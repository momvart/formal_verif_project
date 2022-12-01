from collections import OrderedDict
from typing import List, Tuple, Dict, FrozenSet, Iterable, TypeAlias
import weakref
import z3
import logging
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from time import perf_counter
from enum import Enum


class BranchAction(Enum):
    TAKEN = 0
    NOT_TAKEN = 1
    OPTIMISTIC = 2

    def __invert__(self):
        if self == BranchAction.TAKEN:
            return BranchAction.NOT_TAKEN
        elif self == BranchAction.NOT_TAKEN:
            return BranchAction.TAKEN
        else:
            raise AssertionError(
                "Invert operator only works on taken and not taken.")


PathStep: TypeAlias = Tuple[int, BranchAction]


class ProgramPath:
    def __init__(self, path: Iterable[PathStep] = ()) -> None:
        self.__list: Tuple[PathStep] = tuple(path)

    def __getitem__(self, index):
        if isinstance(index, slice):
            return ProgramPath(self.__list[index])
        else:
            return self.__list[index]

    def __len__(self):
        return self.__list.__len__()

    def to_json_serializable(self):
        return self.__list

    def __repr__(self) -> str:
        return self.__list.__repr__()

    def __str__(self) -> str:
        return self.__list.__str__()

    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, ProgramPath) and self.__list == __o.__list


@dataclass
class Query:
    id: int
    dependencies: FrozenSet[int]
    path: ProgramPath
    constraints: Tuple[str]

    def __init__(self, id: int, dependencies: Iterable[int], path, constraints) -> None:
        self.id = id
        self.dependencies: FrozenSet[int] = frozenset(dependencies)
        self.path: ProgramPath = path
        self.constraints: Tuple[str] = tuple(constraints)

    def to_json_serializable(self):
        return {
            "dependencies": list(self.dependencies),
            "path": self.path.to_json_serializable(),
            "constraints": self.constraints,
        }


@dataclass
class SolverStatistics:
    solve_count: int = 0
    push_count: int = 0
    pop_count: int = 0

    times: Dict[str, float] = field(default_factory=dict)


class MyTimer:
    def __init__(self, name: str = "", store_to=None):
        self.name = name
        self.store_to: Dict[str, float] = store_to

    def __enter__(self):
        self.start_time = perf_counter()

    def __exit__(self, exc_type, exc_value, traceback):
        self.elapsed_time = perf_counter() - self.start_time
        if self.store_to is not None:
            self.store_to[self.name] = self.store_to.get(
                self.name, 0) + self.elapsed_time


class NonFunctionalTimer(object):
    def __new__(cls):
        if not hasattr(cls, 'instance'):
            cls.instance = super(NonFunctionalTimer, cls).__new__(cls)
        return cls.instance

    def __enter__(self):
        pass

    def __exit__(self, exc_type, exc_value, traceback):
        pass


class MySolver:
    def __init__(self, id, z3_ctx, const_declarations) -> None:
        self.id = id
        self.statistics = SolverStatistics()
        self._timer = MyTimer(store_to=self.statistics.times)
        # Stack of subpaths expressed by site ids and whether they are taken or not.
        self._path_stack: List[List[PathStep]] = []
        self._path_length = 0
        with self._timeit("creating"):
            self._solver = z3.Solver(ctx=z3_ctx)
        self._const_declarations = const_declarations

    def solve(self, path, constraints: List[str], assert_prefix=False):
        self.statistics.solve_count += 1

        logging.debug("Path to solve: %s", path)
        logging.debug("Constraints to solve: %s", constraints)
        logging.debug("Solver state: %s", self._solver)

        if assert_prefix:
            logging.debug("Solver path length: %d", self._path_length)
            logging.debug("Solver path: %s", self.stack_path)
            logging.debug("Shared length: %d",
                          self.get_shared_prefix_length(path)[0])
            assert self.get_shared_prefix_length(path)[0] == self._path_length

        if len(path) == self._path_length:
            return self._check()

        self._solver.push()
        self.statistics.push_count += 1

        logging.debug("Adding the last %d constraints",
                      len(constraints) - self.constraint_count)
        self._add(constraints[self.constraint_count:])
        result = self._check()

        self._solver.pop()
        self.statistics.pop_count += 1

        return result

    def sync_with(self, subpath: List[PathStep], constraints):
        _, shared_stack_count = self.get_shared_prefix_length(subpath)
        self._pop(len(self._path_stack) - shared_stack_count)
        self.upgrade(subpath[self._path_length:],
                     constraints[self.constraint_count:], True)

    def upgrade(self, new_subpath: List[PathStep], new_constraints: List[str], downgradable=False):
        if len(new_subpath) == 0:
            return

        logging.debug("Solver path before upgrade: %s", self._path_stack)
        logging.debug("New subpath for upgrade: %s", new_subpath)
        logging.debug("New constraints to be added: %s", new_constraints)

        if downgradable:
            self._path_stack.append(list())
            self._solver.push()
            self.statistics.push_count += 1

        if len(self._path_stack) == 0:
            self._path_stack.append(list())

        self._path_stack[-1].extend(new_subpath)
        self._path_length += len(new_subpath)
        self._add(new_constraints)

    def downgrade(self, subpath: List[PathStep], constraints: List[str], force=False):
        shared_subpath_length, shared_stack_count = self.get_shared_prefix_length(
            subpath)
        completely_shared_length = self._path_length_to(shared_stack_count)

        if shared_subpath_length < len(subpath):
            return False
        elif completely_shared_length < shared_subpath_length and force:
            self._pop(1)
            self.upgrade(subpath[shared_subpath_length:],
                         constraints[self.constraint_count:], True)
            return True

        self._pop(len(self._path_length) - shared_stack_count)
        return True

    def get_shared_prefix_length(self, path: List[PathStep]) -> Tuple[int, int]:
        subpath_index = 0
        stack_index = 0
        while subpath_index < len(path) and stack_index < len(self._path_stack):
            entry = self._path_stack[stack_index]
            for i in range(min(len(entry), len(path) - subpath_index)):
                if entry[i] != path[subpath_index]:
                    return subpath_index, stack_index

                subpath_index += 1

            stack_index += 1

        return subpath_index, stack_index

    @property
    def stack_path(self) -> ProgramPath:
        return ProgramPath(step for entry in self._path_stack for step in entry)

    @property
    def stack_path_len(self):
        return self._path_length

    @property
    def constraint_count(self):
        # This retrieves all queries, we may use our counter to prevent the overhead.
        with self._timeit("assertion_counting"):
            return len(self._solver.assertions())

    def copy_from(self, other):
        with self._timeit("copying"):
            self._path_stack = [e.copy() for e in other._path_stack]
            self._path_length = other._path_length
            self._solver = other._solver.__copy__()

    def _add(self, constraints: List[str]):
        logging.debug("Adding constraints: %s", str(constraints))

        with self._timeit("parsing"):
            assertions = [z3.parse_smt2_string(
                f"(assert {c})", ctx=self._solver.ctx, decls=self._const_declarations) for c in constraints]
        with self._timeit("adding"):
            self._solver.add(assertions)

        logging.debug(
            "Solver state after adding the constraints: %s", self._solver)

    def _pop(self, count):
        with self._timeit("popping"):
            self._solver.pop(count)
        self.statistics.pop_count += count

        for i in range(len(self._path_stack), len(self._path_stack) - count, -1):
            self._path_length -= len(self._path_stack[i])
        del self._path_stack[len(self._path_length) - count:]

    def _check(self):
        with self._timeit("checking"):
            return self._solver.check()

    def _path_length_to(self, stack_index):
        return sum(len(e) for e in self._path_length[:stack_index])

    def _timeit(self, name):
        self._timer.name = name
        return self._timer


@dataclass
class TreeStatistics:
    times: Dict[str, float] = field(default_factory=dict)


class SolverPrefixTree:
    def __init__(self, statistics: TreeStatistics = None) -> None:
        self.solver = None
        self.children: Dict[PathStep, SolverPrefixTree] = dict()
        self.statistics = statistics

    def insert(self, path: ProgramPath, solver: MySolver):
        with self._timeit("insertion"):
            if len(path) == 0:
                self._set_solver(solver)
                return

            if path[0] not in self.children:
                self.children[path[0]] = SolverPrefixTree()

            self.children[path[0]].insert(path[1:], solver)

    def find(self, path: ProgramPath) -> MySolver | None:
        """
        Returns the solver having the longest common prefix with the given path.
        """
        with self._timeit("finding"):
            found_solver = self.solver and self.solver()
            if len(path) == 0:
                return found_solver

            if (child := self.children.get(path[0])):
                found_solver = child.find(path[1:]) or found_solver

            return found_solver

    def _set_solver(self, solver: MySolver):
        if self.solver and self.solver() is not None:
            logging.warn("Replacing an existing alive solver")
        self.solver = weakref.ref(solver)

    def _timeit(self, name):
        if self.statistics:
            return MyTimer(name, self.statistics.times)
        else:
            return NonFunctionalTimer()


@dataclass
class CacheStatistics:
    hit_count: int = 0
    add_count: int = 0
    pop_count: int = 0


class LRUCache:
    def __init__(self, max_size) -> None:
        self.max_size = max_size
        self.items = OrderedDict()
        self.statistics = CacheStatistics()

    def hit(self, id):
        self.items.move_to_end(id, True)
        self.statistics.hit_count += 1

    def add(self, id, value):
        if len(self.items) > self.max_size:
            self.items.popitem()
            self.statistics.pop_count += 1

        self.items[id] = value
        self.statistics.add_count += 1


class SolverSelectionStrategy(ABC):
    def __init__(self, log_level=logging.DEBUG) -> None:
        self.log_level = log_level

    @abstractmethod
    def get_solver(self, found_solver: MySolver | None, query: Query) -> MySolver:
        pass

    def create_empty_solver() -> MySolver:
        pass

    def _log(self, msg, *args):
        logging.log(self.log_level, msg, *args)


class BasicSolverSelectionStrategy(SolverSelectionStrategy):
    def get_solver(self, found_solver: MySolver | None, query: Query) -> MySolver:
        if found_solver is None:
            return self.create_empty_solver()
        else:
            return found_solver


class PoolStatistics:
    def __init__(self, cache: CacheStatistics):
        self.cache = cache
        self.solvers: Dict[int, SolverStatistics] = dict()
        self.trees: Dict[FrozenSet[int], TreeStatistics] = dict()


class SolverPool:
    def __init__(self, max_solvers=200) -> None:
        # This max size is random and no intuition is behind it.
        self._solvers = LRUCache(max_solvers)
        self._solver_trees: Dict[FrozenSet[int], SolverPrefixTree] = dict()
        self._next_id = 1
        self.selection_strategy = BasicSolverSelectionStrategy()
        self._z3_ctx = z3.Context()
        self._const_declarations: Dict[str, z3.Symbol] = dict()
        self._should_assert_solve = False
        self.statistics = PoolStatistics(self._solvers.statistics)

    def solve(self, query: Query):
        if query is None:
            return z3.unknown
        key = query.dependencies
        if key not in self._solver_trees:
            self._ensure_const_for(key)
            stats = TreeStatistics()
            tree = SolverPrefixTree(statistics=stats)
            self._solver_trees[key] = tree
            self.statistics.trees[key] = stats

        tree = self._solver_trees[key]

        solver = self._get_solver(tree, query)
        return solver.solve(query.path, query.constraints, assert_prefix=self._should_assert_solve)

    def enable_solve_prefix_assertions(self, value=True):
        self._should_assert_solve = value

    def _ensure_const_for(self, dependencies: Iterable[int]):
        for index in dependencies:
            if index not in self._const_declarations:
                self._const_declarations[f"k!{index}"] = z3.BitVec(
                    index, 8, ctx=self._z3_ctx)

    def _get_solver(self, tree: SolverPrefixTree, query: Query):
        found_solver = tree.find(query.path)

        solver = self._solver_selection_strategy.get_solver(
            found_solver, query)
        if solver is not found_solver:
            tree.insert(solver.stack_path, solver)

        self._solvers.hit(solver.id)
        return solver

    def _create_solver(self):
        solver = MySolver(self._next_id, self._z3_ctx,
                          self._const_declarations)
        self._solvers.add(solver.id, solver)
        self.statistics.solvers[solver.id] = solver.statistics
        self._next_id += 1
        return solver

    def _set_solver_selection_strategy(self, value: SolverSelectionStrategy):
        value.create_empty_solver = lambda: self._create_solver()
        self._solver_selection_strategy = value

    selection_strategy = property(fset=_set_solver_selection_strategy)