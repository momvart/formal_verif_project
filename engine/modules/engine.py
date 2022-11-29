from collections import OrderedDict
from typing import List, Tuple, Dict, FrozenSet, Iterable
import weakref
import z3
import logging
from abc import ABC, abstractmethod


class ProgramPath:
    def __init__(self, path: Iterable[Tuple[int, bool]] = ()) -> None:
        self.__list: Tuple[Tuple[int, bool]] = tuple(path)

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


class Query:
    def __init__(self, dependencies: Iterable[int], path, constraints) -> None:
        self.dependencies: FrozenSet[int] = frozenset(dependencies)
        self.path: ProgramPath = path
        self.constraints: Tuple[str] = tuple(constraints)

    def to_json_serializable(self):
        return {
            "dependencies": list(self.dependencies),
            "path": self.path.to_json_serializable(),
            "constraints": self.constraints,
        }


class SolverStatistics:
    def __init__(self) -> None:
        self.solve_count = 0
        self.push_count = 0
        self.pop_count = 0

    def __str__(self) -> str:
        return str({"solve_count": self.solve_count, "push_count": self.push_count, "pop_count": self.pop_count, })

    def __repr__(self) -> str:
        return str(self)


class MySolver:
    def __init__(self, id, z3_ctx, const_declarations) -> None:
        self.id = id
        # Stack of subpaths expressed by site ids and whether they are taken or not.
        self._path_stack: List[List[Tuple[int, bool]]] = []
        self._path_length = 0
        self._solver = z3.Solver(ctx=z3_ctx)
        self._const_declarations = const_declarations
        self.statistics = SolverStatistics()

    def solve(self, path, constraints: List[str], assert_prefix=False):
        self.statistics.solve_count += 1

        logging.debug("Path to solve: %s", path)
        logging.debug("Constraints to solve: %s", constraints)
        logging.debug("Solver state: %s", self._solver)

        if assert_prefix:
            logging.debug("Solver path length: %d", self._path_length)
            logging.debug("Shared length: %d", self.get_shared_prefix_length(path)[0])
            assert self.get_shared_prefix_length(path)[0] == self._path_length

        if len(path) == self._path_length:
            return self._solver.check()

        self._solver.push()
        self.statistics.push_count += 1

        self._add(constraints[self.constraint_count:])
        result = self._solver.check()

        self._solver.pop()
        self.statistics.pop_count += 1

        return result

    def sync_with(self, subpath: List[Tuple[int, bool]], constraints):
        _, shared_stack_count = self.get_shared_prefix_length(subpath)
        self._pop(len(self._path_stack) - shared_stack_count)
        self.upgrade(subpath[self._path_length:],
                     constraints[self.constraint_count:], True)

    def upgrade(self, new_subpath: List[Tuple[int, bool]], new_constraints: List[str], downgradable=False):
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

    def downgrade(self, subpath: List[Tuple[int, bool]], constraints: List[str], force=False):
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

    def get_shared_prefix_length(self, path: List[Tuple[int, bool]]) -> Tuple[int, int]:
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
        return len(self._solver.assertions())

    def copy_from(self, other):
        self._path_stack = [e.copy() for e in other._path_stack]
        self._path_length = other._path_length
        self._solver = other._solver.__copy__()

    def _add(self, constraints: List[str]):
        logging.debug("Adding constraints: %s", str(constraints))
        self._solver.add([z3.parse_smt2_string(
            f"(assert {c})", ctx=self._solver.ctx, decls=self._const_declarations) for c in constraints])
        logging.debug("Solver state after adding the constraints: %s", self._solver)

    def _pop(self, count):
        self._solver.pop(count)
        self.statistics.pop_count += 1

        for i in range(len(self._path_stack), len(self._path_stack) - count, -1):
            self._path_length -= len(self._path_stack[i])
        del self._path_stack[len(self._path_length) - count:]

    def _path_length_to(self, stack_index):
        return sum(len(e) for e in self._path_length[:stack_index])


class SolverPrefixTree:
    def __init__(self) -> None:
        self.solver = None
        self.children: Dict[Tuple[int, bool], SolverPrefixTree] = dict()

    def insert(self, path: ProgramPath, solver: MySolver):
        if len(path) == 0:
            self.__set_solver(solver)
            return

        if path[0] not in self.children:
            self.children[path[0]] = SolverPrefixTree()

        self.children[path[0]].insert(path[1:], solver)

    def find(self, path: ProgramPath) -> MySolver | None:
        """
        Returns the solver having the longest common prefix with the given path.
        """

        found_solver = self.solver and self.solver()
        if len(path) == 0:
            return found_solver

        if (child := self.children.get(path[0])):
            found_solver = child.find(path[1:]) or found_solver

        return found_solver

    def __set_solver(self, solver: MySolver):
        if self.solver and self.solver() is not None:
            logging.warn("Replacing an existing alive solver")
        self.solver = weakref.ref(solver)


class LRUCache:
    def __init__(self, max_size) -> None:
        self.max_size = max_size
        self.items = OrderedDict()

    def hit(self, id):
        self.items.move_to_end(id, True)

    def add(self, id, value):
        if len(self.items) > self.max_size:
            self.items.popitem()

        self.items[id] = value


class SolverSelectionStrategy(ABC):
    @abstractmethod
    def get_solver(self, found_solver: MySolver | None, query: Query) -> MySolver:
        pass

    def create_empty_solver() -> MySolver:
        pass


class BasicSolverSelectionStrategy(SolverSelectionStrategy):
    def get_solver(self, found_solver: MySolver | None, query: Query) -> MySolver:
        if found_solver is None:
            return self.create_empty_solver()
        else:
            return found_solver


class SolverPool:
    def __init__(self) -> None:
        # This max size is random and no intuition is behind it.
        self._solvers = LRUCache(200)
        self._solver_trees: Dict[FrozenSet[int], SolverPrefixTree] = dict()
        self._next_id = 1
        self.selection_strategy = BasicSolverSelectionStrategy()
        self._z3_ctx = z3.Context()
        self._const_declarations: Dict[str, z3.Symbol] = dict()
        self._should_assert_solve = False

    def solve(self, query: Query):
        key = query.dependencies
        if key not in self._solver_trees:
            self._ensure_const_for(key)
            tree = SolverPrefixTree()
            self._solver_trees[key] = tree

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

        return solver

    def _create_solver(self):
        solver = MySolver(self._next_id, self._z3_ctx,
                          self._const_declarations)
        self._solvers.add(solver.id, solver)
        self._next_id += 1
        return solver

    def _set_solver_selection_strategy(self, value: SolverSelectionStrategy):
        value.create_empty_solver = lambda: self._create_solver()
        self._solver_selection_strategy = value

    selection_strategy = property(fset=_set_solver_selection_strategy)
