from collections import OrderedDict
from typing import List, Tuple, Dict, FrozenSet
import weakref
import z3


class ProgramPath:
    def __init__(self, path: Tuple[Tuple[int, bool]] = ()) -> None:
        self.__list: Tuple[Tuple[int, bool]] = path

    def __getitem__(self, index):
        if isinstance(index, slice):
            return ProgramPath(self.__list[index])
        else:
            return self.__list[index]

    def __len__(self):
        return self.__list.__len__()

class Query:
    dependencies: FrozenSet[int]
    path: ProgramPath
    constraints: Tuple[Tuple[int, bool]]


class MySolver:
    def __init__(self, id) -> None:
        self.id = id
        # Stack of subpaths expressed by site ids and whether they are taken or not.
        self.__path_stack: List[List[Tuple[int, bool]]] = []
        self.__path_length = 0
        self.__solver = z3.Solver()

    def solve(self, path, constraints, assert_prefix=False):
        if assert_prefix:
            assert self.get_shared_prefix_length(path)[0] == self.__path_length

        self.__solver.push()
        self.__solver.add(constraints[self.__constraints_count:])
        result = self.__solver.check()
        self.__solver.pop()
        return result

    def sync_with(self, subpath: List[Tuple[int, bool]], constraints):
        _, shared_stack_count = self.get_shared_prefix_length(subpath)
        self.__pop(len(self.__path_stack) - shared_stack_count)
        self.upgrade(subpath[self.__path_length:],
                     constraints[self.__path_length:], True)

    def upgrade(self, new_subpath: List[Tuple[int, bool]], new_constraints, downgradable=False):
        if len(new_subpath) == 0:
            return

        if downgradable:
            self.__path_stack.append(list())
            self.__solver.push()

        self.__path_stack[-1].extend(new_subpath)
        self.__path_length += len(new_subpath)
        self.__solver.add(new_constraints)

    def downgrade(self, subpath: List[Tuple[int, bool]], constraints, force=False):
        shared_subpath_length, shared_stack_count = self.get_shared_prefix_length(
            subpath)
        completely_shared_length = self.__path_length_to(shared_stack_count)

        if shared_subpath_length < len(subpath):
            return False
        elif completely_shared_length < shared_subpath_length and force:
            self.__pop(1)
            self.upgrade(subpath[shared_subpath_length:], constraints[self.__constraints_count:], True)
            return True

        self.__pop(len(self.__path_length) - shared_stack_count)
        return True

    def get_shared_prefix_length(self, path: List[Tuple[int, bool]]) -> Tuple[int, int]:
        subpath_index = 0
        stack_index = 0
        while subpath_index < len(path) and stack_index < len(self.__path_stack):
            entry = self.__path_stack[stack_index]
            for i in range(min(len(entry), len(path) - subpath_index)):
                if entry[i] != path[subpath_index]:
                    return subpath_index, stack_index

                subpath_index += 1

            stack_index += 1

        return subpath_index, stack_index

    def clone(self):
        new_solver = MySolver()
        new_solver.__path_stack = [e.copy() for e in self.__path_stack]
        new_solver.__path_length = self.__path_length
        new_solver.__solver = self.__solver.__copy__()
        return new_solver

    def __pop(self, count):
        self.__solver.pop(count)
        for i in range(len(self.__path_stack), len(self.__path_stack) - count, -1):
            self.__path_length -= len(self.__path_stack[i])
        del self.__path_stack[len(self.__path_length) - count:]

    def __path_length_to(self, stack_index):
        return sum(len(e) for e in self.__path_length[:stack_index])

    @property
    def __constraints_count(self):
        # This retrieves all queries, we may use our counter to prevent the overhead.
        return len(self.__solver.assertions())


class SolverPrefixTree:
    def __init__(self) -> None:
        self.solver = None
        self.children: Dict[Tuple[int, bool], SolverPrefixTree] = dict()

    def insert(self, path: ProgramPath, solver: MySolver):
        if len(path) == 0:
            self.__set_solver(solver)

        if path[0] not in self.children:
            self.children[path[0]] = SolverPrefixTree()

        self.children[path[0]].insert(path[1:], solver)

    def find(self, path: ProgramPath) -> MySolver | None:
        """
        Returns the solver having the longest common prefix with the given path.
        """

        found_solver = self.solver()
        if len(path) == 0:
            return found_solver

        if (child := self.children.get(path[0])):
            found_solver = child.find_solver(path[1:]) or found_solver

        return found_solver

    def __set_solver(self, solver: MySolver):
        if self.solver() is not None:
            print("Warining: Replacing an existing alive solver.")
        self.solver = weakref.ref(solver)


class LRUCache:
    def __init__(self, max_size) -> None:
        self.max_size = max_size
        self.items = OrderedDict()

    def hit(self, id):
        self.items.move_to_end(id, True)

    def add(self, id, value):
        if len(self.items > self.max_size):
            self.items.popitem()

        self.items[id] = value


class SolverPool:
    def __init__(self) -> None:
        # This max size is random and no intuition is behind it.
        self.solvers = LRUCache(200)
        self.solver_trees: Dict[FrozenSet[int], SolverPrefixTree] = dict()
        self.__next_id = 1

    def solve(self, query: Query):
        key = query.dependencies
        if key not in self.solver_trees:
            tree = SolverPrefixTree()
            # We add a default empty solver for every tree,
            # so a basic solver will always be available.
            tree.insert(ProgramPath(), self.__create_solver(Query()))
            self.solver_trees[key] = tree

        tree = self.solver_trees[key]

        solver = self.get_solver(tree, query)
        return solver.solve(query.path, query.constraints)

    def get_solver(self, tree: SolverPrefixTree, query: Query):
        solver = tree.find(query.path)
        if solver is None:
            solver = self.__create_solver(query)
            tree.insert(query.path, solver)
            return solver

        # Check any criteria here.
        return solver

    def __create_solver(self, query: Query):
        solver = MySolver(self.__next_id)
        self.solvers.add(solver.id, solver)
        self.__next_id += 1

        solver.upgrade(query.path, query.constraints)
        return solver

