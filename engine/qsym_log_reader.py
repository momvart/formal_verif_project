import json
from typing import FrozenSet, List, Tuple, Iterable, MutableSet, Any
import logging


class ProgramPath:
    def __init__(self, path: Iterable[Tuple[int, bool]] = ()) -> None:
        self.__list = tuple(path)

    def __getitem__(self, index):
        if isinstance(index, slice):
            return ProgramPath(self.__list[index])
        else:
            return self.__list[index]

    def __len__(self):
        return self.__list.__len__()

    def to_json_serializable(self):
        return self.__list


class Query:
    def __init__(self) -> None:
        self.dependencies: MutableSet[int] = set()
        self.path: ProgramPath = None
        self.constraints: List[str] = list()

    def to_json_serializable(self):
        return {
            "dependencies": list(self.dependencies),
            "path": self.path.to_json_serializable(),
            "constraints": self.constraints,
        }


class QueryEncoder(json.JSONEncoder):
    def default(self, o: Any) -> Any:
        if isinstance(o, Query):
            return o.__dict__
        else:
            return super().default(o)


def get_content(line):
    assert line.startswith("[EXPORT] ")
    return line[len("[EXPORT] "):]


def read_log(path):
    queries = list()
    with open(path, "r") as f:
        path = list()
        query = None

        state = list()
        STATE_ADDING = "adding"
        STATE_DEPSET = "depset"

        while True:
            line = f.readline()
            if not line:
                break

            if not line.startswith("[EXPORT]"):
                continue

            logging.debug("Read line: %s", line)

            content = get_content(line).strip().upper()
            command = content
            if False:
                pass
            elif command == "RESET":
                query = Query()

            elif command == "DEPSET":
                state.append(STATE_DEPSET)
            elif command == "END_DEPSET":
                state.pop()

            elif command == "ADD":
                constraint = ""
                state.append(STATE_ADDING)
            elif command == "END_ADD":
                query.constraints.append(constraint)
                state.pop()

            elif command == "BRNEG":
                query.path = ProgramPath(
                    path[:-1] + [(path[-1][0], not path[-1][1])])

            elif command == "SMT":
                pass
            elif command == "BRANCH":
                branch = get_content(f.readline()).split()
                path.append((int(branch[0]), branch[1] == 'T'))

            elif command == "CHECK":
                queries.append(query)

            elif len(state) > 0:
                if False:
                    pass
                elif state[-1] == STATE_ADDING:
                    constraint += content + "\n"
                elif state[-1] == STATE_DEPSET:
                    query.dependencies.add(content)

    return queries


if __name__ == "__main__":
    logging.basicConfig(level=logging.DEBUG)
    queries = read_log("./engine/test.log")
    print(json.dumps([q.to_json_serializable() for q in queries]))
