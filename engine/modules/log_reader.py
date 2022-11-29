import json
from typing import FrozenSet, List, Tuple, Iterable, MutableSet, Any
import logging
from .engine import Query, ProgramPath

def _get_content(line):
    assert line.startswith("[EXPORT] ")
    return line[len("[EXPORT] "):]


def read_qsym_log(path) -> List[Query]:
    queries = list()
    with open(path, "r") as f:
        path = list()
        
        dependencies = None
        current_path = None
        constraints = None

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

            content = _get_content(line).strip().upper()
            command = content
            if False:
                pass
            elif command == "RESET":
                dependencies = set()
                current_path = None
                constraints = list()

            elif command == "DEPSET":
                state.append(STATE_DEPSET)
            elif command == "END_DEPSET":
                state.pop()

            elif command == "ADD":
                constraint = ""
                state.append(STATE_ADDING)
            elif command == "END_ADD":
                constraints.append(constraint)
                state.pop()

            elif command == "BRNEG":
                current_path = ProgramPath(
                    path[:-1] + [(path[-1][0], not path[-1][1])])

            elif command == "SMT":
                pass
            elif command == "BRANCH":
                branch = _get_content(f.readline()).split()
                path.append((int(branch[0]), branch[1] == 'T'))

            elif command == "CHECK":
                queries.append(Query(dependencies, current_path, constraints))

            elif len(state) > 0:
                if False:
                    pass
                elif state[-1] == STATE_ADDING:
                    constraint += content + "\n"
                elif state[-1] == STATE_DEPSET:
                    dependencies.add(content)

    return queries


if __name__ == "__main__":
    logging.basicConfig(level=logging.DEBUG)
    queries = read_qsym_log("./engine/test.log")
    print(json.dumps([q.to_json_serializable() for q in queries]))
