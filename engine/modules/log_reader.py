import json
from typing import List
import logging
from .engine import Query, ProgramPath, BranchAction


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

            content = _get_content(line).strip()
            command = content.upper()
            if False:
                pass
            elif command == "PROG":
                path = list()
            elif command == "END_PROG":
                path = None

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
                    path[:-1] + [(path[-1][0], ~path[-1][1])])
            elif command == "OPTIMISTIC":
                current_path = ProgramPath(
                    path[:-1] + [(path[-1][0], BranchAction.OPTIMISTIC)])
            elif command == "SMT":
                pass
            elif command == "BRANCH":
                branch = _get_content(f.readline()).split()
                path.append(
                    (int(branch[0]), BranchAction.TAKEN if branch[1] == 'T' else BranchAction.NOT_TAKEN))

            elif command == "CHECK":
                if not current_path:
                    current_path = ProgramPath(path)
                queries.append(Query(len(queries), dependencies,
                               current_path, constraints))

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
