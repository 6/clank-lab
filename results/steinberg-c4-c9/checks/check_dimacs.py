"""Compare two DIMACS formulas by their parsed variables and ordered clauses."""
import sys


def read(path):
    header = None
    clauses, pending = [], []
    with open(path) as stream:
        for line in stream:
            if not line.strip() or line.lstrip().startswith("c"):
                continue
            if line.startswith("p "):
                fields = line.split()
                if header is not None or fields[:2] != ["p", "cnf"] or len(fields) != 4:
                    raise ValueError("bad DIMACS header")
                header = tuple(map(int, fields[2:]))
                continue
            if header is None:
                raise ValueError("clauses before header")
            for literal in map(int, line.split()):
                if literal == 0:
                    clauses.append(tuple(pending))
                    pending = []
                elif abs(literal) <= header[0]:
                    pending.append(literal)
                else:
                    raise ValueError("literal out of range")
    if header is None or pending or len(clauses) != header[1]:
        raise ValueError("incomplete DIMACS formula")
    return header, clauses


if __name__ == "__main__":
    if read(sys.argv[1]) != read(sys.argv[2]):
        raise SystemExit("REJECT: generated and supplied CNF differ")
    print("OK: generated and supplied CNF have identical parsed contents")
