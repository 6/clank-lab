"""Check that a clausal proof refutes a CNF formula, using unit propagation only.

Usage: python3 checks/rup_check.py FORMULA.cnf PROOF.drat

This is a second checker for the DRAT proof, written separately from
DRAT-trim and much simpler. It reads the proof's added clauses in order and
ignores its deletions. An added clause C is accepted when assigning false
to every literal of C and running unit propagation on the formula together
with the clauses accepted so far yields a conflict. Such a clause is a
logical consequence of the formula, and keeping clauses the proof deleted
only strengthens propagation, so every accepted clause follows from the
formula. A clause that fails this test is skipped, never used. The
formula is refuted when the empty clause is accepted, that is, when unit
propagation alone yields a conflict, either at the proof's empty clause or
after its last clause.

The script prints "s VERIFIED" and exits with status 0 if the formula is
refuted, and prints "s NOT VERIFIED" and exits with status 1 otherwise.
"""
import sys


def read_clauses(path, allow_deletions):
    added = []
    current = []
    deleting = False
    with open(path) as f:
        for line in f:
            words = line.split()
            if not words or words[0] in ('c', 'p'):
                continue
            for w in words:
                if w == 'd' and allow_deletions and not current:
                    deleting = True
                    continue
                lit = int(w)
                if lit != 0:
                    current.append(lit)
                    continue
                if not deleting:
                    added.append(current)
                current, deleting = [], False
    if current:
        raise ValueError(f'{path}: unterminated clause')
    return added


class Propagator:
    """Clauses with two watched literals; assignments undone after each test."""

    def __init__(self, nvars):
        self.value = [0] * (nvars + 1)
        self.watches = {}
        self.clauses = []
        self.units = []
        self.empty = False

    def add(self, clause):
        lits = list(dict.fromkeys(clause))
        if any(-lit in lits for lit in lits):
            return
        if not lits:
            self.empty = True
            return
        if len(lits) == 1:
            self.units.append(lits[0])
            return
        index = len(self.clauses)
        self.clauses.append(lits)
        for lit in lits[:2]:
            self.watches.setdefault(lit, []).append(index)

    def true(self, lit):
        v = self.value[abs(lit)]
        return v == (1 if lit > 0 else -1)

    def false(self, lit):
        v = self.value[abs(lit)]
        return v == (-1 if lit > 0 else 1)

    def conflict_from(self, assumptions):
        """Assign the assumptions and propagate; True if a conflict arises."""
        trail = []
        try:
            for lit in list(assumptions) + self.units:
                if self.false(lit):
                    return True
                if not self.true(lit):
                    self.value[abs(lit)] = 1 if lit > 0 else -1
                    trail.append(lit)
            head = 0
            while head < len(trail):
                falsified = -trail[head]
                head += 1
                watching = self.watches.get(falsified, [])
                keep = []
                conflict = False
                for pos, index in enumerate(watching):
                    if conflict:
                        keep.append(index)
                        continue
                    lits = self.clauses[index]
                    if lits[0] == falsified:
                        lits[0], lits[1] = lits[1], lits[0]
                    other = lits[0]
                    if self.true(other):
                        keep.append(index)
                        continue
                    for j in range(2, len(lits)):
                        if not self.false(lits[j]):
                            lits[1], lits[j] = lits[j], lits[1]
                            self.watches.setdefault(lits[1], []).append(index)
                            break
                    else:
                        keep.append(index)
                        if self.false(other):
                            conflict = True
                        else:
                            self.value[abs(other)] = 1 if other > 0 else -1
                            trail.append(other)
                self.watches[falsified] = keep
                if conflict:
                    return True
            return False
        finally:
            for lit in trail:
                self.value[abs(lit)] = 0


def main(argv):
    formula = read_clauses(argv[1], allow_deletions=False)
    proof = read_clauses(argv[2], allow_deletions=True)
    nvars = max((abs(l) for c in formula + proof for l in c), default=0)
    checker = Propagator(nvars)
    for clause in formula:
        checker.add(clause)
    accepted = skipped = 0
    for clause in proof:
        if checker.conflict_from([-lit for lit in clause]):
            if not clause:
                print(f'c {accepted} proof clauses accepted, {skipped} skipped')
                print('s VERIFIED')
                return 0
            checker.add(clause)
            accepted += 1
        else:
            skipped += 1
    if checker.conflict_from([]):
        print(f'c {accepted} proof clauses accepted, {skipped} skipped')
        print('s VERIFIED')
        return 0
    print(f'c {accepted} proof clauses accepted, {skipped} skipped; '
          'the empty clause was not derived')
    print('s NOT VERIFIED')
    return 1


if __name__ == '__main__':
    sys.exit(main(sys.argv))
