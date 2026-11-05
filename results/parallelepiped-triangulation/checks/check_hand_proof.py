#!/usr/bin/env python3
"""Check every finite statement of the hand proof of Theorem 1 by brute force.

Usage: check_hand_proof.py [paper.tex]

Standard library only; it shares no code with the other programs. It reads
the tables of Steps 1-3 from the paper's appendix (the rows between the
"% table: step N" and "% end table" comments) and checks:
- the 20 lattice points of P = P[1,2,2,5] and their names;
- Step 1: for each edge a b, a + b is the only way to write 2y = a + b with
  two distinct lattice points of P;
- Steps 2 and 3: the tables list every set of distinct lattice points with
  positive integer weights summing to 4 and weighted sum 4q (resp. 4r)
  exactly once (Step 2 leaving out A11 + I1 + I2 + I3 itself);
- every identity sum p_s s = sum q_r r: both sides agree, the weights are
  nonnegative with equal totals, its left points lie in S and its right
  points in R, some left point with p_s > 0 is not in R, and R is a lattice
  point, a Step 1 edge or the Step 2 tetrahedron.
"""
import itertools, os, re, sys
from fractions import Fraction as Fr

V = (1, 2, 2, 5)


def in_P(x):
    t4 = Fr(x[3], V[3])
    t = (x[0] - V[0] * t4, x[1] - V[1] * t4, x[2] - V[2] * t4, t4)
    return all(0 <= c <= 1 for c in t)


PTS = [x for x in itertools.product(range(-1, 4), range(-1, 5), range(-1, 5), range(-1, 7)) if in_P(x)]
NAME = {}
for a in (0, 1):
    for b in (0, 1):
        NAME[f'A{a}{b}'] = (0, a, b, 0)
        NAME[f'B{a}{b}'] = (1, a, b, 0)
        NAME[f'C{a}{b}'] = (1, 2 + a, 2 + b, 5)
        NAME[f'D{a}{b}'] = (2, 2 + a, 2 + b, 5)
NAME.update(I1=(1, 1, 1, 1), I2=(1, 1, 1, 2), I3=(1, 2, 2, 3), I4=(1, 2, 2, 4))
assert len(PTS) == 20 and sorted(PTS) == sorted(NAME.values()), 'lattice points'
print('PASS: P[1,2,2,5] has exactly the 20 named lattice points')


def vsum(terms):
    terms = list(terms)
    return tuple(sum(m * NAME[n][i] for n, m in terms) for i in range(4))


def plain(cell):
    """'$2A_{00}+B_{11}+2I_3$' -> '2A00+B11+2I3'; '$A_{11}\\,I_2$' -> 'A11 I2'."""
    cell = cell.replace('\\,', ' ').replace('$', '').replace('{', '').replace('}', '')
    return re.sub(r'([ABCDI])_', r'\1', cell).strip()


def parse_combo(s):
    """'2A00 + B11 + I3' -> {'A00': 2, 'B11': 1, 'I3': 1}"""
    out = {}
    for term in s.split('+'):
        term = term.strip()
        m = re.fullmatch(r'(\d*)([ABCD][01][01]|I[1-4])', term)
        assert m, f'bad term {term!r}'
        n = m.group(2)
        assert n not in out, f'repeated point in {s!r}'
        out[n] = int(m.group(1) or 1)
    return out


def rows(text, heading):
    sec = text.split(f'% table: {heading}\n', 1)[1].split('% end table', 1)[0]
    rs = []
    for line in sec.splitlines():
        line = line.strip()
        if line.startswith('$') and line.endswith('\\\\'):
            rs.append([plain(c) for c in line[:-2].split('&')])
    return rs


path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'paper', 'paper.tex')
text = open(path, encoding='utf-8').read()

# Step 1
edges = set()
for r in rows(text, 'step 1'):
    a, b = r[0].split()
    y2 = tuple(int(t) for t in r[1].strip('()').split(','))
    assert vsum([(a, 1), (b, 1)]) == y2, r
    assert any(t % 2 for t in y2), 'midpoint is a lattice point'
    pairs = [(u, v) for u, v in itertools.combinations(PTS, 2) if tuple(p + q for p, q in zip(u, v)) == y2]
    assert len(pairs) == 1, (r, pairs)
    edges.add(frozenset((a, b)))
assert len(edges) == 12
print('PASS: Step 1: 12 edges, each the only pair of lattice points of P with its midpoint')

F = frozenset(('A11', 'I1', 'I2', 'I3'))


def solutions(target):
    sols = set()
    names = sorted(NAME)
    for k in range(1, 5):
        for S in itertools.combinations(names, k):
            for w in itertools.product(range(1, 5), repeat=k):
                if sum(w) == 4 and vsum(zip(S, w)) == target:
                    sols.add(frozenset(zip(S, w)))
    return sols


def check_step(heading, target, leave_out, known):
    rs = rows(text, heading)
    listed = []
    for S_s, R_s, ident in rs:
        S = parse_combo(S_s)
        assert sum(S.values()) == 4 and vsum(S.items()) == target, S_s
        R = frozenset(R_s.split())
        assert R in known or (len(R) == 1 and next(iter(R)) in NAME), f'R not known: {R_s}'
        lhs, rhs = (parse_combo(x) for x in ident.split('='))
        assert vsum(lhs.items()) == vsum(rhs.items()), f'identity fails: {ident}'
        assert sum(lhs.values()) == sum(rhs.values()) > 0, ident
        assert set(lhs) <= set(S) and set(rhs) <= R, f'identity points: {ident}'
        assert any(n not in R for n in lhs), f'no weight outside R: {ident}'
        listed.append(frozenset(S.items()))
    sols = solutions(target)
    want = sols - {leave_out} if leave_out else sols
    assert len(listed) == len(set(listed)), 'duplicate row'
    assert set(listed) == want, (sorted(map(sorted, want - set(listed))), sorted(map(sorted, set(listed) - want)))
    return len(sols), len(listed)


q4 = vsum([(n, 1) for n in F])
assert q4 == (3, 5, 5, 6)
n, m = check_step('step 2', q4, frozenset((n, 1) for n in F), edges)
print(f'PASS: Step 2: {n} weighted sets with sum (3,5,5,6); all {m} other than A11+I1+I2+I3 ruled out by the common-face lemma')
r4 = vsum([('B01', 3), ('C10', 1)])
assert r4 == (4, 3, 5, 5)
n, m = check_step('step 3', r4, None, edges | {F})
print(f'PASS: Step 3: {n} weighted sets with sum (4,3,5,5); all {m} ruled out by the common-face lemma')
