"""Exact action on Eichler flags at arbitrary tame prime powers.

Line labels at q^e enumerate (1,y), then (qx,1). At q||N the bad
Hecke correspondence shifts an oriented edge without backtracking.
At q^e||N it shifts a length-e segment one edge forward.
"""
import itertools
import json
from pathlib import Path


def column(s, q, m):
    return (1, s) if s < m else ((s - m) * q, 1)


def label(v, q, m):
    x, y = v
    if x % q:
        return y * pow(x, -1, m) % m
    if y % q:
        return m + (x * pow(y, -1, m) % m) // q
    raise ValueError("imprimitive projective column")


def act(a, v):
    return a[0]*v[0] + a[1]*v[1], a[2]*v[0] + a[3]*v[1]


def adj(a):
    return a[3], -a[1], -a[2], a[0]


def determinant(a):
    return a[0]*a[3] - a[1]*a[2]


def direction(a, q):
    for v in ((a[0], a[2]), (a[1], a[3])):
        if any(x % q for x in v):
            return label(v, q, q)
    raise ValueError("edge matrix vanishes modulo the level prime")


class Flags:
    def __init__(self, case, ell, directory):
        self.directory = Path(directory)
        self.levels = case["levels"]
        self.powers = []
        for q in self.levels:
            m = q
            while case["N"] % (m*q) == 0:
                m *= q
            self.powers.append(m)
        self.sizes = [m + m//q for q, m in zip(self.levels, self.powers)]
        self.data = self.read("classes.json")
        self.ell = ell
        self.ramified = self.read(f"well{ell}.json")
        self.rows = {}

    def read(self, name):
        return json.loads((self.directory / name).read_text())

    def all(self):
        return itertools.product(range(len(self.data["units"])),
                                 *(range(s) for s in self.sizes))

    def offset(self, state):
        pos = state[0]
        for s, size in zip(state[1:], self.sizes):
            pos = pos*size + s
        return pos

    def action(self, matrices, lines, backwards):
        out = []
        for q, m, s in zip(self.levels, self.powers, lines):
            a = matrices[f"p{q}"]
            if backwards:
                a = adj(a)
            out.append(label(act(a, column(s,q,m)), q, m))
        return tuple(out)

    def load(self, q):
        if q not in self.rows:
            self.rows[q] = self.read(f"q{q}.json")
        return self.rows[q]

    def moves(self, state, q):
        i, *lines = state
        if q == self.ell:
            e = self.ramified[i]
            yield (e["index"], *self.action(e, lines, True))
            return
        if q not in self.levels:
            for e in self.load(q)[i]:
                yield (e["index"], *self.action(e, lines, True))
            return
        k = self.levels.index(q)
        m = self.powers[k]
        v = column(lines[k], q, m)
        chosen = [e for e in self.load(q)[i]
                  if direction(e[f"p{q}"], q) == label(v,q,q)]
        if len(chosen) != 1:
            raise ValueError("missing or duplicated first edge")
        edge, = chosen
        matrix = edge[f"p{q}"]
        pullback = adj(matrix)
        output = []
        for j, (r,h,s) in enumerate(zip(self.levels,self.powers,lines)):
            if j == k:
                output.append(None)
            else:
                output.append(label(act(adj(edge[f"p{r}"]), column(s,r,h)), r,h))
        if m == q:
            reverse = direction(pullback,q)
            successors = [t for t in range(q+1) if t != reverse]
        else:
            x, y = act(pullback,v)
            if x % q or y % q:
                raise ValueError("selected edge does not contain segment")
            h = m//q
            t = label((x//q,y//q), q,h)
            # Each endpoint at depth e-1 has q children at depth e.
            if t < h:
                successors = [t + a*h for a in range(q)]
            else:
                successors = [m + t-h + a*(h//q) for a in range(q)]
        for s in successors:
            output[k] = s
            yield (edge["index"], *output)


class UnresolvedEigenspace(ValueError):
    """The priced Hecke subsystem did not isolate a single eigenfunction."""


class SegmentPriceLimit(ValueError):
    """Eliminating the full flag system exceeds the dense variable limit."""


def solve(case, ell, directory, primes, max_variables=9000):
    """Intersect actual Hecke equations on the full unit quotient."""
    from sage.all import EllipticCurve, GF, matrix

    flags = Flags(case, ell, directory)
    p, eps = case["p"], case["eps"]
    E = EllipticCurve(case["ainvs"])
    indices, reps = {}, []
    for state in flags.all():
        if state in indices:
            continue
        orbit = {state}
        todo = [state]
        while todo:
            v = todo.pop()
            for u in flags.data["units"][v[0]]:
                w = (v[0], *flags.action(u, v[1:], False))
                if w not in orbit:
                    todo.append(w)
                    orbit.add(w)
        indices.update(dict.fromkeys(orbit, len(reps)))
        reps.append(state)
    n = len(reps)
    if n > max_variables:
        raise SegmentPriceLimit(f"full segment kernel has {n} variables, cap {max_variables}")
    # Restrict on good T first, then on bad U. No local newness is assumed.
    ops = list(dict.fromkeys([*primes, ell, *flags.levels]))
    basis = None
    dims = []
    for q in ops:
        a = eps if q == ell else int(E.ap(q))
        entries = {}
        for i, s in enumerate(reps):
            entries[i,i] = -a
            for t in flags.moves(s,q):
                j = indices[t]
                entries[i,j] = entries.get((i,j),0) + 1
        op = matrix(GF(p), n,n, entries, sparse=basis is not None)
        if basis is None:
            basis = op.right_kernel_matrix()
        else:
            basis = (op*basis.transpose()).dense_matrix().right_kernel_matrix()*basis
        dims.append(int(basis.nrows()))
        if not basis.nrows():
            raise ValueError(f"no eigensystem after operator {q}")
    if basis.nrows() != 1:
        raise UnresolvedEigenspace(f"eigenspace failed isolation: {dims}")
    v = basis[0]
    scale = next(x for x in v if x)
    out = [int(v[indices[s]] / scale) for s in flags.all()]
    for q in ops:
        a = eps if q == ell else int(E.ap(q))
        for s in flags.all():
            if (sum(out[flags.offset(t)] for t in flags.moves(s,q)) -
                    a*out[flags.offset(s)]) % p:
                raise ArithmeticError(f"Hecke replay at {q} failed")
    (flags.directory/"eigen.json").write_text(json.dumps(out,separators=(",",":"))+"\n")
    return dict(operators=ops, nullities=dims, variables=n)
