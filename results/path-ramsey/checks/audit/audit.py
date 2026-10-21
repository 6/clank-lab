#!/usr/bin/env python3
"""Independent semantic audit of the R_3(P_10) encoding.

Written from the problem and the statement of the encoding below, without
reading or importing encode.py, p3path or check_paths.py.
It may run the pinned command `encode.py n m --fix k` as a subprocess, to
obtain the formula for a small exhaustive instance; it never imports it.

THE PROBLEM.  A colouring X gives each edge of K_n one of the colours
0, 1, 2.  X is *good* if no colour class contains a path on m vertices
(a P_m).  R_3(P_m) <= n says that K_n has no good colouring.

STATED VARIABLE MEANING.  Edges (i, j), i < j, are numbered row-wise
(0,1), (0,2), ..., (n-2, n-1); variable 3e + c + 1 means "edge e has colour
c".  Every larger variable is an auxiliary of the symmetry breaking, which
the auditor gives its own meaning (the witness extension below).

STATED REDUCTIONS (../README.md, "The encoding").
  * fixed path (k > 0): edges (t, t+1), t = 0..k-2, have colour 0.  Sound
    when R_3(P_k) <= n, which a lower rung of the ladder establishes.
  * lex-leader: X <=lex g.X for each listed generator g = (pi, sigma),
    where (g.X)(pi(e)) = sigma(X(e)), positions are compared in row-wise
    edge order and colours as 0 < 1 < 2.  With k > 0 the generators are the
    transpositions of W = {k..n-1} in lexicographic order, the reversal
    t -> k-1-t of 0..k-1, and the colour swap 1 <-> 2; with k = 0, every
    vertex transposition, then the colour swaps 0 <-> 1 and 1 <-> 2.
  * path clauses are not in the base formula: the solver adds them lazily
    and logs each one.

WITNESS EXTENSION.  For generator g let (f_1, s_1), (f_2, s_2), ... be its
compared positions in edge order: f is a position, s = pi^-1(f) its source,
so (g.X)(f) = sigma(X(s)); a position with s = f and sigma = identity is
skipped, being equal for every X.  Auxiliary variables are numbered from
3|E| + 1 upward, generator by generator, one per compared position; the
auditor assigns  eq(g, j) := "X(f_i) = sigma(X(s_i)) for all i <= j".

CHECKS (subcommands):
  cnf CNF n m k [--gens JSON]   every clause of the base formula holds under
      the witness extension of every *admissible* colouring (fixed path and
      all generator inequalities); the formula's clause multiset equals the
      one the stated meaning generates (Encoding.generated: exactly-one, the
      fixed-path units and the four prefix/lex families), nothing
      missing and nothing extra, and each generated group, as a truth table
      over its own variables, means exactly its stated definition; plus the
      reduction lemma that every generator maps the fixed-path set to itself.
      With the inventory, the formula's models are exactly the witness
      extensions of the admissible colourings (../README.md, L5').
  paths n m LOG...              every logged clause is a path clause (LOG
      may be gzipped).
  ladder                        each rung's fixed path rests on a lower rung
      that ../check.py solves whole (its LADDER).
  small n m k [--paths FILE] [--dump-paths FILE] [--gens JSON]
      exhaustive end-to-end check on a small instance (see small()).
  all                           everything the certificate uses;
      deterministic output.

Clause validity (cnf) is decided locally: for a clause, enumerate the colours
of every edge it mentions or that an auxiliary it mentions compares, and a
free truth value for each auxiliary's prefix that the clause leaves
unmentioned.  The only constraints imposed are consequences of
admissibility: fixed-path edges are 0; each generator's first compared
position satisfies X(f_1) <= sigma(X(s_1)); for each mentioned eq(g, j),
prefix -> X(f_j) <= sigma(X(s_j)) and eq(g, j) -> X(f_{j+1}) <=
sigma(X(s_{j+1})) (when those edges are local), and eq(g, j) = prefix and
equality at j; eq(g, j) implies eq(g, i) for i < j.  Every admissible colouring projects to
a state enumerated here, so a clause true in every enumerated state is true
under the witness extension of every admissible colouring.  (The converse
can fail: the check may reject a valid clause, never accept an invalid one.)
"""
import argparse
import collections
import gzip
import hashlib
import itertools
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
CHECKS = os.path.dirname(HERE)
ROOT = os.path.dirname(CHECKS)
DATA = os.path.join(ROOT, 'data')


class Fail(Exception):
    pass


# ---------------------------------------------------------------- the problem

class Kn:
    def __init__(self, n):
        self.n = n
        self.E = [(i, j) for i in range(n) for j in range(i + 1, n)]
        self.idx = {e: t for t, e in enumerate(self.E)}
        self.ne = len(self.E)

    def eid(self, a, b):
        return self.idx[(a, b) if a < b else (b, a)]


def longest_mono_path(K, X):
    """Number of vertices of a longest monochromatic path (DFS)."""
    best = 1 if K.n else 0
    for c in range(3):
        adj = [[] for _ in range(K.n)]
        for t, (a, b) in enumerate(K.E):
            if X[t] == c:
                adj[a].append(b)
                adj[b].append(a)

        def dfs(v, seen):
            r = len(seen)
            for w in adj[v]:
                if w not in seen:
                    seen.add(w)
                    r = max(r, dfs(w, seen))
                    seen.discard(w)
            return r
        for v in range(K.n):
            if adj[v]:
                best = max(best, dfs(v, {v}))
    return best


def stated_generators(n, k):
    ident = list(range(n))
    gens = []

    def transp(i, j):
        p = list(ident)
        p[i], p[j] = j, i
        return p
    if k:
        for i, j in itertools.combinations(range(k, n), 2):
            gens.append((transp(i, j), [0, 1, 2]))
        gens.append(([k - 1 - v if v < k else v for v in range(n)], [0, 1, 2]))
        gens.append((ident, [0, 2, 1]))
    else:
        for i, j in itertools.combinations(range(n), 2):
            gens.append((transp(i, j), [0, 1, 2]))
        gens.append((ident, [1, 0, 2]))
        gens.append((ident, [0, 2, 1]))
    return gens


def is_perm(p, size):
    return sorted(p) == list(range(size))


def compared_positions(K, g):
    pi, sigma = g
    inv = [0] * K.n
    for v in range(K.n):
        inv[pi[v]] = v
    out = []
    for f, (a, b) in enumerate(K.E):
        s = K.eid(inv[a], inv[b])
        if s == f and list(sigma) == [0, 1, 2]:
            continue
        out.append((f, s))
    return out


def act(K, g, X):
    pi, sigma = g
    Y = [None] * K.ne
    for t, (a, b) in enumerate(K.E):
        Y[K.eid(pi[a], pi[b])] = sigma[X[t]]
    return Y


def path_edges(K, k):
    return {K.eid(t, t + 1) for t in range(k - 1)} if k else set()


# ------------------------------------------------- reduction lemma: stabiliser

def check_stabiliser(K, k, gens):
    """Each g must map the fixed-path set S_k to itself: pi a vertex
    permutation mapping the path's edge set onto itself, sigma a colour
    permutation fixing colour 0.  Goodness is invariant under every
    (pi, sigma) (lemma L1), so these conditions are exactly what g
    needs."""
    P = path_edges(K, k)
    for x, (pi, sigma) in enumerate(gens):
        if not is_perm(pi, K.n) or not is_perm(sigma, 3):
            raise Fail(f'generator {x}: not a permutation pair')
        if k:
            img = {K.eid(pi[a], pi[b]) for (a, b) in (K.E[e] for e in P)}
            if img != P:
                raise Fail(f'generator {x} = {pi_str(pi, sigma)}: does not map the fixed '
                           f'path 0..{k - 1} to itself (reduction mis-stated)')
            if sigma[0] != 0:
                raise Fail(f'generator {x} = {pi_str(pi, sigma)}: moves colour 0 of the '
                           f'fixed path (reduction mis-stated)')


def pi_str(pi, sigma):
    moved = [v for v in range(len(pi)) if pi[v] != v]
    return f'vertices {moved}->{[pi[v] for v in moved]}, colours {list(sigma)}'


# ------------------------------------------------- reading DIMACS

def read_cnf(path):
    header, cls, cur = None, [], []
    with open(path) as f:
        for line in f:
            if line.startswith('c'):
                continue
            if line.startswith('p'):
                if header is not None:
                    raise Fail('two headers')
                header = line.split()
                continue
            for tok in line.split():
                v = int(tok)
                if v == 0:
                    if not cur:
                        raise Fail('empty clause')
                    cls.append(cur)
                    cur = []
                else:
                    cur.append(v)
    if cur:
        raise Fail('unterminated clause')
    if header is None or header[:2] != ['p', 'cnf'] or len(header) != 4:
        raise Fail('bad header')
    return int(header[2]), int(header[3]), cls


def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        h.update(f.read())
    return h.hexdigest()


# ------------------------------------------------- clause-by-clause soundness

class Encoding:
    """The auditor's own reading of the variables of (n, k, gens)."""

    def __init__(self, n, k, gens):
        self.K = K = Kn(n)
        self.k = k
        self.gens = gens
        self.comp = [compared_positions(K, g) for g in gens]
        self.sig = [list(g[1]) for g in gens]
        self.aux = {}
        v = 3 * K.ne
        for gi, cp in enumerate(self.comp):
            for j in range(1, len(cp) + 1):
                v += 1
                self.aux[v] = (gi, j)
        self.nvars = v
        self.path = path_edges(K, k)
        self.touch = {}             # edge -> compared positions (g, j) using it
        for gi, cp in enumerate(self.comp):
            for j, (f, s) in enumerate(cp, 1):
                self.touch.setdefault(f, set()).add((gi, j))
                self.touch.setdefault(s, set()).add((gi, j))

    def valid(self, clause, level):
        """level 0: colouring only; 1: + fixed path; 2: + generator
        inequalities.  Returns True iff the clause holds in every local
        state (module docstring)."""
        K = self.K
        lits, L, A = [], set(), set()
        for l in clause:
            v = abs(l)
            if 1 <= v <= 3 * K.ne:
                e, c = divmod(v - 1, 3)
                lits.append(('x', e, c, l > 0))
                L.add(e)
            elif v in self.aux:
                g, j = self.aux[v]
                lits.append(('q', g, j, l > 0))
                A.add((g, j))
                f, s = self.comp[g][j - 1]
                L.update((f, s))
            else:
                raise Fail(f'variable {v} has no meaning')
        A = sorted(A)
        free = [(g, j) for (g, j) in A if j > 1 and (g, j - 1) not in A]
        Ls = sorted(L)
        pathc = [e for e in Ls if e in self.path] if level >= 1 else []
        # inequality steps whose edges are local and whose prefix is known:
        # position 1 of any generator (no prefix), or position j + 1 after a
        # mentioned eq(g, j)
        first, after = [], []
        if level >= 2:
            for e in Ls:
                for (g, j) in self.touch.get(e, ()):
                    f, s = self.comp[g][j - 1]
                    if f not in L or s not in L or (g, j) in A:
                        continue
                    if j == 1:
                        first.append((g, f, s))
                    elif (g, j - 1) in A:
                        after.append((g, j, f, s))
            first, after = sorted(set(first)), sorted(set(after))
        for cols in itertools.product(range(3), repeat=len(Ls)):
            X = dict(zip(Ls, cols))
            if any(X[e] != 0 for e in pathc):
                continue
            if any(X[f] > self.sig[g][X[s]] for g, f, s in first):
                continue
            for P in itertools.product((False, True), repeat=len(free)):
                Pm = dict(zip(free, P))
                eq, ok = {}, True
                for (g, j) in A:
                    if j == 1:
                        pv = True
                    elif (g, j - 1) in eq:
                        pv = eq[(g, j - 1)]
                    else:
                        pv = Pm[(g, j)]
                    f, s = self.comp[g][j - 1]
                    y = self.sig[g][X[s]]
                    if level >= 2 and pv and X[f] > y:
                        ok = False
                        break
                    eq[(g, j)] = pv and X[f] == y
                if not ok:
                    continue
                if any(eq[(g, j - 1)] and X[f] > self.sig[g][X[s]] for g, j, f, s in after):
                    continue
                # eq(g, j) -> eq(g, i) and prefix(g, j) -> eq(g, i), i < j
                if any(eq[(g, j)] and not eq[(h, i)]
                       for (g, j) in A for (h, i) in A if h == g and i < j):
                    continue
                if any(Pm[(g, j)] and not eq[(h, i)]
                       for (g, j) in free for (h, i) in A if h == g and i < j):
                    continue
                sat = False
                for kind, a, b, pos in lits:
                    val = (X[a] == b) if kind == 'x' else eq[(a, b)]
                    if val == pos:
                        sat = True
                        break
                if not sat:
                    return False
        return True

    def audit(self, path, m):
        nv, nc, cls = read_cnf(path)
        if len(cls) != nc:
            raise Fail(f'header says {nc} clauses, file has {len(cls)}')
        if nv != self.nvars:
            raise Fail(f'header declares {nv} variables; the stated encoding has '
                       f'{self.nvars} (3*{self.K.ne} colour + {len(self.aux)} auxiliary)')
        kinds = {'colouring (exactly-one)': 0, 'auxiliary definition': 0,
                 'fixed path': 0, 'lex-leader inequality': 0}
        for i, cl in enumerate(cls):
            if self.valid(cl, 0):
                aux = any(abs(l) > 3 * self.K.ne for l in cl)
                kinds['auxiliary definition' if aux else 'colouring (exactly-one)'] += 1
            elif self.valid(cl, 1):
                kinds['fixed path'] += 1
            elif self.valid(cl, 2):
                kinds['lex-leader inequality'] += 1
            else:
                raise Fail(f'clause {i + 1} {cl} is not implied by the stated meaning '
                           f'(it excludes an admissible colouring)')
        self.inventory_equal(cls)
        return nc, kinds

    # ---- inventory: the clause set the stated meaning generates, both ways

    def x(self, e, c):
        return 3 * e + c + 1

    def generated(self, mutant=None):
        """The base clauses the stated meaning generates, grouped by what
        they define: ('edge', e) exactly-one; ('path', e) the unit; ('aux',
        v) the four prefix/lex families at auxiliary v = eq(g, j), with
        pre = eq(g, j - 1)
        and no prefix literal at j = 1, Y = (g.X)(f) = sigma(X(s)):
          pre -> not(X_f = a and Y = b)   for a > b   (the inequality)
          pre and X_f = Y = a -> eq        for each a
          eq -> pre                        (j > 1)
          eq and X_f = a -> Y = a          for each a.
        A clause is a sorted tuple of distinct literals (a literal named
        twice is written once); tautologies are kept, as generated.
        `mutant` (corruptions.py only) generates a wrong set on purpose:
        'direction' (a < b), 'no-prefix' (inequality without pre),
        'no-definition' (no pre and X_f = Y = 0 -> eq), 'no-monotone'."""
        K, x = self.K, self.x
        groups = []
        for e in range(K.ne):
            cl = [(x(e, 0), x(e, 1), x(e, 2))]
            cl += [(-x(e, d), -x(e, c)) for c, d in itertools.combinations(range(3), 2)]
            groups.append((('edge', e), cl))
        for e in sorted(self.path):
            groups.append((('path', e), [(x(e, 0),)]))
        for v, (g, j) in sorted(self.aux.items()):
            f, s = self.comp[g][j - 1]
            inv = [self.sig[g].index(b) for b in range(3)]
            y = [x(s, inv[b]) for b in range(3)]        # Y = b  iff  X(s) = sigma^-1(b)
            pre = [-(v - 1)] if j > 1 else []
            cl = []
            for a in range(3):
                bs = range(a + 1, 3) if mutant == 'direction' else range(a)
                cl += [(pre if mutant != 'no-prefix' else []) + [-x(f, a), -y[b]] for b in bs]
                if not (mutant == 'no-definition' and a == 0):
                    cl.append(pre + [-x(f, a), -y[a], v])
            if j > 1 and mutant != 'no-monotone':
                cl.append([-v, v - 1])
            cl += [[-v, -x(f, a), y[a]] for a in range(3)]
            groups.append((('aux', v), [tuple(sorted(set(c))) for c in cl]))
        return groups

    def check_generated_meaning(self, groups):
        """Each group, read as a truth table over its own variables, has
        exactly the models the stated meaning gives it: one colour per edge;
        colour 0 on a fixed-path edge; eq = (pre and X_f = Y) and
        (pre -> X_f <= Y) at an auxiliary, with pre = true at j = 1 and the
        edges' colours ranging over the 3-colourings (exactly-one)."""
        x = self.x
        for (kind, i), cl in groups:
            if kind == 'edge':
                for bits in itertools.product((False, True), repeat=3):
                    val = {x(i, c): bits[c] for c in range(3)}
                    sat = all(any(val[abs(l)] == (l > 0) for l in c) for c in cl)
                    if sat != (sum(bits) == 1):
                        raise Fail(f'generated exactly-one clauses of edge {i} do not mean one colour')
                continue
            if kind == 'path':
                for c in range(3):
                    val = {x(i, d): d == c for d in range(3)}
                    if all(any(val[abs(l)] == (l > 0) for l in q) for q in cl) != (c == 0):
                        raise Fail(f'generated unit of path edge {i} does not mean colour 0')
                continue
            g, j = self.aux[i]
            f, s = self.comp[g][j - 1]
            es = sorted({f, s})
            for cols in itertools.product(range(3), repeat=len(es)):
                X = dict(zip(es, cols))
                Y = self.sig[g][X[s]]
                for pre in ((True,) if j == 1 else (False, True)):
                    for eq in (False, True):
                        val = {x(e, c): X[e] == c for e in es for c in range(3)}
                        val[i] = eq
                        if j > 1:
                            val[i - 1] = pre
                        sat = all(any(val[abs(l)] == (l > 0) for l in q) for q in cl)
                        want = eq == (pre and X[f] == Y) and (not pre or X[f] <= Y)
                        if sat != want:
                            raise Fail(f'generated clauses of auxiliary {i} = eq({g}, {j}) do not '
                                       f'mean the stated definition (X_f={X[f]}, Y={Y}, pre={pre}, eq={eq})')

    def check_positions(self):
        """The compared positions a second way, by pushing each source edge
        forward (compared_positions looks each position's source up through
        pi^-1): a position missing from both the generated set and the
        formula would change the order compared, so it must not depend on one
        derivation."""
        K = self.K
        for gi, (pi, sigma) in enumerate(self.gens):
            src = [None] * K.ne
            for s, (a, b) in enumerate(K.E):
                src[K.eid(pi[a], pi[b])] = s
            fwd = [(f, s) for f, s in enumerate(src) if s != f or list(sigma) != [0, 1, 2]]
            if None in src or fwd != self.comp[gi]:
                raise Fail(f'generator {gi}: compared positions differ between the two derivations')

    def inventory_equal(self, cls):
        """The formula's clause multiset equals the generated one: nothing
        missing, nothing extra, each clause as often as generated."""
        self.check_positions()
        groups = self.generated()
        self.check_generated_meaning(groups)
        want = collections.Counter(c for _, cl in groups for c in cl)
        have = collections.Counter(tuple(sorted(c)) for c in cls)
        if want != have:
            miss, extra = want - have, have - want
            ex = (f'e.g. missing {sorted(miss)[0]}' if miss else f'e.g. extra {sorted(extra)[0]}')
            raise Fail(f'clause inventory differs from the {sum(want.values())} clauses the stated meaning '
                       f'generates: {sum(miss.values())} missing, {sum(extra.values())} extra ({ex})')
        self.inventory = {k: sum(len(cl) for (kk, _), cl in groups if kk == k) for k in ('edge', 'path', 'aux')}


def gens_from(args_gens, n, k):
    if args_gens:
        with open(args_gens) as f:
            return [(list(p), list(s)) for p, s in json.load(f)]
    return stated_generators(n, k)


def cmd_cnf(path, n, m, k, gens):
    enc = Encoding(n, k, gens)
    check_stabiliser(enc.K, k, gens)
    nc, kinds = enc.audit(path, m)
    return (f'{os.path.relpath(path, ROOT) if path.startswith(ROOT) else os.path.basename(path)}'
            f' (n={n}, m={m}, fixed P_{k}, {len(gens)} generators) sha256 {sha256(path)[:16]}: '
            f'{nc} clauses valid: ' + ', '.join(f'{a} {b}' for a, b in kinds.items())
            + f'; inventory equal to the generated set ({inv_str(enc.inventory)})')


def inv_str(inv):
    return (f"exactly-one {inv['edge']}, fixed path {inv['path']}, prefix/lex {inv['aux']}; "
            f"each group means exactly its stated definition; compared positions derived twice")


# ------------------------------------------------- path clauses

def path_of_clause(K, m, clause):
    """(colour, vertex sequence) if the clause says 'not every edge of this
    path on m vertices has colour c', else None."""
    if len(clause) != m - 1:
        return None
    dec = []
    for l in clause:
        if l >= 0 or -l > 3 * K.ne:
            return None
        dec.append(divmod(-l - 1, 3))
    if len({c for _, c in dec}) != 1 or len({e for e, _ in dec}) != m - 1:
        return None
    nbr = {}
    for e, _ in dec:
        a, b = K.E[e]
        nbr.setdefault(a, []).append(b)
        nbr.setdefault(b, []).append(a)
    ends = sorted(v for v, w in nbr.items() if len(w) == 1)
    if len(nbr) != m or len(ends) != 2 or any(len(w) > 2 for w in nbr.values()):
        return None
    walk, prev = [ends[0]], None
    while len(walk) <= m:
        nxt = [w for w in nbr[walk[-1]] if w != prev]
        if not nxt:
            break
        prev = walk[-1]
        walk.append(nxt[0])
    if len(walk) != m or len(set(walk)) != m:
        return None
    return dec[0][1], tuple(walk)


def cmd_paths(n, m, logs):
    K = Kn(n)
    out = []
    for p in logs:
        cnt = 0
        with (gzip.open(p, 'rt') if p.endswith('.gz') else open(p)) as f:
            for ln, line in enumerate(f, 1):
                t = [int(x) for x in line.split()]
                if not t or t[-1] != 0 or 0 in t[:-1]:
                    raise Fail(f'{os.path.basename(p)}:{ln}: not one 0-terminated clause')
                if path_of_clause(K, m, t[:-1]) is None:
                    raise Fail(f'{os.path.basename(p)}:{ln}: not a P_{m} path clause in one colour')
                cnt += 1
        name = os.path.relpath(p, ROOT) if os.path.abspath(p).startswith(ROOT) else os.path.basename(p)
        out.append(f'{name} (n={n}, m={m}) sha256 {sha256(p)[:16]}: {cnt} clauses, each a P_{m} path clause')
    return out


# ------------------------------------------------- ladder

# The rungs of the certificate (the ladder and K_18):
# (n, m, k, CNF).  A rung with k > 0 assumes R_3(P_k) <= n.
RUNGS = [(5, 3, 0), (6, 4, 3), (9, 5, 4), (10, 6, 5), (13, 7, 6),
         (14, 8, 7), (17, 9, 8), (18, 10, 9)]


def solved_whole_by_verify():
    """Rungs (n, m) that ../check.py solves whole and checks (its LADDER)."""
    txt = open(os.path.join(CHECKS, 'check.py')).read()
    line = next(l for l in txt.splitlines() if l.startswith('LADDER = ['))
    return [tuple(map(int, q))[:2] for q in re.findall(r'\((\d+), (\d+), (\d+)\)', line)]


def cmd_ladder(rungs):
    solved = solved_whole_by_verify()
    out = []
    for x, (n, m, k) in enumerate(rungs):
        if k == 0:
            out.append(f'K_{n}, P_{m}: no fixed path; nothing assumed')
            continue
        if k >= m:
            raise Fail(f'K_{n}, P_{m}: fixed P_{k} is not shorter than P_{m} (circular)')
        below = [(lo_n, lo_m) for (lo_n, lo_m, _) in rungs[:x] if lo_m == k and lo_n <= n and (lo_n, lo_m) in solved]
        if not below:
            raise Fail(f'K_{n}, P_{m}: fixed P_{k} needs R_3(P_{k}) <= {n}, which no lower rung '
                       f'solved whole by check.py establishes (reduction mis-stated)')
        out.append(f'K_{n}, P_{m}: fixed P_{k} rests on R_3(P_{k}) <= {below[0][0]} (rung K_{below[0][0]}, '
                   f'solved whole by check.py)')
    return out


# ------------------------------------------------- small exhaustive instances

def all_path_clauses(K, m):
    """Second, independent enumeration of the eager path clauses: vertex
    sequences of length m with first < last, one clause per colour."""
    out = set()
    for seq in itertools.permutations(range(K.n), m):
        if seq[0] > seq[-1]:
            continue
        es = [K.eid(seq[i], seq[i + 1]) for i in range(m - 1)]
        for c in range(3):
            out.add(tuple(sorted(-(3 * e + c + 1) for e in es)))
    return out


def dpll(cls, assign):
    while True:
        new, unit = [], False
        for c in cls:
            rest, sat = [], False
            for l in c:
                v = assign.get(abs(l))
                if v is None:
                    rest.append(l)
                elif v == (l > 0):
                    sat = True
                    break
            if sat:
                continue
            if not rest:
                return False
            if len(rest) == 1:
                assign[abs(rest[0])] = rest[0] > 0
                unit = True
            new.append(rest)
        cls = new
        if not unit:
            break
    if not cls:
        return True
    v = abs(cls[0][0])
    for val in (True, False):
        a = dict(assign)
        a[v] = val
        if dpll(cls, a):
            return True
    return False


class CnfEval:
    """Does a CNF have a model whose colour variables are the colouring X?
    Decided by search over the auxiliaries, not by the witness."""

    def __init__(self, cls, ne):
        self.pre = []
        for c in cls:
            el = [(divmod(abs(l) - 1, 3), l > 0) for l in c if abs(l) <= 3 * ne]
            al = [l for l in c if abs(l) > 3 * ne]
            self.pre.append((el, al))

    def accepts(self, X):
        red = []
        for el, al in self.pre:
            if any((X[e] == c) == pos for (e, c), pos in el):
                continue
            if not al:
                return False
            red.append(al)
        return dpll(red, {})


def code(X):
    v = 0
    for c in reversed(X):
        v = 3 * v + c
    return v


def decode(v, ne):
    X = []
    for _ in range(ne):
        X.append(v % 3)
        v //= 3
    return X


def small(n, m, k, gens, paths_file=None, dump_paths=None, cnf_file=None, lemmas=True):
    """Exhaustive end-to-end check on K_n, P_m, fixed P_k, over all 3^|E|
    colourings:
      E0  premise: if k > 0, every colouring has a monochromatic P_k;
      E1  clause-by-clause soundness (as `cnf`) and the stabiliser lemma;
      E2  for every colouring with the path fixed, the formula accepts it
          iff it is admissible (search over auxiliaries, not the witness);
      E3  relabelling vertices and colours preserves the longest
          monochromatic path (lemma L1), and every orbit of good colourings
          under S_n x S_3 has a member the formula accepts (no colouring
          class is lost);
      E4  the eager path clauses are exactly the clauses the path-clause
          predicate accepts, and a colouring violates one iff it has a
          monochromatic P_m; so base + all path clauses has exactly the
          admissible good colourings as models."""
    K = Kn(n)
    ne = K.ne
    out = []
    if cnf_file is None:
        r = subprocess.run([sys.executable, os.path.join(CHECKS, 'encode.py'), str(n), str(m),
                            '--fix', str(k)], capture_output=True, text=True, check=True)
        cnf_file = os.path.join(os.environ.get('TMPDIR', '/tmp'), f'audit-k{n}p{m}f{k}-{os.getpid()}.cnf')
        with open(cnf_file, 'w') as f:
            f.write(r.stdout)
        made = True
    else:
        made = False
    try:
        enc = Encoding(n, k, gens)
        if lemmas:
            check_stabiliser(K, k, gens)
        nc, kinds = enc.audit(cnf_file, m)
        _, _, cls = read_cnf(cnf_file)
    finally:
        if made:
            os.unlink(cnf_file)
    tag = f'K_{n}, P_{m}, fixed P_{k}'
    out.append(f'{tag}: E1 {nc} clauses valid (' + ', '.join(f'{a} {b}' for a, b in kinds.items())
               + f'); inventory equal to the generated set ({inv_str(enc.inventory)})')

    N = 3 ** ne
    longest = [longest_mono_path(K, decode(v, ne)) for v in range(N)]
    if lemmas and k and min(longest) < k:
        raise Fail(f'{tag}: E0 a colouring of K_{n} has no monochromatic P_{k}, so fixing one '
                   f'is not justified (reduction mis-stated)')
    out.append(f'{tag}: E0 ' + (f'all {N} colourings have a monochromatic P_{k}' if k else 'no premise'))

    P = path_edges(K, k)
    ev = CnfEval(cls, ne)

    def admissible(X):
        return all(X[e] == 0 for e in P) and all(X <= act(K, g, X) for g in gens)
    acc = {}
    free = [e for e in range(ne) if e not in P]
    for cols in itertools.product(range(3), repeat=len(free)):
        X = [0] * ne
        for e, c in zip(free, cols):
            X[e] = c
        a = ev.accepts(X)
        if a != admissible(X):
            raise Fail(f'{tag}: E2 formula {"accepts" if a else "rejects"} {X}, which is '
                       f'{"not " if not admissible(X) else ""}admissible')
        acc[code(X)] = a
    out.append(f'{tag}: E2 {len(acc)} path-fixed colourings: formula accepts exactly the '
               f'{sum(acc.values())} admissible ones')

    # orbits under S_n x S_3: generated by (0 1), the n-cycle, colours (0 1), (0 1 2)
    full = [([1, 0] + list(range(2, n)), [0, 1, 2]), ([(v + 1) % n for v in range(n)], [0, 1, 2]),
            (list(range(n)), [1, 0, 2]), (list(range(n)), [1, 2, 0])]
    parent = list(range(N))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a
    for v in range(N):
        X = decode(v, ne)
        for g in full:
            w = code(act(K, g, X))
            if longest[w] != longest[v]:
                raise Fail(f'{tag}: E3 relabelling changed the longest monochromatic path of {X}')
            a, b = find(v), find(w)
            if a != b:
                parent[a] = b
    good_orbits, kept = set(), set()
    for v in range(N):
        if longest[v] < m:
            good_orbits.add(find(v))
            if acc.get(v):
                kept.add(find(v))
    lost = good_orbits - kept
    if lost:
        X = decode(min(v for v in range(N) if find(v) in lost and longest[v] < m), ne)
        raise Fail(f'{tag}: E3 {len(lost)} of {len(good_orbits)} classes of good colourings have no '
                   f'member the formula accepts, e.g. the class of {X} (reduction mis-stated)')
    ngood = sum(1 for v in range(N) if longest[v] < m)
    out.append(f'{tag}: E3 relabelling preserves the longest monochromatic path; all '
               f'{len(good_orbits)} classes of the {ngood} good colourings keep a member the formula accepts')

    if paths_file:
        pset = {tuple(sorted(int(x) for x in l.split()[:-1]))
                for l in open(paths_file) if l.strip() and l[0] not in 'cp'}
    else:
        pset = all_path_clauses(K, m)
    if dump_paths:
        with open(dump_paths, 'w') as f:
            for c in sorted(pset):
                f.write(' '.join(map(str, c)) + ' 0\n')
    pred = set()
    for es in itertools.combinations(range(ne), m - 1):
        for c in range(3):
            cl = tuple(sorted(-(3 * e + c + 1) for e in es))
            if path_of_clause(K, m, list(cl)) is not None:
                pred.add(cl)
    if pset != pred:
        miss, extra = pred - pset, pset - pred
        raise Fail(f'{tag}: E4 eager path clauses incomplete or wrong: {len(miss)} missing '
                   f'(e.g. {sorted(miss)[:1]}), {len(extra)} not path clauses')
    plist = [[divmod(-l - 1, 3) for l in c] for c in pset]
    for v in range(N):
        X = decode(v, ne)
        hit = any(all(X[e] == c for e, c in cl) for cl in plist)
        if hit != (longest[v] >= m):
            raise Fail(f'{tag}: E4 colouring {X}: path clauses and DFS disagree')
    out.append(f'{tag}: E4 {len(pset)} eager path clauses = every P_{m} in every colour; a colouring '
               f'violates one iff it has a monochromatic P_{m} (all {N})')
    return out


SMALL = [(4, 3, 0), (5, 4, 0), (5, 4, 2), (5, 4, 3)]


def cmd_all():
    out = ['# checks/audit/audit.py all', '',
           '## Base formulas, clause by clause (module docstring), and the stabiliser lemma']
    for n, m, k in RUNGS:
        p = os.path.join(DATA, 'cnf', f'k{n}p{m}.cnf')
        out.append(cmd_cnf(p, n, m, k, stated_generators(n, k)))
    out += ['', '## Path-clause logs in the data']
    for n, m, f in [(18, 10, 'data/k18/genlog.txt'), (18, 10, 'data/k18/split/genlog.txt'),
                    (10, 6, 'checks/controls/paths-good.txt')]:
        out += cmd_paths(n, m, [os.path.join(ROOT, f)])
    out += ['', '## Ladder: every fixed path rests on a rung solved whole'] + cmd_ladder(RUNGS)
    out += ['', '## Small instances, exhaustive (formula from the pinned command encode.py n m --fix k)']
    for n, m, k in SMALL:
        out += small(n, m, k, stated_generators(n, k))
    out += ['', 'PASS']
    return out


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    a = sub.add_parser('cnf')
    a.add_argument('cnf')
    for x in 'nmk':
        a.add_argument(x, type=int)
    a.add_argument('--gens')
    a = sub.add_parser('paths')
    a.add_argument('n', type=int)
    a.add_argument('m', type=int)
    a.add_argument('logs', nargs='+')
    a = sub.add_parser('ladder')
    a.add_argument('--rungs', help='JSON list of [n, m, k] replacing the stated rungs')
    a = sub.add_parser('small')
    for x in 'nmk':
        a.add_argument(x, type=int)
    a.add_argument('--gens')
    a.add_argument('--cnf')
    a.add_argument('--paths')
    a.add_argument('--dump-paths')
    a.add_argument('--no-lemma', action='store_true',
                   help='skip the stabiliser and premise checks (corruption tests: shows E3 alone '
                        'catches a mis-stated reduction)')
    sub.add_parser('all')
    args = ap.parse_args()
    try:
        if args.cmd == 'cnf':
            lines = [cmd_cnf(os.path.abspath(args.cnf), args.n, args.m, args.k,
                             gens_from(args.gens, args.n, args.k))]
        elif args.cmd == 'paths':
            lines = cmd_paths(args.n, args.m, [os.path.abspath(p) for p in args.logs])
        elif args.cmd == 'ladder':
            rungs = [tuple(r) for r in json.load(open(args.rungs))] if args.rungs else RUNGS
            lines = cmd_ladder(rungs)
        elif args.cmd == 'small':
            lines = small(args.n, args.m, args.k, gens_from(args.gens, args.n, args.k),
                          args.paths, args.dump_paths, args.cnf, not args.no_lemma)
        else:
            lines = cmd_all()
    except Fail as e:
        print(f'FAIL {e}')
        sys.exit(1)
    print('\n'.join(lines))


if __name__ == '__main__':
    main()
