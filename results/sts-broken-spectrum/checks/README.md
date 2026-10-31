# Checks

Run every check from the result's folder with

```sh
python3 -I checks/verify.py
```

It needs Python 3.9 or later (standard library only) and a C compiler (`cc`, or the one named by the `CC` environment variable). It exits with status 0 only if every check passes and every corruption test is rejected, and takes a few seconds.

## Files

- `data/sts39.json`: the Steiner triple system on the points 0 to 38 (`blocks`, 247 triples) and its two bicolorings (`coloring3` and `coloring5`, the color of each point, colors numbered from 0).
- `data/strict4.cnf`: the formula $\Phi_4$ of the paper in DIMACS format. The variable $1 + 4x + c$ means that point $x$ has color $c$, for colors $c = 0, 1, 2, 3$.
- `data/strict4.drat`: a DRAT proof that this formula is unsatisfiable, produced by CaDiCaL 2.1.3.
- `checks/check_design.py`: checks the Steiner triple system axioms and that both colorings are surjective and give every block exactly two colors.
- `checks/strict_cnf.py`: builds the strict $k$-bicoloring formula from the blocks, listing all $k^3$ color assignments of each block, and compares it clause by clause (as a multiset) with a given DIMACS file.
- `checks/drat-trim.c`: DRAT-trim, unmodified (see [THIRD_PARTY.md](../THIRD_PARTY.md)).
- `checks/rup_check.py`: a separate proof checker. It accepts an added clause only when unit propagation from its negation, over the formula and the clauses accepted before it, reaches a conflict; it ignores deletions, which keeps it sound, and needs no resolution-asymmetric-tautology steps.
- `checks/verify.py`: the entry point.

## What the checks establish

1. The 247 blocks form a Steiner triple system on 39 points, with a strict 3-bicoloring (class sizes 10, 12, 17) and a strict 5-bicoloring (class sizes 1, 2, 4, 16, 16).
2. `data/strict4.cnf` is exactly the strict 4-bicoloring formula of this system. Its satisfying assignments are exactly the 4-bicolorings (the encoding lemma of the paper).
3. DRAT-trim and the unit-propagation checker both verify that the proof refutes this formula, so the system has no 4-bicoloring.

Calibration: the same definitions give feasible set $`\{3\}`$ for the Fano plane and for the affine plane of order 3 (by listing all set partitions of their points), and on the Fano plane the formulas for $k = 2, 3, 4$ hold at exactly the $k$-bicolorings among all colorings.

Corruption tests, each of which must be rejected: a design with a pair in two blocks, a design with a block removed, the 3-bicoloring with one point recolored, a 5-coloring missing a color, a 3-coloring with a rainbow block, the formula with one literal changed, and, for both proof checkers, a proof that is only the empty clause, the first half of the proof, and the proof applied to the satisfiable 5-bicoloring formula.

## How the system was found

The 5-bicoloring with classes $`\{0\}`$, $`\{1,2\}`$, $`\{3,\dots,6\}`$, $`\{7,\dots,22\}`$, $`\{23,\dots,38\}`$ was fixed in advance. A SAT formula had one variable for each triple of points that this coloring gives exactly two colors, required every pair of points to lie in exactly one chosen triple, and required a second coloring with classes of sizes 10, 12 and 17 under which every chosen triple has exactly two colors. CaDiCaL 2.1.3 returned the system in `data/` as its first solution. The search is not part of the proof and is not included here; the proof checks the system it produced.

## Further credits

- Zsolt Tuza and Vitaly Voloshin, [Problems and results on colorings of mixed hypergraphs](https://doi.org/10.1007/978-3-540-77200-2_12) (2008); [author's copy](https://spectrum.troy.edu/voloshin/horizon-pf.pdf). Section 7 records Gionfriddo's conjecture and lists it as Open problem 2.
- Tao Jiang, Dhruv Mubayi, Zsolt Tuza, Vitaly Voloshin and Douglas West, [The chromatic spectrum of mixed hypergraphs](https://doi.org/10.1007/s003730200023) (2002), which showed that feasible sets of mixed hypergraphs can have gaps.
- Vitaly Voloshin, On the upper chromatic number of a hypergraph, Australas. J. Combin. 11 (1995), 25–45, which introduced mixed hypergraph colorings.
- Lorenzo Milazzo and Zsolt Tuza, on upper chromatic numbers and strict colorings of Steiner triple systems, Discrete Math. 174 (1997), 247–259, and Discrete Math. 182 (1998), 233–243; and Lorenzo Milazzo, Zsolt Tuza and Vitaly Voloshin, Strict colorings of Steiner triple and quadruple systems: a survey, Discrete Math. 261 (2003), 399–411.
- Mario Gionfriddo, Elena Guardo and Lorenzo Milazzo, [Extending bicolorings for Steiner triple systems](https://doi.org/10.2298/AADM130827019G) (2013), on bicolorings of systems built by doubling, including systems of order 39.
- Csilla Bujtás, Mario Gionfriddo, Elena Guardo, Lorenzo Milazzo, Zsolt Tuza and Vitaly Voloshin, [Extended bicolorings of Steiner triple systems of order 2^h − 1](https://doi.org/10.11650/tjm/8042) (2017).
- Paola Bonacini, Mario Gionfriddo and Lucia Marino, [A construction of Steiner triple systems of type v → 2v+7](https://arxiv.org/abs/2511.04823) (November 2025), and Paola Bonacini, Leonardo Fragapane, Mario Gionfriddo and Lucia Marino, [On (n − 1)-bicolorable Steiner triple systems of order 2^n − 7](https://doi.org/10.13069/jacodesmath.v14i1.456) (October 2026), recent work on bicolorable systems with the largest possible number of colors.
- Marijn Heule, Nathan Wetzler and Warren Hunt, for DRAT-trim and the DRAT proof format; Armin Biere and collaborators, for CaDiCaL.
