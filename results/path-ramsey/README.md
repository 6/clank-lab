# The three-color Ramsey number of the 10-vertex path

[![Checks](https://github.com/6/clank-lab/actions/workflows/path-ramsey.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/path-ramsey.yml)

Color each edge of a [complete graph](https://mathworld.wolfram.com/CompleteGraph.html)
with one of three colors. [Ramsey's theorem](https://en.wikipedia.org/wiki/Ramsey%27s_theorem)
says that with enough vertices some long [path](https://mathworld.wolfram.com/PathGraph.html)
has all its edges the same color; the three-color Ramsey number
$R(P_n, P_n, P_n)$ is the smallest number of vertices that forces a
one-colored path $P_n$ on $n$ vertices. Dybizbański, Dzido and Radziszowski (DDR)'s
[Conjecture 2, arXiv:1207.5851v3, Section 2](https://arxiv.org/abs/1207.5851v3)
states the formula below and attributes its suggestion to Faudree and Schelp
(1975), quoting “they feel”:

$$R(P_n, P_n, P_n) = 2n - 2 + (n \bmod 2).$$

Theorem 1 in Gyárfás, Ruszinkó, Sárközy and Szemerédi's
[author manuscript dated July 9, 2012, Section 1.1](https://www.renyi.hu/~gyarfas/Cikkek/120_sharp3cfin.pdf)
proves this formula for all sufficiently large $n$ (published in 2007,
with a corrigendum in 2008). Dybizbański, Dzido and Radziszowski proved
$R(P_8, P_8, P_8)=14$ in Theorem 10 and $R(P_9, P_9, P_9)\le17$ in
Theorem 8; with their Section 2 lower bound, the latter gives equality $17$.
[Radziszowski's survey, revision 18, p. 65, Sections 6.4 and 6.4.1(c)](https://www.cs.rit.edu/~spr/ElJC/ejcram18.pdf)
records the formula through nine vertices and the ten-vertex path as the
first open case. We prove that

$$R(P_{10}, P_{10}, P_{10}) = 18,$$

as conjectured: every 3-coloring of the edges of $K_{18}$ has a one-colored
path on 10 vertices. The new bound is the upper bound $18$; the matching
$K_{17}$ coloring is the even-case blow-up in Gyárfás, Ruszinkó, Sárközy
and Szemerédi's Section 1.1 after Theorem 1, also given in DDR's Section 2.
In that coloring each color has two label
classes, of 9 and 8 vertices, and every edge of the color lies inside one of
them, so a one-colored connected piece has at most 9 vertices. This settles the case $n = 10$; the general conjecture remains open.

<img src="data/lower-bound.svg" width="650" alt="Four parts of sizes 5, 4, 4, 4; colored edges encode the lower-bound coloring.">

The proof is a SAT computation, checked as a Lean formalization with trusted
native evaluation. Every coloring of $K_{18}$ without a one-colored $P_{10}$
contains a one-colored $P_9$, since $R(P_9, P_9, P_9) \le 17$, so it can be
relabeled to have that path in a fixed place and then reduced further by
symmetry; the resulting formula is split into 15,956 pieces, a further
certificate shows the pieces cover every case, and each piece is refuted with
a certificate. Lean proves from the definitions that this chain loses no
coloring, and proves the lower bound by its kernel. The certificate checks
(the 15,956 pieces, the cover and the smaller cases) and one comparison of the
formula with its definition run Lean's verified certificate checker as
compiled code (`Lean.ofReduceBool`), so they trust Lean's compiler as well as
its kernel. The same refutations, before their conversion for Lean, were also
checked by the verified checker cake_lpr, and a separate checker with its own
code re-checked every piece. The upper bounds for $n \le 9$ that the
computation uses, $R(P_9, P_9, P_9) \le 17$ among them, are re-derived by the
same method rather than taken from the literature.

Checked in Lean from the definitions, with compiled evaluation; not yet reviewed by experts.

The proofs, the Lean formalization, the search code, the certificate checkers and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23754649](https://doi.org/10.5281/zenodo.23754649)

## Check it

The Lean proof is a standard Lake project. With
[elan](https://github.com/leanprover/elan) installed, run from this folder:

```sh
cd lean
lake exe cache get
lake build
```

This takes a few minutes and about 8 GB of disk for the Mathlib cache. It
checks the reduction from colorings to formulas, the lower bound, the value
18 with the certificate facts as hypotheses, the statements and their
axioms. It needs no generated data.

The certificates are about 60 GB, so they aren't included: the bundled
solver regenerates them and Lean checks them. They're also archived on
Zenodo, 36 GB compressed, at
[doi:10.5281/zenodo.23562432](https://doi.org/10.5281/zenodo.23562432);
its README explains how to check them without rerunning the solver. This needs Python 3.9 or
later (standard library only), git, gcc, g++, make and network access to
GitHub, besides elan. The quick check re-solves the smaller cases and
checks them, the cover and a random sample of cubes, both in Lean and with
cake_lpr; it also runs the encoding auditor and planted errors, which must
be rejected. It takes about fifteen minutes:

```sh
python3 checks/check.py quick --work /tmp/path-ramsey-work
```

The full check establishes `R3_P10_eq_18 : ramsey3Path 10 = 18` by
checking all 15,956 pieces, the smaller cases and the cover in Lean:

```sh
python3 checks/check.py full --work /tmp/path-ramsey-work
```

It needs about 70 GB of disk and resumes when rerun. Add `--cross-check`
to check every piece independently with cake_lpr and the input and path-clause
checkers. [Checking notes](checks/README.md) give resource measurements,
completed-check records, historical corrections and development background.

## Credits

R. J. Faudree and R. H. Schelp's [Path Ramsey numbers in multicolorings](https://doi.org/10.1016/0095-8956(75)90080-5) is the origin of the conjectured formula. J. Dybizbański, T. Dzido and S. Radziszowski's [On some three-color Ramsey numbers for paths](https://arxiv.org/abs/1207.5851v3) supplies the conjecture, lower bound and preceding cases. A. Gyárfás, M. Ruszinkó, G. N. Sárközy and E. Szemerédi's [Three-color Ramsey numbers for paths](https://doi.org/10.1007/s00493-007-0043-4), with its [corrigendum](https://doi.org/10.1007/s00493-008-2395-9), supplies the large-path theorem and lower-bound construction.

The computation uses A. Biere and contributors' [CaDiCaL 2.0](https://doi.org/10.1007/978-3-031-65627-9_7) SAT solver, the [IPASIR-UP](https://doi.org/10.4230/LIPIcs.SAT.2023.8) interface of K. Fazekas and coauthors, and N. Wetzler, M. J. H. Heule and W. A. Hunt's [DRAT-trim](https://doi.org/10.1007/978-3-319-09284-3_31). Certificate checking uses Y. K. Tan, M. J. H. Heule and M. O. Myreen's [cake_lpr](https://doi.org/10.1007/978-3-030-72013-1_12) and the work of Lean, LRAT and [Mathlib](https://github.com/leanprover-community/mathlib4) contributors. Related work includes Farideh Khoeini and Tomasz Dzido's [On some three color Ramsey numbers for paths, cycles, stripes and stars](https://arxiv.org/abs/1707.06955), Thibault Gauthier and Chad E. Brown's [A Formal Proof of R(4,5)=25](https://arxiv.org/abs/2404.01761v2), and Zhengyu Li, Conor Duggan, Curtis Bright and Vijay Ganesh's [Verified Certificates via SAT and Computer Algebra Systems for the Ramsey R(3,8) and R(3,9) Problems](https://doi.org/10.24963/ijcai.2025/292). The full work-by-work list is in [Further credits](checks/README.md#further-credits).

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamPathRamsey2026,
  author       = {Graham, P.},
  title        = {{The three-color Ramsey number of the 10-vertex path}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/path-ramsey-v7/results/path-ramsey}},
  doi          = {10.5281/zenodo.23754649}
}
```
