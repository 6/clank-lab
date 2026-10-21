# The three-color Ramsey number of the 10-vertex path

[![Checks](https://github.com/6/clank-lab/actions/workflows/path-ramsey.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/path-ramsey.yml)

Color each edge of a [complete graph](https://mathworld.wolfram.com/CompleteGraph.html)
with one of three colors. [Ramsey's theorem](https://en.wikipedia.org/wiki/Ramsey%27s_theorem)
says that with enough vertices some long [path](https://mathworld.wolfram.com/PathGraph.html)
has all its edges the same color; the three-color Ramsey number
$R(P_n, P_n, P_n)$ is the smallest number of vertices that forces a
one-colored path $P_n$ on $n$ vertices. In 1975 Faudree and Schelp
conjectured that

$$R(P_n, P_n, P_n) = 2n - 2 + (n \bmod 2),$$

that is, $2n - 2$ for even $n$ and $2n - 1$ for odd $n$, and gave colorings
showing it is at least that. Gyárfás, Ruszinkó, Sárközy and Szemerédi proved
this for all sufficiently large $n$ in 2007, and Dybizbański, Dzido and
Radziszowski completed the values for $n \le 9$ in 2016, settling $n = 8$
and $n = 9$;
[Radziszowski's survey of small Ramsey numbers](https://www.combinatorics.org/ojs/index.php/eljc/article/view/DS1)
lists $n = 10$ as the first open case. We prove that

$$R(P_{10}, P_{10}, P_{10}) = 18,$$

as conjectured: every 3-coloring of the edges of $K_{18}$ has a one-colored
path on 10 vertices, and a classical coloring of $K_{17}$, Faudree and
Schelp's, shows that 18 is needed. We found the result neither in the survey
nor in the literature we searched, so it is likely new.

The proof is a SAT computation. A formula that every coloring without such a
path would satisfy, after symmetry reductions, is split into 15,956 pieces,
and each piece is refuted with a certificate. A Lean proof derives the value
from the definitions: it proves that the symmetry reductions and the
formula lose no coloring, that the pieces cover every case, and the lower
bound, and Lean's verified certificate checker checked every certificate.
Those checks ran as compiled code, so they trust Lean's compiler as well as
its kernel. The same refutations, before their conversion for Lean, were
also checked separately by the verified checker cake_lpr. The upper bounds
for $n \le 9$ that the computation uses are re-derived by the same method
rather than taken from the literature.

Computer-assisted; not yet reviewed by experts.

The proofs, the Lean formalization, the search code, the certificate checkers and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

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
solver regenerates them and Lean checks them. This needs Python 3.9 or
later (standard library only), git, gcc, g++, make and network access to
GitHub, besides elan. The quick check re-solves the smaller cases and
checks them, the cover and a random sample of cubes, both in Lean and with
cake_lpr; it also runs the encoding auditor and planted errors, which must
be rejected. It takes about fifteen minutes:

```sh
python3 checks/check.py quick --work /tmp/path-ramsey-work
```

The full check re-solves every cube and checks it in Lean, then builds the
final theorem `R3_P10_eq_18 : ramsey3Path 10 = 18` with
`lake build R3P10Final`; only this step establishes the value in Lean. It takes about 250
CPU-hours on as many cores as are available, resumes when rerun, and needs
about 70 GB of disk:

```sh
python3 checks/check.py full --work /tmp/path-ramsey-work
```

Details for specialists are in [the Lean notes](lean/README.md) and
[the checking notes](checks/README.md).

## Credits

R. J. Faudree and R. H. Schelp posed the conjecture and gave the coloring
behind the lower bound. A. Figaj and T. Łuczak found the asymptotics of
three-color path Ramsey numbers, A. Gyárfás, M. Ruszinkó, G. N. Sárközy and
E. Szemerédi proved the conjecture for large $n$, and S. Letzter later gave a
simpler proof for long paths. J. Dybizbański,
T. Dzido and S. Radziszowski settled $n = 8$ and $n = 9$, completing the known
values, and this computation follows their work directly: it re-derives
the upper bounds up to $n = 9$ and starts from their bound for $n = 9$. R. W. Irving, Yang Yuansheng and
P. Rowlinson found the values for $n = 4$ to $7$. S. Radziszowski's dynamic survey records
the problem's status and the sources of the earlier values. The paper
also credits related work on other three-color path and cycle Ramsey
numbers, including N. F. Galindez's recent SAT bound for 10-cycles. The
computation
uses A. Biere's CaDiCaL solver and its user-propagator interface by
K. Fazekas, A. Niemetz, M. Preiner, M. Kirchweger, S. Szeider and A. Biere;
drat-trim by N. Wetzler, M. Heule and W. Hunt; and cake_lpr by Y. K. Tan,
M. Heule and M. Myreen. Lean, its LRAT checker and Mathlib, with their
contributors, supplied the formal-development infrastructure.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamPathRamsey2026,
  author       = {Graham, P.},
  title        = {{The three-color Ramsey number of the 10-vertex path}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/path-ramsey-v1/results/path-ramsey}}
}
```
