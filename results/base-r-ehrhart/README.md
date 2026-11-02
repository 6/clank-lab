# A base-r simplex that is not Ehrhart positive

[![Checks](https://github.com/6/clank-lab/actions/workflows/base-r-ehrhart.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/base-r-ehrhart.yml)

The number of integer points in the $t$-fold dilate of a [lattice polytope](https://en.wikipedia.org/wiki/Ehrhart_polynomial) is a polynomial in $t$, its [Ehrhart polynomial](https://mathworld.wolfram.com/EhrhartPolynomial.html). Its top two coefficients and its constant term are always positive, but the others can be negative; a polytope is called Ehrhart positive when none is. For integers $r \ge 2$ and $d \ge 1$, Liam Solus's base-r $d$-simplex is the [simplex](https://en.wikipedia.org/wiki/Simplex) spanned by the $d$ standard basis vectors and the point $-(r-1)(1, r, \dots, r^{d-1})$. Solus introduced these simplices in 2017 through base-r numeral systems and proved that their $h^\ast$-polynomials are real-rooted, adding that computations suggest they are also Ehrhart positive. Fu Liu recorded this as Solus's conjecture in a 2017 survey (Conjecture 5.1.1), and Liu and Solus restated it in 2018 for all $r \ge 2$ and $d \ge 1$ (Conjecture 2.2). We show that the conjecture is false: for the base-14 5-simplex, with fifth vertex $-(13, 182, 2548, 35672, 499408)$, the number of integer points in the $t$-fold dilate is, for every $t \ge 0$,

$$1 - \frac{268}{15}t + \frac{3955}{12}t^2 + \frac{5833}{2}t^3 + \frac{10343}{12}t^4 + \frac{67228}{15}t^5,$$

so the coefficient of $t$ is negative. The proof counts the integer points through their residues modulo $14^5 = 537824$, which reduces the count to the distribution of one integer-valued height over those residues. Solus's real-rootedness theorem is unaffected, and other values of $r$ and $d$ are not settled here.

Checked in Lean from the definitions; not yet reviewed by experts.

The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

## Check it

Install Lean using [elan](https://github.com/leanprover/elan). A network connection is needed to obtain the pinned dependencies and their compiled cache. After the cache is downloaded, the build takes roughly five minutes on two cores and needs about 6 GB of memory, most of it for the finite height count.

```sh
cd lean
lake exe cache get
lake build
```

The build checks the theorem, its statement, small consistency checks and its axioms. Dependency details and the correspondence with the paper are in [lean/README.md](lean/README.md).

## Credits

Liam Solus defined the base-r simplices in [Simplices for numeral systems](https://arxiv.org/abs/1706.00480v2) and observed that computations suggested they are Ehrhart positive. Fu Liu stated this as Solus's conjecture in the survey [On positivity of Ehrhart polynomials](https://arxiv.org/abs/1711.09962v2), and Liu and Solus restated it in [On the relationship between Ehrhart unimodality and Ehrhart positivity](https://arxiv.org/abs/1804.08258v1). This result answers their question, and it uses their definitions and the relation between the Ehrhart polynomial and the $h^\ast$-vector recalled in Liu's survey.

The counting argument is the standard decomposition of the lattice points of a simplex by residues modulo its normalized volume, combined with stars and bars. Lean and Mathlib provide the formal proof infrastructure. [Further credits](checks/README.md) list recent work on related families of simplices.

Apache-2.0 (see the repository's LICENSE).

## Cite

```bibtex
@misc{GrahamBaseREhrhart2026,
  author = {Graham, P.},
  title = {{A base-r simplex that is not Ehrhart positive}},
  year = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/base-r-ehrhart-v1/results/base-r-ehrhart}}
}
```
