# A counterexample to Stanley's conjecture on Smith forms of Jucys–Murphy elements

[![Checks](https://github.com/6/clank-lab/actions/workflows/stanley-smith-forms.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/stanley-smith-forms.yml)

The [Jucys–Murphy elements](https://en.wikipedia.org/wiki/Jucys%E2%80%93Murphy_element)
$X_k = (1\,k) + (2\,k) + \cdots + (k{-}1\,k)$ act on each integral
[Specht module](https://en.wikipedia.org/wiki/Specht_module) $S^\lambda$ of the
symmetric group, with eigenvalues given by the contents of standard Young
tableaux. In his 2016 survey
[Smith normal form in combinatorics](https://arxiv.org/abs/1602.00166)
(Conjecture 7.4), Richard P. Stanley conjectured a formula for their Smith
normal forms, based on Darij Grinberg's computations. Grinberg later
clarified the intended lattice in reply to Alexander Chervov's
[MathOverflow question](https://mathoverflow.net/questions/484782) about the
conjecture's status.

We show the conjecture is false. The identity

$$X_3\,\bigl(X_3 - (1\,2)\bigr) = 2$$

in the group ring forces every invariant factor of $X_3$ to be 1 or 2, while
the conjecture predicts a 4 whenever $\lambda$ has at least three rows and
three columns. So for $k = 3$ it holds exactly when $\lambda$ has at most two
rows or at most two columns. The smallest counterexample is
$\lambda = (3,1,1)$, whose Smith form is $(1,1,1,1,2,2)$ instead of the
predicted $(1,1,1,1,1,4)$.

Lean checks the identity and the Smith form of the $(3,1,1)$ matrix. The rest
is a written proof, and independent programs confirm the matrix.

Computer-assisted; not yet reviewed by experts.

The proofs, the Lean formalization, the certificate checkers and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23541470](https://doi.org/10.5281/zenodo.23541470)

## Check it

Python 3.10 or later, with no third-party packages, checks the certificates
in a few seconds:

```sh
python3 checks/check.py
```

Both checkers must accept the witnesses for λ = (3,1,1), k = 3 and
λ = (5,2), k = 7, and reject an agreeing control and seven corrupted
certificates. Grinberg's original computations covered n ≤ 7; natural corrected readings of the formula, tested against every case with n ≤ 8, all fail. A third checker recomputes every case with n ≤ 5 and
confirms that the conjecture holds for n ≤ 4 and fails at n = 5 only for
λ = (3,1,1), with k = 3 and k = 5. [Checker documentation](checks/README.md) describes the
certificate format and what each checker proves; the optional programs that
computed every case with n ≤ 8 are described there too.

Install [elan](https://github.com/leanprover/elan), then check the Lean
proof, which takes a few minutes once the Mathlib cache is downloaded:

```sh
cd lean
lake exe cache get
lake build
```

[Lean documentation](lean/README.md) explains the formal statement.

## Credits

Richard P. Stanley posed the conjecture in his survey of Smith normal forms
in combinatorics. Darij Grinberg's computations for n ≤ 7 underlie it, and
his MathOverflow comment fixed the lattice on which it is to be read.
Alexander Chervov asked on MathOverflow for its status. Lean, Mathlib and
their contributors supplied the formal-proof infrastructure.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamStanleySmithForms2026,
  author       = {Graham, P.},
  title        = {{A counterexample to Stanley's conjecture on Smith forms of Jucys--Murphy elements}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/stanley-smith-forms-v1/results/stanley-smith-forms}},
  doi          = {10.5281/zenodo.23541470}
}
```
