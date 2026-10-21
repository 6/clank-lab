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

We show the conjecture is false. A counterexample at the smallest possible
size, $n = 5$, is $\lambda = (3,1,1)$ with $k = 3$, whose Smith form is $(1,1,1,1,2,2)$ instead
of the predicted $(1,1,1,1,1,4)$. It comes from the identity

$$X_3\,\bigl(X_3 - (1\,2)\bigr) = 2$$

in the group ring, which forces every invariant factor of $X_3$ to be 1 or 2,
while the conjecture predicts a 4 whenever $\lambda$ has at least three rows
and three columns. So for $k = 3$ it holds exactly when $\lambda$ has at most
two rows or at most two columns; this classification is proved in writing
(not machine-checked). Stanley's weaker remark, that every invariant factor
is a product of eigenvalues, fails too: for $\lambda = (5,2)$ and $k = 7$ the
eigenvalues are only 0 and 4, but the Smith form
$(1,1,1,1,2,4,4,4,4,0,0,0,0,0)$ contains a 2.

Lean checks the identity, both counterexamples' Smith forms and two steps of
the general argument; independent programs confirm the matrices. The rest is
a written proof.

Written proof, with Lean and computer checks; not yet reviewed by experts.

The proofs, the Lean formalization, the certificate checkers and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

## Check it

Both counterexamples are verified by Lean proofs and executable checkers:
Lean checks the identity, the Smith forms of the two matrices and the
eigenvalues of the second, and two independent programs check that the
matrices represent $X_k$ on the integral Specht modules. Lean also checks two steps of the general argument: that any
diagonalization of an integer matrix $A$ with $AB = 2I$ by unimodular matrices
has entries $\pm 1$ or $\pm 2$, with as many even entries as the power of 2 in
$\det A$, and the final count. The rest is proved in writing (not
machine-checked).

Python 3.10 or later, with no third-party packages, checks the certificates
in a few seconds:

```sh
python3 checks/check.py
```

Both checkers must accept the witnesses for $\lambda = (3,1,1)$, $k = 3$ and
$\lambda = (5,2)$, $k = 7$, including the weak-form claim for the second (its
eigenvalues are only 0 and 4, but its Smith form has a 2), and reject three
controls and eight corrupted certificates. Stanley reports computations
through $n \le 7$; the modifications of the formula we tested, against every
case with $n \le 8$, all fail. A third checker recomputes every case with $n \le 5$ and
confirms that the conjecture holds for $n \le 4$ and fails at $n = 5$ only for
$\lambda = (3,1,1)$, with $k = 3$ and $k = 5$. [Checker documentation](checks/README.md) describes the
certificate format and what each checker proves; the optional programs that
computed every case with $n \le 8$ are described there too.

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
in combinatorics. Stanley reports computations through $n \le 7$ by Darij Grinberg as its basis, and
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
  howpublished = {\url{https://github.com/6/clank-lab/tree/stanley-smith-forms-v2/results/stanley-smith-forms}}
}
```
