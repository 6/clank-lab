# No post-Lie algebra structures on pairs of perfect and nilpotent Lie algebras

[![Checks](https://github.com/6/clank-lab/actions/workflows/postlie-perfect-nilpotent.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/postlie-perfect-nilpotent.yml)

A [Lie algebra](https://en.wikipedia.org/wiki/Lie_algebra) is a vector space with a bracket operation, such as the commutator $xy - yx$ of square matrices. It is perfect if every element is a sum of brackets, as for the $2 \times 2$ matrices of trace zero, and [nilpotent](https://en.wikipedia.org/wiki/Nilpotent_Lie_algebra) if repeated brackets of enough elements always vanish. A post-Lie algebra structure ties two Lie brackets on the same space together through a third product; such structures arise from affine actions of Lie groups on nilpotent Lie groups. In [2015](https://arxiv.org/abs/1505.00955v1) Dietrich Burde and Karel Dekimpe asked, as their Question 3.5, whether such a structure can exist when the first bracket is perfect and the second nilpotent, having shown that it cannot when the second is abelian or two-step nilpotent. In [2023](https://arxiv.org/abs/2311.08985v1) Burde, Dekimpe and Mina Monadjem conjectured that it never exists when the perfect bracket is moreover not semisimple, and proved this for the two six-dimensional examples. We prove that no such structure exists for any nonzero perfect first bracket, over any field of characteristic zero.

More generally, if the second bracket is nilpotent and every right multiplication of the product has trace zero, the first bracket gives a [solvable](https://en.wikipedia.org/wiki/Solvable_Lie_algebra) Lie algebra. When the second bracket is zero, the product is a [left-symmetric algebra](https://en.wikipedia.org/wiki/Pre-Lie_algebra) and this is a 1979 theorem of Helmstetter; the proof extends Helmstetter's argument.

Written proof, with Lean and computer checks; not yet reviewed by experts.

The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

## Check it

Install [elan](https://github.com/leanprover/elan) and Git. From `lean/`, run:

```sh
lake exe cache get
lake build
```

The first command downloads Mathlib's compiled files. The build then checks the proof, the exact statements, a small example and the axioms used, in about two minutes with under 3 GB of memory. Levi's theorem and Whitehead's first lemma are assumed as two named axioms, quoted from Weibel's textbook; everything else is proved. The [Lean notes](lean/README.md) give the definitions, how they match the paper and where each lemma is proved.

## Credits

Dietrich Burde and Karel Dekimpe posed the question as Question 3.5 of *Post-Lie algebra structures on pairs of Lie algebras* (Journal of Algebra, 2016) and settled two-step nilpotent second brackets. Burde stated the conjecture in a 2023 Oberwolfach report on joint work with Dekimpe, as did Burde, Dekimpe and Mina Monadjem in *Post-Lie algebra structures for perfect Lie algebras* (Communications in Algebra, 2024). The proof rests above all on Helmstetter's *Radical d'une algèbre symétrique à gauche* (Annales de l'Institut Fourier, 1979), which settles abelian second brackets, and extends its Levi-factor argument, in the form Daniel J. F. Fox gives in Lemma 5.3 of *Left-symmetric algebras and homogeneous improper affine spheres*, to nilpotent ones.

The embedding into the holomorph is Proposition 2.13 of Burde, Dekimpe and Kim Vercammen's *Affine actions on Lie groups and post-Lie algebra structures*. The determinant step follows the method of Alec Kriebel's preprint *Post-Lie nonexistence with a semisimple target* (2026), after Oliver Baues's relative invariant of étale affine representations. Marco Damele and Andrea Loi's work on Lie skew braces, Nigel Byott's solubility theorem for finite skew braces and Damele's recent extension of it are the group-level analogues. Levi's theorem and Whitehead's first lemma are cited from Charles A. Weibel's textbook. The formalization uses Lean 4 and Mathlib.

Apache-2.0 (see the repository's LICENSE).

## Cite

```bibtex
@misc{GrahamPostliePerfectNilpotent2026,
  author = {Graham, P.},
  title = {{No post-Lie algebra structures on pairs of perfect and nilpotent Lie algebras}},
  year = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/postlie-perfect-nilpotent-v1/results/postlie-perfect-nilpotent}}
}
```
