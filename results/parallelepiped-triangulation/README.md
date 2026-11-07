# A lattice parallelepiped with no unimodular triangulation

[![Checks](https://github.com/6/clank-lab/actions/workflows/parallelepiped-triangulation.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/parallelepiped-triangulation.yml)

A lattice polytope has a unimodular [triangulation](https://en.wikipedia.org/wiki/Triangulation_(geometry)) if it can be cut into simplices with integer vertices and the smallest possible volume. Christian Haase, Andreas Paffenholz, Lindsay C. Piechnik and Francisco Santos asked, in Section 1.5.4 of their [survey of unimodular triangulations](https://arxiv.org/abs/1405.1687v3) (third arXiv version, December 11, 2017), whether all lattice [parallelepipeds](https://en.wikipedia.org/wiki/Parallelepiped) and, more generally, all lattice [zonotopes](https://en.wikipedia.org/wiki/Zonotope) have one. Giulia Codenotti and Francisco Santos had shown that every 3-dimensional lattice parallelepiped can at least be covered by such simplices, and asked whether it can be triangulated by them. We show that the answer to the survey's question is no in every dimension from 4 on. The 4-dimensional parallelepiped spanned by the three unit vectors $`e_1, e_2, e_3`$ and the vector $(1,2,3,5)$ has no unimodular triangulation, and its products with unit cubes give examples in all higher dimensions. It is the parallelepiped of a cone that Robert T. Firla and Günter M. Ziegler showed cannot be triangulated into unimodular cones using only its Hilbert basis.

The main theorem and its extension to all higher dimensions have written proofs that need no computer: a chain of faces that any unimodular triangulation would be forced to contain ends at a point that no face can contain. A short program also rechecks the finite steps of that proof. The further results are computer-assisted, resting on certificates checked by programs: this parallelepiped can be covered by unimodular simplices, the cone at each of its corners can be triangulated unimodularly, and up to lattice equivalence it is the unique 4-dimensional lattice parallelepiped of determinant at most 5 without a unimodular triangulation; the paper lists the exceptions up to determinant 8. The question in dimension 3 stays open.

Computer-assisted; not yet reviewed by experts.

The proofs, the checking programs and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23990077](https://doi.org/10.5281/zenodo.23990077)

## Check it

The checks need Python 3.12 or newer, numpy and scipy, and a C++ compiler. From this directory, run:

```sh
python3 -m pip install --require-hashes -r checks/requirements.txt
python3 -I checks/check.py
```

This takes about half an hour on an ordinary computer. It checks every finite statement of the hand proof against the tables in the paper's source, and the certificates of the other results with two separately written checkers where the paper says so, and confirms that the checkers reject deliberately corrupted inputs. The [checking notes](checks/README.md) describe the programs and the data.

## Credits

Christian Haase, Andreas Paffenholz, Lindsay C. Piechnik and Francisco Santos posed the question, and their survey frames the hierarchy of properties the result separates; Luis Ferroni and Akihiro Higashitani restated it in their survey of Ehrhart theory. The work this result builds on most is the cone of Robert T. Firla and Günter M. Ziegler (Example 8 of their 1999 paper), whose parallelepiped is our example and which they present as a simplification of the earlier cone of Catherine Bouvier and Gérard Gonzalez-Sprinberg, and the work of Giulia Codenotti and Francisco Santos on unimodular covers of 3-dimensional parallelepipeds, with its questions on dimension 3 and on covers. The parallelepiped of the Bouvier–Gonzalez-Sprinberg cone is the exception of determinant 7.

Winfried Bruns, Joseph Gubeladze and Ngô Viêt Trung built a normal 4-dimensional lattice polytope without a unimodular triangulation from the Bouvier–Gonzalez-Sprinberg cone (1997), and Bruns and Gubeladze showed that the hierarchy's implications are strict, so normal polytopes without unimodular triangulations were known before. The searches used the SAT solver CaDiCaL of Armin Biere and coauthors, and the checks use numpy and scipy. [Further credits](checks/README.md#further-credits) list the other work cited.

Apache-2.0 (see the repository's LICENSE).

## Cite

```bibtex
@misc{GrahamParallelepipedTriangulation2026,
  author = {Graham, P.},
  title = {{A lattice parallelepiped with no unimodular triangulation}},
  year = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/parallelepiped-triangulation-v1/results/parallelepiped-triangulation}},
  doi          = {10.5281/zenodo.23990077}
}
```
