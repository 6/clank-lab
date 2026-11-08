# A four-dimensional 4-reptile simplex

[![Checks](https://github.com/6/clank-lab/actions/workflows/reptile-simplex.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/reptile-simplex.yml)

A [rep-tile](https://en.wikipedia.org/wiki/Rep-tile) is a shape that can be cut into several congruent pieces, each a smaller copy of the whole; a [simplex](https://en.wikipedia.org/wiki/Simplex) with this property, cut into $k$ pieces, is a $k$-reptile. In the plane there are many: a right isosceles triangle splits into two half-size copies of itself. In dimension $d \ge 3$ the known examples all used $k = m^d$ pieces, like cutting a cube into $m^d$ small cubes. Jiří Matoušek and Zuzana Safernová conjectured in 2010 that this is forced for every $d \ge 3$, and proved it for $d = 3$. Jan Kynčl and Zuzana Patáková proved in 2016 that in dimension four $k$ must be a perfect square, and asked whether a four-dimensional $m^2$-reptile simplex exists for $m$ not a square ([Problem 2 of arXiv:1602.04668](https://arxiv.org/abs/1602.04668); Problem 1.4 of the published version). We show that the simplex with vertices $(0,0,0,0)$, $(1,0,0,0)$, $(1/2,1/2,0,0)$, $(2/3,1/3,1/3,0)$ and $(3/4,1/4,1/4,1/4)$ is a 4-reptile: it is tiled by four congruent copies of itself scaled by $1/\sqrt{2}$, two of them mirror images. This answers their question with $m = 2$ and disproves the conjecture in dimension four. The simplex is the fundamental alcove of the [affine Weyl group](https://en.wikipedia.org/wiki/Affine_Weyl_group) of type [F4](https://en.wikipedia.org/wiki/F4_(mathematics)), and the subdivision is due to Anna Felikson and Pavel Tumarkin (2004), in their work on reflection subgroups of Euclidean reflection groups; what is new here is the observation that it answers the reptile question, with a short direct proof. As a corollary, the same simplex is a $4^a m^4$-reptile for all $a \ge 0$ and $m \ge 1$.

Computer-assisted; not yet reviewed by experts.

The proofs, the computer checks and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.24061700](https://doi.org/10.5281/zenodo.24061700)

## Check it

The paper's proof is written out by hand in its Section 2. The file `data/certificate.json` lists the simplex, the scaling map and the four pieces, each with the orthogonal matrix and translation that carry the simplex onto it. Three programs check in exact rational arithmetic that the pieces are congruent copies of the simplex, lie inside its $\sqrt{2}$-scaled copy, have disjoint interiors and fill it by volume; the third also checks that each piece is an alcove of the $F_4$ arrangement. With Python 3.8 or later and no other packages, from this folder:

```sh
sh checks/check.sh
```

It takes under a second and ends with `PASS: 3 checkers accept the certificate and reject all 6 corruptions`. The [checker documentation](checks/README.md) describes each program, the certificate format and the six corrupted certificates the programs must reject.

## Credits

Jiří Matoušek and Zuzana Safernová stated the conjecture in *On the nonexistence of k-reptile tetrahedra* (Discrete & Computational Geometry, 2011) and proved its three-dimensional case. Jan Kynčl and Zuzana Patáková posed the question answered here in *On the nonexistence of k-reptile simplices in* $\mathbb{R}^3$ *and* $\mathbb{R}^4$ (Electronic Journal of Combinatorics, 2017), where they proved that four-dimensional $k$-reptile simplices need $k$ to be a square; the definitions used here are theirs. The subdivision itself is Lemma 10 of Anna Felikson and Pavel Tumarkin's *Reflection subgroups of Euclidean reflection groups* (Sbornik: Mathematics, 2005), whose case of type F4 gives a simplex similar to the alcove and made of four alcoves. This work's contribution is the observation that their lemma settles the reptile question, with an explicit tiling and a direct proof.

The coordinates of the $F_4$ root system are Bourbaki's. The checkers are plain Python with exact rational arithmetic. [Further credits](checks/README.md#further-credits) give the exact references.

Apache-2.0 (see the repository's LICENSE).

## Cite

```bibtex
@misc{GrahamReptileSimplex2026,
  author = {Graham, P.},
  title = {{A four-dimensional 4-reptile simplex}},
  year = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/reptile-simplex-v1/results/reptile-simplex}},
  doi          = {10.5281/zenodo.24061700}
}
```
