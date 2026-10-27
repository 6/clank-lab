# Relations among cycle invariants of a three-armed quiver

[![Checks](https://github.com/6/clank-lab/actions/workflows/makonzi-invariants.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/makonzi-invariants.yml)

Brian Makonzi's [Conjecture 5.2](https://doi.org/10.1093/qmath/haaf044) asks whether three determinants give every relation among specified cycle polynomials of a three-arm quiver. We prove the kernel equality for every triple of arm lengths at least two over the complex numbers. Makonzi's Lemma 4.1, Proposition 4.2, Lemma 4.3 and Proposition 5.1 supply the generation theorem; together these give Makonzi’s proposed presentation of the invariant ring. The proof reduces polynomials to pure powers and distinguishes them in a rational function field.

![Three doubled paths with common endpoints](data/quiver.svg)

Each pair of curves abbreviates a path of $p_i$ edges and its reverse, with the intermediate vertices suppressed. The labels are products along entire paths.

Checked in Lean from the definitions; not yet reviewed by experts.

The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23705764](https://doi.org/10.5281/zenodo.23705764)

## Check it

Install [elan](https://github.com/leanprover/elan), Git and a C toolchain. From this folder:

```sh
cd lean
lake exe cache get
lake build
```

Elan installs the pinned Lean version. Lake downloads Mathlib and checks the complete kernel equality, its statement, and its axiom guards. Allow a few minutes after downloading dependencies. The [checking guide](lean/README.md) explains the definitions and what remains in Makonzi's source.

## Credits

Brian Makonzi posed the conjecture, specified its generators and matrix, and proved generation through Lemma 4.1, Proposition 4.2, Lemma 4.3 and Proposition 5.1, which also proves vanishing of the minors. Makonzi’s [type-A work](https://doi.org/10.4171/jncg/552) and [Iyama and Wemyss's reconstruction-algebra setting](https://doi.org/10.46298/epiga.2020.volume3.4761) are related antecedents. Wemyss's original [type-A reconstruction algebra](https://arxiv.org/abs/0704.3693v4) supplies the earlier reconstruction-algebra context. [Bruns and Vetter](https://doi.org/10.1007/BFb0080378) give the conditional Hilbert–Burch and Eagon–Northcott machinery for maximal-minor ideals, and [Wahl](https://doi.org/10.24033/asens.1326) treats determinantal rational surface equations and their exceptional curves. Those contextual theorems are not premises of our direct normal-form proof. The free coefficient-ring module in Corollary 6 also gives a flat family; this is a written consequence. The formal proof uses Lean and Mathlib.

Alastair Craw and Ryo Yamagishi’s [*The Le Bruyn–Procesi theorem following Lusztig*](https://arxiv.org/abs/2312.08527v4), Theorems 1.1 and 4.3, describe trace generators and the relation ideal in the invariant ring of an unconstrained quiver. Our explicit three-relation presentation uses Makonzi’s specified polynomial generators. The bounded comparison read the introduction and §§3–4 of v4 (November 14, 2025); no general no-overlap claim is inferred.

Makonzi’s account credits Claus Michael Ringel’s [*Tame algebras and integral quadratic forms*](https://doi.org/10.1007/BFb0072870) for canonical-algebra lineage and Jan Stevens’s [*Deformations of singularities*](https://doi.org/10.1007/b10723), §12, for the minor format. These books were not read here. Makonzi’s related thesis, *Computing the Artin component using Reconstruction Algebras*, was located as an institutional record; its full text was not obtained. Andrzej Skowroński and Jerzy Weyman’s [*Semi-invariants of canonical algebras*](https://doi.org/10.1007/s002290050208) is related older background, consulted only through a review.

Oswald Riemenschneider’s *Special surface singularities: A survey on the geometry and combinatorics of their deformations* supplies broader surface-deformation context; only selected §8 and bibliography passages were read. Makonzi also cites Riemenschneider’s *Deformations of rational singularities and their resolutions* and *Cyclic quotients surface singularities: constructing the Artin Component via the McKay-Quiver* for cyclic-surface history. Those two originals were not read, and no theorem from them is used in our proof.

Related classical sources are G. N. Tjurina’s [*Absolute isolatedness of rational singularities and triple rational points*](https://doi.org/10.1007/BF01075685) and J. A. Eagon and D. G. Northcott’s [*Ideals defined by matrices and a certain complex associated with them*](https://doi.org/10.1098/rspa.1962.0170). These identities were checked in publisher-deposited metadata; the article bodies were not read. We invoke no classification theorem from Tjurina’s article, and cite the conditional determinantal methods through Bruns and Vetter.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamMakonziInvariants2026,
  author       = {Graham, P.},
  title        = {{Relations among cycle invariants of a three-armed quiver}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/makonzi-invariants-v1/results/makonzi-invariants}},
  doi          = {10.5281/zenodo.23705764}
}
```
