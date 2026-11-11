# The Heawood family is not the complete list of excluded minors for 4-flat graphs

[![Checks](https://github.com/6/clank-lab/actions/workflows/heawood-family-four-flat.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/heawood-family-four-flat.yml)

A graph is 4-flat if attaching a separate disk along each simple cycle produces a complex that embeds piecewise linearly in four-dimensional Euclidean space. The [Heawood family](https://en.wikipedia.org/wiki/Heawood_family) consists of 78 graphs obtained from two small graphs by triangle-to-star and star-to-triangle moves. The completeness question asks whether a graph is 4-flat precisely when none of these 78 graphs can be obtained by deleting or contracting edges and deleting vertices. [Georgakopoulos and Winter](https://arxiv.org/abs/2408.12681v1) stated this as the second clause of Conjecture 1.1 in 2024, explaining that it follows implicitly from two conjectures of van der Holst (2006). They proved the first clause, that every family member is an excluded minor.

We disprove the completeness clause. A known graph $H$, with 11 vertices and 22 edges, is not 4-flat and has no Heawood-family minor. An explicit mod-two obstruction proves the first statement; exhaustive minor checks prove the second. Earlier work shows that every proper minor of $H$ is 2-apex, and Georgakopoulos–Winter show that every 2-apex graph is 4-flat. Thus $H$ itself is a new excluded minor. Its exact Colin de Verdière invariant remains undetermined here.

Computer-assisted; not yet reviewed by experts.

The proofs, the computer checks and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

## Check it

With Python 3.12 or later and GNU `time` and `timeout`, run from this folder:

```sh
python3 -m pip install --require-hashes -r checks/requirements.txt
sh checks/check.sh
```

The check takes about 15 seconds on one core, with a peak memory use of about 155 MiB. It ends with `PASS: H is not 4-flat and has no Heawood-family minor.` It runs two separately written obstruction checkers, positive, boundary-corruption and even-invariant controls, two minor-exclusion checks, an exact check of the printed certificate appendix, and direct comparisons of $H$ and its 44 single-edge minors. It also finds two vertices whose deletion makes each of those minors planar. The [checker documentation](checks/README.md) explains the mathematical inputs, the exact data and the reproducibility options.

The minor checks fetch five files from the immutable tagged release of [the preceding result, heawood-family-mu5 v1](https://doi.org/10.5281/zenodo.24128771), checking their SHA-256 hashes before use. That result concerns the Colin de Verdière invariant. This is a separate result about 4-flatness, using a new obstruction certificate for $H$.

## Credits

Hein van der Holst introduced 4-flatness, proved that all Heawood-family graphs are non-4-flat and that the two seed graphs are excluded minors, and posed the conjectures whose combination implies completeness. Hein van der Holst and Rudi Pendavingh developed the deleted-product obstruction used here, in *On a graph property generalizing planarity and flatness* (Combinatorica, 2009). We use Lemma 12 and Theorem 18 with the numbering of their author manuscript dated April 26, 2008. Agelos Georgakopoulos and Martin Winter supplied the full cycle-complex formulation and proved that all 78 Heawood-family graphs really are excluded minors; their theorem is unaffected by this counterexample. Their Theorem 5.9(ii) supplies the 2-apex implication used to deduce minimality. The intersection obstruction goes back to van Kampen; Matoušek, Tancer and Wagner describe its moment-curve evaluation in [Appendix D](https://doi.org/10.4171/JEMS/252). Kaluža and Tancer give the cellular certificate method and the explicit crossing/invariant identity in [Appendix B of arXiv:1907.05055v2](https://arxiv.org/abs/1907.05055v2). The new contribution is the certificate for this graph.

Thomas Mattman and Mike Pierce had already found $H$ by computer search among minor-minimal non-2-apex graphs in 2017. The present public check rechecks the proper-minor property. Hyoungjun Kim and Thomas Mattman named it $H_2$ and related it to their graph $G_2$ in 2025. Thomas Mattman and Andrei Pavelescu's 2026 catalog supplies the labeling of that larger graph used here. We claim neither the discovery of $H$ nor these earlier structural facts. The [preceding result](https://doi.org/10.5281/zenodo.24128771) supplies the published minor-exclusion programs. NetworkX supplies graph representations and isomorphism tests. Exact [model and role credits](checks/README.md#model-and-role-credits) distinguish the builders and readers.

Apache-2.0 (see the repository's LICENSE).

## Cite

```bibtex
@misc{GrahamHeawoodFamilyFourFlat2026,
  author = {Graham, P.},
  title = {{The Heawood family is not the complete list of excluded minors for 4-flat graphs}},
  year = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/heawood-family-four-flat-v1/results/heawood-family-four-flat}}
}
```
