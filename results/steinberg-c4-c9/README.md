# A planar graph with no 4- or 9-cycles that is not 3-colorable

[![Checks](https://github.com/6/clank-lab/actions/workflows/steinberg-c4-c9.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/steinberg-c4-c9.yml)

A [proper three-coloring](https://en.wikipedia.org/wiki/Graph_coloring) assigns three colors to a graph's vertices so that adjacent vertices differ. A question attributed to Lu, Wang, Wang, Bu, Montassier and Raspaud (2009), [as reproduced by Kang, Jin and Wang](https://arxiv.org/pdf/1506.04629), asks which cycle lengths, together with length four, force a planar graph to admit such a coloring. This extends the question behind [Steinberg's conjecture](https://arxiv.org/abs/1604.05108), disproved by Cohen-Addad, Hebdige, Král', Li and Salgado. To our knowledge, the first counterexample to the assertion that every planar graph without four- or nine-cycles has a proper three-coloring is given here: an 82-vertex planar graph without four- or nine-cycles has no proper three-coloring.

Computer-assisted; not yet reviewed by experts.

The proofs, the search code, the certificate checkers and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

## Check it

With Python 3.10 or later, a C compiler and a POSIX shell, check the complete certificate and corruption controls in a few seconds:

```sh
sh checks/check.sh
```

No Python packages are required. [Checker documentation](checks/README.md) explains the inputs, mathematical reductions and independent implementations.

## Credits

The graph is a composition of 27 copies of K4; the paper gives the elementary non-colorability proof and credits Kostochka and Yancey for the sharp edge bound. Lu and coauthors posed the question; Kang, Jin and Wang and Jin, Kang, Liu and Wang recorded and developed it. Cohen-Addad and coauthors supplied the earlier Steinberg disproof. Marijn Heule and Nathan Wetzler's drat-trim checks the SAT certificate, generated with Armin Biere and collaborators' CaDiCaL. The paper distinguishes proper DP/list coloring and defective coloring results of Kang, Jin and Zhu, Dai, Wang and Xu, and Chen, Dai, Nie, Wang and Yu.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamSteinbergC4C92026,
  author       = {Graham, P.},
  title        = {{A planar graph without four- or nine-cycles that is not three-colorable}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/steinberg-c4-c9-v2/results/steinberg-c4-c9}}
}
```
