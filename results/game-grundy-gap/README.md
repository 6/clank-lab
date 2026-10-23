# Greedy play can require more colors in the coloring game

[![Checks](https://github.com/6/clank-lab/actions/workflows/game-grundy-gap.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/game-grundy-gap.yml)

In the [graph coloring game](https://en.wikipedia.org/wiki/Game_chromatic_number), Alice and Bob take turns coloring a vertex, keeping adjacent vertices different. Alice wants the whole graph colored; Bob wants to prevent this. The game chromatic number is the smallest palette with which Alice can win. In the greedy game, each player chooses a vertex and must use its smallest available positive color; Alice minimizes the number of colors and Bob maximizes it. Havet and Zhu asked in [June 2011, Problem 5](https://inria.hal.science/inria-00600738v1/document), whether greedy play always needs at most the game chromatic number. [Hollom's Question 3.4](https://arxiv.org/abs/2308.03528v2) restates this question and explains an obstacle to transferring strategies between the games. We answer its first part negatively with a graph satisfying

$$
\chi_g(G) \leq 5 < \Gamma_g(G).
$$

This answers only the first part of Havet and Zhu's question. Whether the gap can be arbitrarily large remains open.

Computer-assisted; not yet reviewed by experts.

The proofs, the search code, the certificate checkers and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

<img src="data/graph.svg" width="830" alt="The counterexample graph, with vertices labeled 0 through 10.">

## Check it

Python 3.10 or later is sufficient; [requirements.txt](requirements.txt) lists the requirements. From this folder, run:

```sh
python3 -I checks/verify.py
```

The command checks both strategy certificates with two independent implementations, requires both to reject the corruption tests, and checks that the figures match the graph. It needs only this folder and Python's standard library. The [checker documentation](checks/README.md) explains the certificate format and the proof obligations.

## Credits

Frédéric Havet and Xuding Zhu introduced the game Grundy number and posed the question. Their examples provided checks of the game rules. Lawrence Hollom restated the question and supplied the ordered-game obstruction and another calibration example. The graph here gives a counterexample when both players may choose any uncolored vertex, starting with Alice and without passes.

Tomasz Krawczyk and Bartosz Walczak [answered a different question in 2015](https://arxiv.org/abs/1503.04748): the game chromatic number cannot be bounded by a function of the static Grundy number, and consequently cannot be bounded by the game Grundy number. That reverse comparison is distinct from the inequality addressed here.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamGameGrundyGap2026,
  author       = {Graham, P.},
  title        = {{Greedy play can require more colors in the coloring game}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/game-grundy-gap-v1/results/game-grundy-gap}}
}
```
