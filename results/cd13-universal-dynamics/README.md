# Faithful local dynamics on every finite acyclic graph

[![Checks](https://github.com/6/clank-lab/actions/workflows/cd13-universal-dynamics.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/cd13-universal-dynamics.yml)

A [directed acyclic graph](https://en.wikipedia.org/wiki/Directed_acyclic_graph) describes a network with no directed feedback loops. Updating one site uses the states at its outgoing neighbors, without reading its own state. Elena Collina and Alessandro D'Andrea asked in [2013](https://arxiv.org/abs/1311.3460) whether the graph's Hecke–Kiselman monoid describes exactly which update sequences always agree. We prove that it does for every finite acyclic graph, by constructing finite state sets that distinguish every pair of different monoid elements. This answers their question, extending their complete-graph theorem and using Aragona and D'Andrea's cancellation rules.

Checked in Lean from the definitions; not yet reviewed by experts.

The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

## Check it

Install Lean using [elan](https://github.com/leanprover/elan). A network connection is needed to obtain the pinned dependencies and their compiled cache. Allow roughly five minutes after downloading the cache and about 4 GB of memory; download time varies.

```sh
cd lean
lake exe cache get
lake build
```

The build checks the theorem, its statement, elementary boundary cases and its axioms. Dependency details and the correspondence with the paper are in [lean/README.md](lean/README.md).

## Credits

Elena Collina and Alessandro D'Andrea posed the question and proved the complete-graph case. This paper is an answer to their question. Riccardo Aragona and D'Andrea supplied the elementary cancellation rules used to choose reduced words; D'Andrea's later reconstruction question also informs the approach. D'Andrea and Salvatore Stella's recent [cardinality and parity-asymptotic work](https://arxiv.org/abs/2610.14331) concerns the complete-graph Kiselman monoids, whose local faithfulness was already known. Their counting theorem does not cover local faithfulness for arbitrary acyclic graphs.

The proof combines finite constructor terms with the classical trace-projection argument associated with Robert Cori, Dominique Perrin and Christine Duboc. Love Forsberg's effective representations cover earlier special graph classes. Jin, Luo and Zhang's recent [cycle-monoid paper](https://doi.org/10.1007/s00233-026-10687-7) treats directed cycles, outside the acyclic graphs of this theorem. Lean and Mathlib provide the formal proof infrastructure. [Further credits](checks/README.md) give precise references, and list each source not read in full with the reason why, to our knowledge, it does not contain the theorem.

Apache-2.0 (see the repository's LICENSE).

## Cite

```bibtex
@misc{GrahamCd13UniversalDynamics2026,
  author = {Graham, P.},
  title = {{Faithful local dynamics on every finite acyclic graph}},
  year = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/cd13-universal-dynamics-v1/results/cd13-universal-dynamics}}
}
```
