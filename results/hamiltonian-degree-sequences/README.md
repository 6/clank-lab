# Counterexamples to the conjectured characterization of Hamiltonian degree sequences in digraphs

[![Checks](https://github.com/6/clank-lab/actions/workflows/hamiltonian-degree-sequences.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/hamiltonian-degree-sequences.yml)

A [Hamilton cycle](https://en.wikipedia.org/wiki/Hamiltonian_path) visits every vertex exactly once. [Chvátal's theorem](https://mathworld.wolfram.com/ChvatalsTheorem.html) (1972) says exactly which degree sequences of graphs force one. For [directed graphs](https://en.wikipedia.org/wiki/Directed_graph), whose out-degrees and in-degrees are sorted separately, Nash-Williams conjectured in 1975 that a strongly connected digraph satisfying two Chvátal-type conditions is Hamiltonian. In 2008 Kühn, Osthus and Treglown replaced strong connectivity by a third condition for even orders and conjectured that the three conditions force a Hamilton cycle; if true, this would have characterized the digraph degree sequences that force Hamiltonicity. Georgi Guninski found 6-vertex counterexamples to Nash-Williams' conjecture on MathOverflow in [2013](https://mathoverflow.net/questions/124217) and [2020](https://mathoverflow.net/questions/369168); the 2013 example was confirmed there by Gordon Royle and Hugh Thomas, and the 2020 ones by Louis DeBiasio. All of them violate the third condition. This work shows that the conjecture of Kühn, Osthus and Treglown is false for every number of vertices $n \ge 7$, with an explicit 7-vertex digraph and an explicit family, and true for every $n$ from 3 to 6.

Consequently Nash-Williams' conjecture is false for every $n \ge 7$, as well as for Guninski's $n = 6$, and the same search shows it is true for $n$ from 3 to 5. The family also shows that for every $n \ge 8$ the conditions of either conjecture do not even force a cycle through every pair of vertices, a question Kühn, Osthus and Treglown recorded as open.

Computer-assisted; not yet reviewed by experts.

The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23966080](https://doi.org/10.5281/zenodo.23966080)

## Check it

The counterexamples are in `data/` and in the Lean files. With Python 3.10 or later and a C compiler, run from this folder:

```sh
python3 checks/verify.py
python3 checks/verify.py --n6
```

The first command checks the counterexamples with two independent programs, confirms that both reject altered inputs, and searches all digraphs on at most five vertices, in a few seconds. The second adds the exhaustive search on six vertices, about four minutes on one core. The [checks notes](checks/README.md) describe each program.

The Lean proof of the counterexamples needs [elan](https://github.com/leanprover/elan):

```sh
cd lean
lake exe cache get
lake build
```

The first command downloads the mathematical library's compiled cache. Allow several minutes for it, then about two minutes and 9 GB of memory for the build, which also checks the statements and their axioms. The [Lean notes](lean/README.md) list the definitions and theorems.

## Credits

Daniela Kühn, Deryk Osthus and Andrew Treglown posed the conjecture refuted here, in *Hamiltonian degree sequences in digraphs*, as a characterization of the degree sequences forcing Hamiltonicity; Crispin Nash-Williams posed the original conjecture in 1975. Georgi Guninski found the first counterexamples to Nash-Williams' conjecture, on six vertices, in MathOverflow questions 124217 and 369168; the case $n = 6$ of that conjecture is Guninski's. Gordon Royle and Hugh Thomas confirmed the 2013 example, and Louis DeBiasio analyzed it, verified the 2020 examples and discussed larger ones. The 6-vertex example used here is isomorphic to Guninski's 2020 example $g_2$.

The counterexamples for seven or more vertices, the proofs and the exhaustive search for six or fewer vertices are new here. Lean and the Mathlib library check the counterexamples, and two independent programs in Python and C check them again and run the search. The [checks notes](checks/README.md) list further credits and nearby work.

Apache-2.0 (see the repository's LICENSE).

## Cite

```bibtex
@misc{GrahamHamiltonianDegreeSequences2026,
  author = {Graham, P.},
  title = {{Counterexamples to the conjectured characterization of Hamiltonian degree sequences in digraphs}},
  year = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/hamiltonian-degree-sequences-v1/results/hamiltonian-degree-sequences}},
  doi          = {10.5281/zenodo.23966080}
}
```
