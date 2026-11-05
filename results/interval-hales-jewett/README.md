# A quadratic lower bound for intervals in the Hales–Jewett theorem

[![Checks](https://github.com/6/clank-lab/actions/workflows/interval-hales-jewett.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/interval-hales-jewett.yml)

The [Hales–Jewett theorem](https://en.wikipedia.org/wiki/Hales%E2%80%93Jewett_theorem), a cornerstone of [Ramsey theory](https://en.wikipedia.org/wiki/Ramsey_theory), says that if the words of length $n$ over an alphabet of $m$ letters are colored with $r$ colors and $n$ is large enough, then some combinatorial line is monochromatic: $m$ words that agree outside a nonempty set of wildcard positions and repeat one letter on all of them. Shelah's proof finds such a line whose wildcard set is a union of few intervals. For three letters, David Conlon and Nina Kamčev (2018), Imre Leader and Eero Räty (2018), and Nina Kamčev and Christoph Spiegel (2022) determined exactly how many intervals are needed. For four or more letters, Conlon and Kamčev asked whether some coloring forces more than $cr$ intervals, for some $c > 1$; Kamčev and Spiegel noted that $r - 1$ intervals was the best explicit lower bound the known methods give, and Younes Mouhib's 2026 master's thesis records the case of four or more letters as open. We show that the number of intervals needed grows at least quadratically with the alphabet. For every $Q \ge 1$ and every $m \ge 2\lceil\sqrt{32Q}\rceil + 2$ there is, for every $n$, a 2-coloring of the words of length $n$ over $m$ letters with no monochromatic line whose wildcard set is a union of at most $Q$ intervals. The coloring is the parity of $\lfloor S/(32Q) \rfloor$, where $S$ is the sum of the squared differences of consecutive letters, with a letter 0 placed before the first.

As a corollary, the least number of intervals that every 2-coloring must allow, for long enough words over $m$ letters, exceeds $(m-3)^2/128$. With 18 letters and two colors no monochromatic line has a wildcard set made of one or two intervals, which answers Conlon and Kamčev's question with $c$ between 1 and 3/2.

Checked in Lean from the definitions; not yet reviewed by experts.

The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

## Check it

Install Lean using [elan](https://github.com/leanprover/elan). A network connection is needed to download Mathlib and its compiled cache, about 5 GB. Allow a few minutes for the download and under a minute for the build, with about 2 GB of memory.

```sh
cd lean
lake exe cache get
lake build
```

The build checks the main theorem and its consequence for every alphabet size, restates both with their full types, checks small examples of the definitions and checks the axioms used. [Lean details](lean/README.md) give the dependency pins and how the formal statements match the paper.

## Credits

David Conlon and Nina Kamčev posed the question, as Question 3.1 of the 2018 arXiv version of *Intervals in the Hales–Jewett theorem* (published in the European Journal of Combinatorics, 2026), after proving that for odd $r$ some $r$-colorings of words over three letters have no monochromatic line whose wildcard set is a union of fewer than $r$ intervals. Imre Leader and Eero Räty showed that with two colors and three letters one interval always suffices, and Nina Kamčev and Christoph Spiegel, in *Another note on intervals in the Hales–Jewett theorem* (Electronic Journal of Combinatorics, 2022), settled every even number of colors, named the quantity bounded here and asked, as their Question 19, whether its immediate bounds can be improved.

Younes Mouhib's 2026 papers and master's thesis, *Improving bounds on Hales–Jewett numbers* (ETH Zürich; Question 4.21), record that nothing beyond upper bounds was known for four or more letters, and prove that colorings invariant under permuting positions cannot give a lower bound; the coloring here depends on adjacent letters. The proof is formalized with Lean 4 and Mathlib. [Further credits and source notes](checks/README.md) give the exact references.

Apache-2.0 (see the repository's LICENSE).

## Cite

```bibtex
@misc{GrahamIntervalHalesJewett2026,
  author = {Graham, P.},
  title = {{A quadratic lower bound for intervals in the Hales--Jewett theorem}},
  year = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/interval-hales-jewett-v1/results/interval-hales-jewett}}
}
```
