# Changelog

Each result is versioned on its own and tagged `NAME-vN`. A new version never
replaces an old one: earlier versions stay available through their tags and
Zenodo records.

## density-seven v2 (October 20, 2026)

- Correction: the paper and README now credit Polymath1's 2009 bounds
  1302–1348, recorded by Tao and repeated by O'Bryant, and describe the
  witness as a realization of the known lower bound.
- Zenodo: [10.5281/zenodo.23509560](https://doi.org/10.5281/zenodo.23509560)

## steinberg-c4-c9 v3 (October 20, 2026)

- Adds a Lean proof of the whole result for the published graph: it is
  planar, has no cycle of length 4 or 9, and has no proper 3-coloring, with
  the coloring certificate checked inside Lean.

## uniform-5-polytopes v2 (October 20, 2026)

- Correction: version 1 left out some programs its proof relies on and the
  source of a table its Lean proof uses. Version 2 includes them, and its
  checks now confirm the final counts and that every known polytope is
  matched.
- Correction: two bookkeeping errors in a table; neither affects the result.
- Explains the count of 104: the 5-cube occurs both as a B5 form and as a
  prism. Open Problem Garden's 105 matches the total before removing that
  duplicate.
- Zenodo: [10.5281/zenodo.23502450](https://doi.org/10.5281/zenodo.23502450)

## ekg-sequence v3 (October 20, 2026)

- Correction: v2 described OEIS A155549 as a set of indices n, but it lists
  the values a(n). v3 fixes the text and adds a Lean proof that A155549
  itself is finite.
- States that one count, #{k ≤ N : a(k) > k}, is proved in Lean only in the
  form #{k ≤ N : a(k) > k}/N → 1.
- Zenodo: [10.5281/zenodo.23493113](https://doi.org/10.5281/zenodo.23493113)

## ekg-sequence v2 (October 20, 2026)

- Proves, in the paper and in Lean, OEIS conjectures that follow from v1:
  Ordowski's (2009) on A064413 and Jasinski's (2008) on A152458 and A152519,
  finiteness of A155549 and A064420, and finitely many cycles of each length.
- Zenodo: [10.5281/zenodo.23491265](https://doi.org/10.5281/zenodo.23491265)

## steinberg-c4-c9 v2 (October 20, 2026)

- Adds an elementary proof: the graph is built from 27 copies of K4 by 26
  Ore compositions, which shows directly that it can't be 3-colored. Also
  shows it is 4-critical: removing any edge makes it 3-colorable.
- Zenodo: [10.5281/zenodo.23491271](https://doi.org/10.5281/zenodo.23491271)

## ekg-sequence v1 (October 20, 2026)

- First version: the second-order growth of the EKG sequence,
  b(n) = n + n/(3 log n) + o(n/log n). Paper, Lean proof and checks.

## uniform-5-polytopes v1 (October 20, 2026)

- First version: completeness of the known list of convex uniform
  5-polytopes, conditional on the 3- and 4-dimensional classifications.
  Paper, Lean formalization and certificate checkers.
- Zenodo: [10.5281/zenodo.23491267](https://doi.org/10.5281/zenodo.23491267)

## density-seven v1 (October 20, 2026)

- First version: the density Hales–Jewett number for length 7 over three
  letters is 1,302. Paper, witness and certificate checkers.
- Zenodo: [10.5281/zenodo.23491269](https://doi.org/10.5281/zenodo.23491269)

## steinberg-c4-c9 v1 (October 20, 2026)

- First version: an 82-vertex planar graph with no 4- or 9-cycles that has
  no proper 3-coloring. Paper, graph, SAT certificate and checkers.
