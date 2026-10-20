# Changelog

Each result is versioned on its own and tagged `NAME-vN`. A new version never
replaces an old one: earlier versions stay available through their tags and
Zenodo records.

## ekg-sequence v2 (October 20, 2026)

- Consequences of the v1 theorem, proved in the paper and in Lean:
  Ordowski's 2009 conjectures on A064413 (for large n, a(n) > n exactly
  when a(n) is composite), Jasinski's 2008 finiteness conjectures on
  A152458 and A152519, finiteness of A155549 and A064420, and finitely
  many cycles of each bounded length. Tag `ekg-sequence-v2`.

## steinberg-c4-c9 v2 (October 20, 2026)

- Adds the explicit tree of 27 K4 graphs and 26 Ore compositions and an
  elementary non-three-colorability proof. All 136 edge-deletion colorings
  certify four-criticality and equality in the Kostochka–Yancey edge bound
  at order 82; no minimum-order claim is made. A single standalone checker
  verifies the construction and these certificates. Tag: `steinberg-c4-c9-v2`.

## ekg-sequence v1 (October 20, 2026)

- First version: the second-order growth of the EKG sequence,
  b(n) = n + n/(3 log n) + o(n/log n). Paper, Lean proof and checks.

## uniform-5-polytopes v1 (October 20, 2026)

- First version: completeness of the known list of convex uniform
  5-polytopes, conditional on the 3- and 4-dimensional classifications.
  Paper, Lean formalization and certificate checkers.

## density-seven v1 (October 20, 2026)

- First version: the density Hales–Jewett number for length 7 over three
  letters is 1,302. Paper, witness and certificate checkers.

## steinberg-c4-c9 v1 (October 20, 2026)

- First version: an 82-vertex planar graph with no 4- or 9-cycles that has
  no proper 3-coloring. Paper, graph, SAT certificate and checkers.
