# Changelog

Each result is versioned on its own and tagged `NAME-vN`. A new version never
replaces an old one: earlier versions stay available through their tags and
Zenodo records.

## uniform-5-polytopes v2 (October 20, 2026)

- Added the external-hypothesis evidence map, explicit finite-fan chart
  correspondence, literal P1 range check, and 104-count overlap check.
- Correction: version 1 named primary proof programs that were absent from
  the bundle and supplied a Lean report without its source or a check
  against the executable output. Version 2 ships those programs and source,
  replays both proof routes, and checks all 629 logical report rows.
  It also checks stage-one interval containment, disjoint class intervals,
  the exact 628/1/890 outcomes and complete known-name coverage.
- Correction: the extra-candidate table conflated search states with
  development branches. At P16 the primary search has four completed states
  for that encoding and a two-branch development; the independent development
  has four nodes. A displayed snub-cube separation value is a squared
  distance, not a distance. These bookkeeping corrections do not alter
  either exclusion.
- The finite count is 104 = 19 + 31 + 8 + 47 − 1: the 5-cube occurs both
  among B5 forms and as a prism. Open Problem Garden's 105 equals the
  subtotal before that subtraction, but its page does not explain the
  discrepancy. No historical explanation is asserted. The classification
  and its conditional scope are unchanged.
  Tag on publication: `uniform-5-polytopes-v2`.

## ekg-sequence v3 (October 20, 2026)

- Correction to v2: OEIS A155549 lists the values a(n), not the indices n.
  v2's paper, Lean README and Lean docstring described it as the indices n
  with a(n) not prime and a(n) <= n - 1, and its Lean statement was about
  that index set. v3 describes A155549 correctly and adds a Lean theorem
  that A155549 itself, the image of that set under a, is finite. It also
  says that #{k <= N : a(k) > k} is Lean-checked only in the form
  #{k <= N : a(k) > k}/N -> 1, and removes a stale comment about
  native_decide. Tag `ekg-sequence-v3`.
- Zenodo: [10.5281/zenodo.23493113](https://doi.org/10.5281/zenodo.23493113)

## ekg-sequence v2 (October 20, 2026)

- Consequences of the v1 theorem, proved in the paper and in Lean:
  Ordowski's 2009 conjectures on A064413 (for large n, a(n) > n exactly
  when a(n) is composite), Jasinski's 2008 finiteness conjectures on
  A152458 and A152519, finiteness of A155549 and A064420, and finitely
  many cycles of each bounded length. Tag `ekg-sequence-v2`.
- Zenodo: [10.5281/zenodo.23491265](https://doi.org/10.5281/zenodo.23491265)

## steinberg-c4-c9 v2 (October 20, 2026)

- Adds the explicit tree of 27 K4 graphs and 26 Ore compositions and an
  elementary non-three-colorability proof. All 136 edge-deletion colorings
  certify four-criticality and equality in the Kostochka–Yancey edge bound
  at order 82; no minimum-order claim is made. A single standalone checker
  verifies the construction and these certificates. Tag: `steinberg-c4-c9-v2`.
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
