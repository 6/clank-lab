# Lean proof

From this directory, with [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get
lake build
```

The toolchain and Mathlib dependency are pinned in `lean-toolchain`,
`lakefile.toml` and the standard Lake dependency manifest. They use Lean
4.34.0 and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
Only dependency artifacts come from the Mathlib cache; Lake checks the local
proof sources.

[Check.lean](Check.lean) states `Steinberg.planar_counterexample`:

```lean
RationalPlanar graph ∧
(∀ v (p : graph.Walk v v), p.IsCycle → p.length ≠ 4 ∧ p.length ≠ 9) ∧
IsEmpty (graph.Coloring (Fin 3))
```

`RationalPlanar G` is the existence of an injective map from the finite
vertex set into rational coordinate pairs giving a crossing-free straight-line
drawing. [Drawing.lean](Steinberg/Drawing.lean) defines each closed segment
by a real affine parameter between zero and one. Every vertex is excluded
from a segment unless it is an endpoint; distinct edge segments can meet
only at the image of a common endpoint. This includes adjacent edges, whose
interiors cannot overlap. Increasing endpoint labels only select a canonical
orientation for undirected edges; segment reversal is proved in Lean.

[Planarity.lean](Steinberg/Planarity.lean) proves this property for the
unchanged graph. [DrawingData.lean](Steinberg/DrawingData.lean) contains the
figure's exact six-decimal coordinates as integer millionths, interpreted as
rationals by division by one million. The coordinate export can be reproduced
with `python3 checks/export_lean_drawing.py --check` from the bundle root.
The exporter checks equality to the existing SVG and PDF and is not trusted
by the formal proof: Lean checks the literal coordinates and proves equality
between its edge list and the parsed graph.

The finite check uses separating linear functionals with integer
coefficients. Lean proves that strict separation of endpoints excludes every
intersection of their real closed segments. A supporting functional at a
shared endpoint proves that adjacent edges meet there alone. Every vertex
and edge pair is checked by kernel reduction in
[DrawingCertificate.lean](Steinberg/DrawingCertificate.lean) and
[DrawingRows.lean](Steinberg/DrawingRows.lean), then composed with these
geometric soundness lemmas. [DrawingControls.lean](Steinberg/DrawingControls.lean)
checks a solved square and rejects crossing, coincident, nonincident and
overlapping configurations. No assumption of general position is used.

The earlier `Steinberg.counterexample` theorem is retained with its exact
statement, replacing `RationalPlanar graph` by
`HasSphericalRotation graph rotation` in the conjunction above.

The graph is a `SimpleGraph (Fin 82)`. [Data.lean](Steinberg/Data.lean)
parses the bundle's unchanged [graph](../data/graph.txt) and
[rotation](../data/rotation.txt) through `include_str`, checks parsing,
bounds, distinctness and counts, and defines adjacency from those edges.
Literal normal forms used to shorten later calculations are proved equal
to these parsed data.

Both endpoint theorems concern this same graph. The retained components are:

- [Rotation.lean](Steinberg/Rotation.lean) defines the spherical rotation
  criterion. Each vertex has its exact neighbors in one cyclic order;
  reversal followed by cyclic successor traces faces. The graph is connected,
  and distinct, nonempty face orbits partition every dart exactly once.
  [The certificate](Steinberg/RotationCertificate.lean) checks 272 darts and
  56 faces. [The theorem](Steinberg/RotationControls.lean) assembles this
  certificate with `82 + 56 = 136 + 2`. This is the combinatorial planarity
  criterion. The paper retains its written surface argument; the new
  geometric theorem proves planarity directly from the rational drawing.
- [Cycles.lean](Steinberg/Cycles.lean) proves exclusion of lengths four and
  nine for every Mathlib closed walk satisfying `IsCycle`, including cycles
  with chords. The bounded search has a general soundness proof and checks
  every possible starting vertex against the parsed adjacency relation.
- [Noncolorable.lean](Steinberg/Noncolorable.lean) proves soundness of a
  generic coloring-to-CNF reduction and equality of its computed formula
  to the certificate input: 246 variables and 736 clauses, with no symmetry
  units. [Core.lean](LocalRup/Core.lean) proves a RUP checker's soundness,
  resolving each hint against input or previously proved clauses. Deletion
  records retain the entailed clauses. The explicit Lean certificate data
  and chunk checks prove a final empty clause. This restricted LRAT-style
  checker does not implement general RAT or deletion-liveness validation.

The default build also checks a fully qualified explicit type for the top
theorem, the meaning of the raw UNSAT predicate and its standard CNF bridge,
and exact `#guard_msgs` audits of `#print axioms`. The top theorem uses only
`propext`, `Classical.choice` and `Quot.sound`. Certificate checks use kernel
reduction. There is no native/compiler proof evaluation or additional axiom.

Controls in the default build include a planar K4 rotation, a toroidal K4
face certificate failing Euler, duplicate-neighbor and missing-face rejection,
a corrupted symmetry-free certificate addition, and the added edge `0--12`
that creates the explicit simple cycle `0--6--60--12--0`. The torus control
refutes its supplied face certificate, rather than quantifying over every
possible face list.

The retained executable checks are documented [separately](../checks/README.md).
Four-criticality, the Ore decomposition, the sharp edge bound and exclusion
of ten-cycles keep their written and executable proofs; the Lean theorem above
does not assert those additional properties.
