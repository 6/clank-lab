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

A source-only default build with dependency caches took about 4.5 minutes
on a 12-CPU allocation. Peak observed memory was 10.1 GiB for one compiler
and 16.9 GiB for the complete build process tree; dependency download time
is excluded. The package uses six proof threads per compiler.

[Check.lean](Check.lean) states `Steinberg.counterexample`:

```lean
HasSphericalRotation graph rotation ∧
(∀ v (p : graph.Walk v v), p.IsCycle → p.length ≠ 4 ∧ p.length ≠ 9) ∧
IsEmpty (graph.Coloring (Fin 3))
```

The graph is a `SimpleGraph (Fin 82)`. [Data.lean](Steinberg/Data.lean)
parses the bundle's unchanged [graph](../data/graph.txt) and
[rotation](../data/rotation.txt) through `include_str`, checks parsing,
bounds, distinctness and counts, and defines adjacency from those edges.
Literal normal forms used to shorten later calculations are proved equal
to these parsed data.

The three properties use this same graph:

- [Rotation.lean](Steinberg/Rotation.lean) defines the spherical rotation
  criterion. Each vertex has its exact neighbors in one cyclic order;
  reversal followed by cyclic successor traces faces. The graph is connected,
  and distinct, nonempty face orbits partition every dart exactly once.
  [The certificate](Steinberg/RotationCertificate.lean) checks 272 darts and
  56 faces. [The theorem](Steinberg/RotationControls.lean) assembles this
  certificate with `82 + 56 = 136 + 2`. This is the combinatorial planarity
  criterion; its correspondence with a topological embedding is the surface
  argument in the paper, rather than a separate Lean realization theorem.
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
