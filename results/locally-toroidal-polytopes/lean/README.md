# Lean proof of existence of locally toroidal polytopes

For example, the parameters $s=3$, $u=9$ give a universal regular
4-polytope with square toroidal facets of period 3 and vertex-figures of
period 9. In general, the theorem covers every ordered pair of distinct
odd integers $s,u\geq3$, including pairs with common divisors. It proves
the existence clause of McMullen and Schulte's Conjecture 10C7, restated
in Schulte and Weiss's Problem 16. Classification and the conjectured
finiteness criterion remain open.

The proofs, the Lean formalization and the text were produced by AI models
(from OpenAI and Anthropic), working under the author's direction.

With [elan](https://github.com/leanprover/elan) installed, run these commands
from this directory:

```sh
lake exe cache get
lake build
```

Elan installs the Lean version selected by `lean-toolchain`. The manifest
pins Mathlib and its dependencies; no other part of the accompanying
material is required. The build retrieves dependency caches and checks all
proof modules, statement interfaces, examples, and axiom guards.

For the group formulation, start with `Main.lean`. Its theorem
`P16c.Main.p16c` uses explicit presented groups and asserts the involution
relations, exact adjacent orders, commuting nonadjacent generators, the
intersection property for every pair of generator subsets, and
generator-preserving identifications of both local groups with orders
$8s^2$ and $8u^2$.

For the polytope formulation, start with `StatementTorus.lean`.
`P16c.p16c_polytope_geometric` constructs a regular 4-polytope with the
prescribed geometric square toroidal facets and vertex-figures and a
covering onto every regular 4-polytope with these local sections.
`P16c.torus_identification` identifies the geometric maps with the coset
maps of their presentations. Their definitions are in `P16c/TorusDefs.lean`,
`P16c/Polytope.lean`, and `P16c/CosetPoset.lean`.

`ExactTypes.lean` checks the complete quantified types of the theorem
interfaces. `Examples.lean` checks lattice reduction, torus faces and
reflections, generation, and applications at noncoprime and reversed
parameter pairs. `Axioms.lean` uses `#guard_msgs` to require that each listed
theorem depends on exactly `propext`, `Classical.choice`, and `Quot.sound`;
a changed axiom report fails the build.

Dependencies and their licenses are described in
[THIRD_PARTY.md](../THIRD_PARTY.md).
