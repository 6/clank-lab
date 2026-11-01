# Formalization

The project uses Lean 4.19.0 and mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The toolchain and Lake manifest pin the complete dependencies. With elan and Git installed, run `lake exe cache get` and `lake build` here. Downloaded dependencies can occupy several gigabytes. The proof build needs roughly 6 GB of memory; allow more when building several modules concurrently.

`FT23.conjecture_counterexample` proves that the explicit functions `phi` and `psi` give a strict Archimedean generator and its inverse, that `C` is a copula on the closed unit square, that it is PQD everywhere on that square, and that it is not PMI. `FT23.conjecture_equivalence_false` states the resulting failure of the universal equivalence. The root import includes both final statements and the checks in `FT23/Audit.lean`; plain `lake build` builds that root.

`FT23/Definitions.lean` defines PMI by a positive Borel measure on the open square $(0,1/2)^2$ with finite rectangle values equal to the increments of the reflected copula sum. `MeasureBridge.lean` proves that a negative rectangle contradicts that definition. This uses no absolute-continuity assumption. `GeneratorAdmissible.lean`, `Copula.lean` and `PQD.lean` establish the analytic properties globally, including the zero boundary. `CornerBridge.lean` gives exact square-root enclosure conditions, and `Witness.lean` supplies all sixteen rational corner enclosures for the displayed rectangle.

The build checks the final theorem's type, the rectangle's location, the independence example's zero reflected increments and the final theorems' axiom lists. Only `propext`, `Classical.choice` and `Quot.sound` are permitted. No compiled-evaluation axiom, floating-point computation or external numerical checker is needed by the proof.

The paper uses coarser rational bounds to make the arithmetic readable. Its table is a presentation of the same sixteen corners; `Witness.lean` proves the negative increment with tighter bounds.
