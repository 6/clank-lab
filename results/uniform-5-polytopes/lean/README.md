# Conditional Lean formalization

The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

The project formalizes selected geometric lemmas and a conditional classification of convex uniform five-dimensional polytopes. It does not prove the external computations or the cited lower-dimensional classifications, and it does not jointly instantiate all its assumptions.

`Uniform5.Composition.mainClassification` and `classification_of_core_inputs` take exactly twelve computational hypotheses: `LIB`, `S1`, `S2`, `ROOT`, `DEV`, `B2`, `P1`, `W`, `PartnerRadiusFilter`, `U3Realizations`, `U3Identification` and `U3Forcing`. The unused `FILTER`, `RIDGES`, `QFOLLOW` and `LU` hypotheses and their data parameters have been removed. The manuscript appendix prints the twelve structure declarations verbatim.

Both theorems also assume `CitedClassification3D` and `CitedClassification4D`, and take explicit numerical/geometric data parameters. Their conclusion is:

```lean
∀ P : Set (Space 5), UnitUniform 5 P → K1 P ∨ K2 P ∨ K3 P
```

`UnitUniform` means a finite convex hull of affine dimension five, vertex transitivity, recursively uniform facets and unit exposed edges. `K1`, `K2` and `K3` are whole-set congruences to the specified Wythoff orbit hulls, prisms over uniform 4-polytopes and polygon–polyhedron products.

The written links between certificate output and these hypotheses remain outside Lean: library/model correspondence, stage-1 root coverage, stage-2 signature coverage, stage-3 encodings and identification/forcing, exhaustive refutation of the extra candidate, and the numerical B2/P1/W/partner-radius assertions used in Case B. Formalized conditional geometry does not discharge these links. Coverage does not assert existence of every retained encoding, and `DEV` refutes a hypothetical actual full star. A proof of the implication alone establishes neither truth nor joint satisfiability of its premises.

## Rebuild and audit

Install elan, then from the bundle root run:

```bash
cd lean
lake exe cache get
lake build
lake env lean Audit.lean
```

Lake downloads dependencies; no other checkout or local dependency path is required. `lake-manifest.json` pins all transitive packages. Build artifacts and dependencies are not shipped.

`lake build` checks the modules imported by `Uniform5.lean`. `Audit.lean` traverses every declaration in the `Uniform5` namespace and rejects dependencies other than `propext`, `Classical.choice` and `Quot.sound`. It additionally runs `#print axioms` for the main classification, its core theorem, Case A and Case B. Success begins `PASS dependency audit:`. This checks kernel foundations; the explicit assumptions remain hypotheses.

There has been no human expert review. Apache-2.0 applies to this work; Lean and Mathlib dependencies retain their own licences.
