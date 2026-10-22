# Source attributions

All file paths below are relative to this result's folder. Every file not listed here is new and covered by the repository's root `LICENSE`.

## EKG sequence foundation (`lean/vendor/EKG/`)

The EKG foundation is the Lean tree of the author's earlier result, *The second-order asymptotic of the EKG sequence* ([DOI 10.5281/zenodo.23493113](https://doi.org/10.5281/zenodo.23493113)), copied without change. Its sources derive from Tomer Haver, *Explicit rates for the EKG sequence*, version 3, October 4, 2026, [DOI 10.5281/zenodo.23129632](https://doi.org/10.5281/zenodo.23129632), whose Lean archive is released under Creative Commons Attribution 4.0 International (CC BY 4.0): https://creativecommons.org/licenses/by/4.0/ .

Relative to Haver's archive, `lean/vendor/EKG/PatternCount.lean` replaces a finite native-evaluation proof with ordinary kernel proofs; `lean/vendor/EKG/PrimeEstimates.lean` and `lean/vendor/EKG/PrimeStructureObstruction.lean` have tactic-only changes; and `lean/vendor/EKG/PrimeStructureGlobal.lean` has its module comment updated to match. The following files derive from Haver and remain under CC BY 4.0, including the four changed files:

```text
lean/vendor/EKG/Asymptotic.lean
lean/vendor/EKG/Basic.lean
lean/vendor/EKG/Bootstrap.lean
lean/vendor/EKG/Canonical.lean
lean/vendor/EKG/Clock.lean
lean/vendor/EKG/CrossingBounds.lean
lean/vendor/EKG/Crossings.lean
lean/vendor/EKG/EarlyEvens.lean
lean/vendor/EKG/FiniteBase.lean
lean/vendor/EKG/Frontier.lean
lean/vendor/EKG/HoleCounting.lean
lean/vendor/EKG/MissingComposites.lean
lean/vendor/EKG/PatternCount.lean
lean/vendor/EKG/PrimeEstimates.lean
lean/vendor/EKG/PrimePatternBase.lean
lean/vendor/EKG/PrimeStructure.lean
lean/vendor/EKG/PrimeStructureGlobal.lean
lean/vendor/EKG/PrimeStructureLarge.lean
lean/vendor/EKG/PrimeStructureLocal.lean
lean/vendor/EKG/PrimeStructureObstruction.lean
lean/vendor/EKG/PrimeStructurePermutation.lean
lean/vendor/EKG/SelfPairing.lean
lean/vendor/EKG/Span.lean
lean/vendor/EKG/Targets.lean
lean/vendor/EKG/VerifiedCounts.lean
lean/vendor/EKG/VerifiedSpans.lean
```

The files `lean/vendor/EKG/CountingDefinitions.lean`, `lean/vendor/EKG/CountingExact.lean`, `lean/vendor/EKG/CountingMissing.lean`, `lean/vendor/EKG/CountingOccurrences.lean`, `lean/vendor/EKG/CountingPrimeIntervals.lean`, `lean/vendor/EKG/CountingTicks.lean` were added in the earlier result and are covered by the root `LICENSE`.

## Arithmetic large sieve (`lean/vendor/OAI/`)

Files under `lean/vendor/OAI/` are taken from OpenAI's mathematics formalizations, https://github.com/openai/math , commit `1581d4cbdd69a0faf34b2089614fe2a814316a6a`, under the [Apache License 2.0](https://www.apache.org/licenses/LICENSE-2.0). They are the declaration dependency cone of `OAI.Ostmann.prime_set_support_sieve`. Every retained statement and proof is verbatim. In every file the imports are replaced by `Mathlib` and the retained direct dependencies, for Lean 4.34.0 and the pinned mathlib (upstream uses Lean 4.34.1 and mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`); namespace, scope and variable commands are unchanged. The other changes are these omissions of unused declarations (paths relative to `lean/vendor/OAI/`):

- `NumberTheory/Ostmann/Arithmetic/CRTResidueAverage.lean`: omit `crtUnitEquiv_apply`, `crt_unit_average`.
- `NumberTheory/Ostmann/Arithmetic/ReducedFrequencyEnergy.lean`: omit `unitFrequencyEnergy_nonneg`.
- `NumberTheory/Ostmann/Arithmetic/ResidueIntervals.lean`: omit `reducedResidues_card_le`, `prime_mod_mem_reducedResidues`, `sum_residue_indicator`, `complexPrimeInterval_residues`, `complexIntegerInterval_residues`, `complexPrimeInterval_finset_sum`, `reciprocalPrimeInterval_le_exp`.
- `NumberTheory/Ostmann/Characters/AdditiveFourier.lean`: omit `additiveFourier`, `additiveFourier_apply`, `additiveFourier_inversion`, `additiveFourier_conjugate_coefficient`, `additiveFourier_energy`, `additiveFourier_parseval`, `additiveFourier_sub`, `additiveFourier_const`.
  The final orphaned doc comment becomes an ordinary comment after its declaration is omitted.
- `NumberTheory/Ostmann/Characters/FiniteKernelCoordinates.lean`: omit `uniformResidueVector_ite`, `residuePointVector_decomposition`, `rawAdditiveKernelAction_add_input`, `residuePointVector_kernel`.
- `NumberTheory/Ostmann/Characters/FiniteKernelPairing.lean`: omit `kernelPairing_polynomial`, `kernelPairing_rectangular`.
- `NumberTheory/Ostmann/Characters/TupleCRTFourier.lean`: omit `tupleCRTFunction`, `tupleCRTFunction_intCast`, `tupleCRTFunction_fourier`.
- `NumberTheory/Ostmann/Preliminaries/BoundedSieveSubsets.lean`: omit `sieve_subset_log_iff`, `fixed_shift_bounded_weight`.
- `NumberTheory/Ostmann/Quadratic/KernelCoordinateIdentity.lean`: omit `rawKernel_pairing_add`, `kernel_centered_coordinate_identity`.
  The final orphaned doc comment becomes an ordinary comment after its declaration is omitted.
- `NumberTheory/Ostmann/Supply/CenteredProjectionPairing.lean`: omit `rawAdditiveKernelAction_selfAdjoint`.
- `NumberTheory/Ostmann/Supply/CenteredSupportProjection.lean`: omit `centered_support_energy`, `centeredSupportProjection_energy`, `centeredSupportProjection_energy_le`, `centeredSupportProjection_eq_of_eqOn`, `centeredSupportProjection_disjoint`, `centeredSupportProjection_spectral_energy`.
- `NumberTheory/Ostmann/Supply/NaturalResidueAverage.lean`: omit `sum_reducedResidues_eq_units`, `sum_range_eq_zmod`.
- `NumberTheory/Ostmann/Tree/TruncatedModePairing.lean`: omit `finiteKernelOperator_pairing_le`, `lowModeVector`, `truncatedSparseTensorKernel_pairing`, `truncatedSparseTensorKernel_pairing_le`.

## Prime-counting bounds (`lean/vendor/IEANTN/`)

Files under `lean/vendor/IEANTN/` come from two projects under the [Apache License 2.0](https://www.apache.org/licenses/LICENSE-2.0), and keep their copyright headers:

- IEANTN, https://github.com/teorth/IEANTN , commit `ec66e388e6e117c6881367f38665f310edf7cacf`. Copyright (c) 2026 IEANTN contributors; Chebyshev proof by Terence Tao; the Rosser–Schoenfeld Theorem 12 formalization by Akula and PrimeNumberTheoremAnd contributors, crediting the PrimeNumberTheoremAnd formalization at `81eca5aa3fa4779883a9aeba18e49087c5366e0f`. Files: `lean/vendor/IEANTN/RS12/` and `lean/vendor/IEANTN/Chebyshev/`.

- LeanCert, https://github.com/alerad/leancert , commit `6b11513512c9d27183fb4725bfc291ab38b4a6d7`. Copyright (c) 2026 LeanCert Contributors. Files: `lean/vendor/IEANTN/LeanCert/`.

Changes: in 56 files the local imports are prefixed with `IEANTN.` (mathematical namespaces and declarations are not renamed); `Chebyshev.v1`'s `LogBounds` import is relocated to `IEANTN.Chebyshev.LogBounds`; and `lean/vendor/IEANTN/Chebyshev/Lower.lean` (upstream `Solutions/Chebyshev.v1/ChebyshevDev.lean`) keeps the upstream file only through `psi_lower`, omitting its later upper bounds, with `end ChebyshevSol` appended. The files with no change are: `lean/vendor/IEANTN/Chebyshev/LogBounds.lean`, `lean/vendor/IEANTN/LeanCert/Core/DerivativeIntervals.lean`, `lean/vendor/IEANTN/LeanCert/Core/Expr.lean`, `lean/vendor/IEANTN/LeanCert/Core/Interval.lean`, `lean/vendor/IEANTN/RS12/Chebyshev.lean`, `lean/vendor/IEANTN/RS12/Tables.lean`, `lean/vendor/IEANTN/RS12/Weights.lean`.

## Dependencies

Lean, mathlib and their dependencies are downloaded by Lake from their own repositories, keep their own licenses, and are not redistributed here. The cover checker uses python-flint (the Arb and FLINT libraries), installed separately.
