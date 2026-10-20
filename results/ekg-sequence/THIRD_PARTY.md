# Source attributions

All file paths below are relative to this result's folder.

The EKG foundation sources derive from Tomer Haver, *Explicit rates for the
EKG sequence*, version 3, October 4, 2026,
[DOI 10.5281/zenodo.23129632](https://doi.org/10.5281/zenodo.23129632),
which retains the version 2 Lean archive. That deposit designates
Creative Commons Attribution 4.0 International (CC BY 4.0):
https://creativecommons.org/licenses/by/4.0/ .

Relative to that archive, `EKG/PatternCount.lean` replaces a finite
native-evaluation proof with ordinary kernel proofs. The port makes two
tactic-only changes in `EKG/PrimeEstimates.lean` and
`EKG/PrimeStructureObstruction.lean`. The PartA, PartB, Counting and
Endpoint modules, together with the theorem adapters and public interface,
are additions. File-level attribution is listed below.
The mathematical argument also credits Lagarias, Rains and Sloane, and
Hofman and Pilipczuk in the manuscript.

Files under `lean/PrimeNumberTheoremAnd/` are an unchanged subset of
*PrimeNumberTheoremAnd* (Prime Number Theorem and More),
by A. Kontorovich, T. Tao et al., revision
`c39a751132c88b6e8080b74c74023fd95b3d8be0`,
https://github.com/AlexKontorovich/PrimeNumberTheoremAnd .
They retain their source copyright and author notices. They remain under [Apache License 2.0](https://www.apache.org/licenses/LICENSE-2.0).
Every file under `lean/PrimeNumberTheoremAnd/` is covered by this attribution;
none has been changed.

Downloaded Lean, mathlib and other dependencies retain their respective
licenses and are not redistributed in this small source bundle.
The following files derive from Haver and retain Haver's CC BY 4.0 notice,
including the three modified files identified above:

```text
lean/EKG/Asymptotic.lean
lean/EKG/Basic.lean
lean/EKG/Bootstrap.lean
lean/EKG/Canonical.lean
lean/EKG/Clock.lean
lean/EKG/ClockRates.lean
lean/EKG/CompositePositions.lean
lean/EKG/CrossingBounds.lean
lean/EKG/Crossings.lean
lean/EKG/EarlyEvens.lean
lean/EKG/FiniteBase.lean
lean/EKG/Frontier.lean
lean/EKG/HoleCounting.lean
lean/EKG/MainRate.lean
lean/EKG/MissingComposites.lean
lean/EKG/OrdinaryPositions.lean
lean/EKG/PatternCount.lean
lean/EKG/PrimeEstimates.lean
lean/EKG/PrimePatternBase.lean
lean/EKG/PrimeStructure.lean
lean/EKG/PrimeStructureGlobal.lean
lean/EKG/PrimeStructureLarge.lean
lean/EKG/PrimeStructureLocal.lean
lean/EKG/PrimeStructureObstruction.lean
lean/EKG/PrimeStructurePermutation.lean
lean/EKG/RateAssembly.lean
lean/EKG/SelfPairing.lean
lean/EKG/SmoothedPositions.lean
lean/EKG/Span.lean
lean/EKG/Targets.lean
lean/EKG/VerifiedClock.lean
lean/EKG/VerifiedCounts.lean
lean/EKG/VerifiedSpans.lean
```

All other Lean files in `lean/`, except the PNT subtree identified
above, are new sources covered by the repository's root `LICENSE`. No proof source was changed
when adding these license notices.
