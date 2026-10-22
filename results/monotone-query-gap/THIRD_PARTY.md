# Third-party material

The paper, proof sources, certificate and checkers supplied here are under
Apache-2.0. No third-party source code is copied into the bundle.

[Lean](https://github.com/leanprover/lean4), installed separately through
elan at the version selected by `lean/lean-toolchain`, is licensed under
[Apache-2.0](https://github.com/leanprover/lean4/blob/v4.34.0/LICENSE).
The Lake project fetches [Mathlib](https://github.com/leanprover-community/mathlib4)
and its dependencies to provide the standard cache command. These upstream
trees and compiled caches are not included here, and no modifications to
them are supplied. Their downloaded copies retain their upstream license
and attribution notices. The mathematical proof itself uses Lean's core
library and does not import Mathlib. Exact revisions are recorded in
`lean/lake-manifest.json`.

| Dependency | License |
| --- | --- |
| [Mathlib](https://github.com/leanprover-community/mathlib4) | Apache-2.0 |
| [plausible](https://github.com/leanprover-community/plausible) | Apache-2.0 |
| [LeanSearchClient](https://github.com/leanprover-community/LeanSearchClient) | Apache-2.0 |
| [importGraph](https://github.com/leanprover-community/import-graph) | Apache-2.0 |
| [ProofWidgets](https://github.com/leanprover-community/ProofWidgets4) | Apache-2.0 |
| [aesop](https://github.com/leanprover-community/aesop) | Apache-2.0 |
| [Qq](https://github.com/leanprover-community/quote4) | Apache-2.0 |
| [batteries](https://github.com/leanprover-community/batteries) | Apache-2.0 |
| [Cli](https://github.com/leanprover/lean4-cli) | MIT |

The mathematical definitions and Question 2.1 are due to Laurin
Köhler-Schindler and Jeffrey E. Steif, *A study of distributional complexity
measures for Boolean functions*, [ACM Transactions on Computation Theory
(2026)](https://doi.org/10.1145/3814613), published online May 19, 2026;
[first posted as arXiv:2408.12995 on August 23, 2024](https://arxiv.org/abs/2408.12995v1).
The question's wording and numbering, and the example numbers, are cited
from arXiv v1, the only arXiv version listed. The [open author manuscript](https://www.math.chalmers.se/~steif/p74.pdf)
retains the question's wording and number; ACM's final typeset text was not
accessible to us. The short quotation of the question is attributed in the
paper. That quotation remains the original authors' text; the repository license does not relicense it.
Other cited works are used for mathematical background, with no copied
code, tables or figures.

Our own discovery code used [Google OR-Tools' CP-SAT solver](https://developers.google.com/optimization/cp/cp_solver),
which is [Apache-2.0 licensed](https://github.com/google/or-tools/blob/stable/LICENSE).
Neither that search code nor OR-Tools is included here or needed for the proof
checks. The paper credits the OR-Tools contributors for this discovery tool.
