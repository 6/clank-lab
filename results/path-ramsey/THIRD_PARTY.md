# Third-party material

No third-party source code or data is included in this folder. The solver
`checks/p3path.cpp`, the certificate packer, the checkers, the encoding
auditor, the Lean development and the data files were written for this
result.

The executable checks download and build three tools from their upstream
repositories at pinned commits, into a work directory outside this folder
(`checks/check.py`). They are used under their own licenses and are not
redistributed here:

- [CaDiCaL](https://github.com/arminbiere/cadical) by Armin Biere and
  contributors, MIT license. The solver `checks/p3path.cpp` links against
  it and uses its external-propagator interface.
- [drat-trim](https://github.com/marijnheule/drat-trim) by Marijn Heule and
  Nathan Wetzler, MIT license.
- [cake_lpr](https://github.com/tanyongkiam/cake_lpr) by Marijn Heule,
  Magnus Myreen and Yong Kiam Tan, under the CakeML copyright notice and
  license (a BSD-style license) reproduced in its repository.

The formal development uses Lean v4.32.2 and Mathlib (with its dependencies
Plausible, LeanSearchClient, ImportGraph, ProofWidgets, Aesop, Qq and
Batteries, under Apache-2.0, and Lean4 CLI, under the MIT license). They
are obtained through elan and Lake at the versions pinned in
`lean/lean-toolchain` and `lean/lake-manifest.json`; no copy of them is
included. The certificates are checked by the LRAT checker that ships with
Lean (`Std.Tactic.BVDecide.LRAT`), under Lean's Apache-2.0 license.
