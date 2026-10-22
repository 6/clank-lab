# Third-party material

## Nine-point Thomson formalization

The Lean project adapts Aravind Karthigeyan's
[thomson-n9-lean](https://github.com/aravindkarthigeyan/thomson-n9-lean/tree/168ff0c98cab4dfda0460ba55f8d169070ac385e),
commit `168ff0c98cab4dfda0460ba55f8d169070ac385e`, under the MIT license.
The reused Lean code is MIT-licensed. No prose from the upstream manuscript
is copied here; its separately licensed prose is not part of this adaptation.
Its proof architecture and implementation are substantial foundations of this
work. The upstream license notice is reproduced in full below.

The upstream `proof/lean/ThomsonN9/` definitions, challenge structure,
three-point certificate interfaces, scalar bounds, geometric alignment, and
local-Hessian proof supply the corresponding components under
`lean/ThomsonN10/`, together with `lean/Challenge.lean` and `lean/Solution.lean`.
The upstream exact polynomial-checking and window-classification modules
supply `lean/ThomsonN10/Cert/L1/` and `lean/ThomsonN10/Windows/`.
The ambient-circuit export design supplies the exact certificate layout under
`lean/ThomsonN10/Local/Certificates/`. Each adapted file identifies its
specific upstream source in its opening comment.

Changes specialize the configuration size, namespaces, candidate geometry,
stationarity equation, rational height interval, polynomial and scalar
certificates, window-classification data, and constrained-Hessian data and
proofs to ten points and the bicapped square antiprism. The adapted project
adds the full ten-point theorem and candidate-admissibility proof. Public
packaging adds build checks, automatic decompression of the large exact
certificate, and removes process identities from comments. References in
source comments to certificate generators describe their provenance; those
generators are not needed to check the supplied exact certificate data.
The independent Python checker reconstructs the operators separately; it
imports no upstream generator or proof code.

```text
MIT License

Copyright (c) 2026 Aravind Karthigeyan

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```

## Lean and Mathlib

The proof uses [Lean](https://github.com/leanprover/lean4) and
[Mathlib](https://github.com/leanprover-community/mathlib4), distributed under
Apache-2.0. Lake downloads these dependencies using the project's pinned
configuration; their source trees and licenses are not redistributed in this
folder. Dependency notices remain in the downloaded packages.

The manuscript and the new material are under Apache-2.0, as specified by
the repository's root LICENSE. The MIT notice above continues to apply to
the adapted material.
