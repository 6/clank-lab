# Third-party material

`checks/drat-trim.c` is an unmodified copy of the DRAT-trim proof checker
by Marijn Heule and Nathan Wetzler, from
[the matching upstream commit](https://github.com/marijnheule/drat-trim/blob/2e3b2dc0ecf938addbd779d42877b6ed69d9a985/drat-trim.c).
Its source header dates the last edit to April 21, 2024. It is distributed
under MIT, separately from the original work's Apache-2.0 license.
The original work is by the author named in the paper.

The Lean project depends on [Lean 4](https://github.com/leanprover/lean4)
and [Mathlib](https://github.com/leanprover-community/mathlib4), distributed
upstream under Apache-2.0. Their source and binaries are fetched dependencies,
not vendored material in this bundle. The project imports Std's CNF definitions
and Mathlib's graph, coloring and walk APIs. The local deletion-erased RUP
checker and its soundness proof were written for this formalization. Prior
LRAT verification methodology is credited in the paper.

The source retains this full notice (including its updated copyright line):

```text
Copyright (c) 2014 Marijn Heule and Nathan Wetzler, The University of Texas at Austin.
Copyright (c) 2015-2024 Marijn Heule, Carnegie Mellon University
Last edit: April 21, 2024

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
```

The accompanying upstream license supplied with the source also retains
this notice, reproduced without alteration:

```text
Copyright (c) 2014 Marijn Heule and Nathan Wetzler, The University of Texas at Austin.
Copyright (c) 2015-2016 Marijn Heule, The University of Texas at Austin.

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

```

The proof `data/col3.drat` was generated with
[CaDiCaL](https://github.com/arminbiere/cadical), by Armin Biere and
collaborators. CaDiCaL source and executable are not redistributed and are
not needed to check the certificate. The DRAT proof format and its checker
are due to Heule, Wetzler and collaborators; see the paper's references.
No text, figure or code from the graph-coloring papers is redistributed.
