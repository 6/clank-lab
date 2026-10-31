# Third-party material

`checks/drat-trim.c` is an unmodified copy of the DRAT-trim proof checker
by Marijn Heule and Nathan Wetzler, from
[the matching upstream commit](https://github.com/marijnheule/drat-trim/blob/2e3b2dc0ecf938addbd779d42877b6ed69d9a985/drat-trim.c).
It is distributed under the MIT license below, separately from the rest of
this folder's Apache-2.0 license. The rest is by the author named in the
paper.

The source retains this notice:

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

The proof `data/strict4.drat` was produced by
[CaDiCaL](https://github.com/arminbiere/cadical) 2.1.3, by Armin Biere and
collaborators. CaDiCaL is not redistributed and is not needed to check the
proof. No text, figure or code from the cited papers is redistributed.
