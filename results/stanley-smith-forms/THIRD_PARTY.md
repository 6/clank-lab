# Third-party material

No third-party material is included in this folder. The certificates, the
census data, the checkers, the optional census programs, the Lean sources
and the paper were produced for this result.

The Lean project depends on [Lean 4](https://github.com/leanprover/lean4)
v4.34.0 and [Mathlib](https://github.com/leanprover-community/mathlib4) at
revision 5ed2965256430c3649e86755f9576b54eca72435, distributed upstream
under Apache-2.0
([Lean license](https://github.com/leanprover/lean4/blob/v4.34.0/LICENSE),
[Mathlib license](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/LICENSE)),
together with Mathlib's own declared dependencies. They are fetched by elan
and Lake, not vendored in this bundle, and their license notices remain
with their distributions.

The optional programs in `checks/census/` import
[python-flint](https://github.com/flintlib/python-flint) and
[SymPy](https://github.com/sympy/sympy), which the reader installs
separately; neither is included. The certificate check uses only the Python
standard library.

Stanley's survey, Grinberg's MathOverflow comment and the other cited works
are bibliographic references: they are cited, not redistributed. The control case λ = (5,1), k = 5 is Stanley's
worked example, recomputed here; its certificate was produced for this
result.
