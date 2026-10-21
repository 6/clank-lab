import R3P10.Base

/-! # The ladder rungs and the K_18 cover, checked by Lean's LRAT checker

Each `lrat_unsat` reads a compact certificate from `generated/certs/`, which
`../checks/check.py` writes (a rung re-solved whole by the bundled solver, or
the cover re-derived by CaDiCaL; drat-trim's LRAT proof repacked by
`../checks/pack.py`), and proves the fact by `checkCompact_sound` and
`Lean.ofReduceBool`: the kernel evaluates Lean's verified LRAT checker on the
certificate. These are the eight non-cube hypotheses of `K18_P10_of_certs`.

Build with `lake build R3P10Ladder` after `python3 ../checks/check.py quick`
(or its `ladder` step) has written the certificates. -/

namespace R3P10

lrat_unsat cert_k5p3 5 3 (encode 5 0) "generated/certs/k5p3.cert"
lrat_unsat cert_k6p4 6 4 (encode 6 3) "generated/certs/k6p4.cert"
lrat_unsat cert_k9p5 9 5 (encode 9 4) "generated/certs/k9p5.cert"
lrat_unsat cert_k10p6 10 6 (encode 10 5) "generated/certs/k10p6.cert"
lrat_unsat cert_k13p7 13 7 (encode 13 6) "generated/certs/k13p7.cert"
lrat_unsat cert_k14p8 14 8 (encode 14 7) "generated/certs/k14p8.cert"
lrat_unsat cert_k17p9 17 9 (encode 17 8) "generated/certs/k17p9.cert"

lrat_unsat cover_raw 18 10 (k18Base ++ finalCubes.map negCube) "generated/certs/cover.cert"

/-- The K_18 cover: `encode 18 9`, the generation path clauses and the
negation of every final cube are refuted. -/
theorem cert_k18_cover : UnsatWithPaths 18 10 (encode 18 9 ++ finalCubes.map negCube) := by
  rw [encode_k18]; exact cover_raw

/- The final list has 15,956 cubes. -/
native_decide_thm finalCubes_length : finalCubes.length = 15956

/-! The statements, exactly as `K18_P10_of_certs` needs them. -/

example : UnsatWithPaths 5 3 (encode 5 0) := cert_k5p3
example : UnsatWithPaths 6 4 (encode 6 3) := cert_k6p4
example : UnsatWithPaths 9 5 (encode 9 4) := cert_k9p5
example : UnsatWithPaths 10 6 (encode 10 5) := cert_k10p6
example : UnsatWithPaths 13 7 (encode 13 6) := cert_k13p7
example : UnsatWithPaths 14 8 (encode 14 7) := cert_k14p8
example : UnsatWithPaths 17 9 (encode 17 8) := cert_k17p9

end R3P10

/-- info: 'R3P10.cert_k17p9' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound] -/
#guard_msgs in #print axioms R3P10.cert_k17p9

/-- info: 'R3P10.cert_k18_cover' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound] -/
#guard_msgs in #print axioms R3P10.cert_k18_cover
