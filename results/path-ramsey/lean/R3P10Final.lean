import R3P10.Ramsey
import R3P10Ladder
import R3P10Cubes

/-! # R(P_10, P_10, P_10) = 18, with every certificate checked in Lean

The nine hypotheses of `K18_P10_of_certs` (`R3P10/Main.lean`) as theorems:
the seven rungs and the cover from `R3P10Ladder`, the 15,956 cubes from
`R3P10Cubes` (the generated chunk modules `R3P10Cubes.C*`, joined). Each fact
is checked by Lean's verified LRAT checker (`Std.Tactic.BVDecide.LRAT`),
evaluated natively through `Lean.ofReduceBool`.

Build with `lake build R3P10Final` after `python3 ../checks/check.py full`
has built every chunk module (about 250 CPU-hours). -/

namespace R3P10

theorem cert_k18_cubes : ∀ c ∈ finalCubes, UnsatWithPaths 18 10 (encode 18 9 ++ cubeUnits c) :=
  cubes_of_range finalCubes_length K18.all

/-- Every 3-coloring of the edges of `K_18` contains a monochromatic path
on 10 vertices, i.e. `R(P_10, P_10, P_10) ≤ 18`. -/
theorem K18_has_mono_P10 (X : Sym2 (Fin 18) → Fin 3) :
    ∃ (c : Fin 3) (p : Fin 10 → Fin 18), Function.Injective p ∧
      ∀ (i : ℕ) (h : i + 1 < 10), X s(p ⟨i, by omega⟩, p ⟨i + 1, h⟩) = c :=
  K18_P10_of_certs cert_k5p3 cert_k6p4 cert_k9p5 cert_k10p6 cert_k13p7 cert_k14p8 cert_k17p9
    cert_k18_cover cert_k18_cubes X

/-- `R(P_10, P_10, P_10) = 18`. Upper bound from the nine facts above, each
checked by Lean's LRAT checker; lower bound from the explicit coloring
`k17Col` (`R3P10/Lower.lean`), checked by the kernel. -/
theorem R3_P10_eq_18 : ramsey3Path 10 = 18 :=
  R3_P10_eq_18_of_certs cert_k5p3 cert_k6p4 cert_k9p5 cert_k10p6 cert_k13p7 cert_k14p8
    cert_k17p9 cert_k18_cover cert_k18_cubes

end R3P10

/-! The statement, unfolded to the definitions. -/

example : R3P10.ramsey3Path 10 =
    sInf {n | ∀ X : Sym2 (Fin n) → Fin 3, ∃ (c : Fin 3) (p : Fin 10 → Fin n),
      Function.Injective p ∧ ∀ (i : ℕ) (h : i + 1 < 10), X s(p ⟨i, by omega⟩, p ⟨i + 1, h⟩) = c} :=
  rfl

/-- info: 'R3P10.R3_P10_eq_18' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound] -/
#guard_msgs in #print axioms R3P10.R3_P10_eq_18

/--
info: 'R3P10.K18_has_mono_P10' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound]
-/
#guard_msgs in #print axioms R3P10.K18_has_mono_P10
