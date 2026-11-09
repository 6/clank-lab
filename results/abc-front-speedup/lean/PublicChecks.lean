import ABC

/-! Statement and axiom checks for the public build. -/
namespace ABC.PublicChecks

open Filter Topology

/-- The main theorem, restated with its full type. -/
example (f : ℝ → ℝ) (hf : ZlatosKPP f) (e : E 3) (he : ‖e‖ = 1) :
    ∃ ℓ : ℝ, 0 < ℓ ∧
      Tendsto (fun K => cstar (2 * Real.pi) abcField f e K / K) atTop (𝓝 ℓ) :=
  abc_kpp_linear_speedup f hf e he

/-- The field is the ABC flow with `A = B = C = 1`. -/
example (x y z : ℝ) :
    abcField !₂[x, y, z] = !₂[Real.sin z + Real.cos y, Real.sin x + Real.cos z,
      Real.sin y + Real.cos x] := rfl

/-- `cstar` is the infimum of the speeds of `L`-periodic pulsating fronts. -/
example (L : ℝ) (u : E 3 → E 3) (f : ℝ → ℝ) (e : E 3) (A : ℝ) :
    cstar L u f e A = sInf {c | ∃ T, IsPulsatingFront L u f A e c T} := rfl

/-! The main theorem rests on Lean's three standard axioms, the certified facts
(`ABC.Cert.fixed_point`) and the two cited theorems (`ABC.Poschel2001.theorem_A`,
`ABC.Zlatos2010.theorem_1_1`). -/

/--
info: 'ABC.abc_kpp_linear_speedup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Cert.fixed_point,
 Poschel2001.theorem_A,
 Zlatos2010.theorem_1_1]
-/
#guard_msgs (whitespace := lax) in
#print axioms abc_kpp_linear_speedup

/-- The KAM input uses Pöschel's theorem and not the certificate axiom (the certified facts
enter it as a hypothesis). -/
example : KAMInput := S4.kam_input

/--
info: 'ABC.S4.kam_input' depends on axioms: [propext, Classical.choice, Quot.sound, Poschel2001.theorem_A]
-/
#guard_msgs (whitespace := lax) in
#print axioms S4.kam_input

/--
info: 'ABC.vortex_tube_exists' depends on axioms: [propext, Classical.choice, Quot.sound, Cert.fixed_point]
-/
#guard_msgs (whitespace := lax) in
#print axioms vortex_tube_exists

/--
info: 'ABC.S4.twist_phi_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms S4.twist_phi_iff

end ABC.PublicChecks
