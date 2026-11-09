import ABC.Tube

/-!
# Orbits of the ABC field and the first-crossing map

Definitions for the certificate axiom (`ABC/Cert.lean`) and the KAM input (`ABC/Hand.lean`).
-/

open MeasureTheory Set Filter Topology Metric

noncomputable section

namespace ABC

/-- An integral curve of the ABC field, defined for all time. -/
def IsOrbit (γ : ℝ → E 3) : Prop := ∀ t, HasDerivAt γ (abcField (γ t)) t

/-- The point `(a₀, a₁, c)`. -/
def lift (a : E 2) (c : ℝ) : E 3 := !₂[a 0, a 1, c]

/-- The certificate box `X` of `checks/cert.txt`: centre `(6533234620664, 1727108826179)·2⁻⁴⁰`,
half-width `2⁻²⁰`, closed. -/
def certBox : Set (E 2) :=
  {a | |a 0 - 6533234620664 / 2 ^ 40| ≤ 1 / 2 ^ 20 ∧ |a 1 - 1727108826179 / 2 ^ 40| ≤ 1 / 2 ^ 20}

/-- The orbit from `(a, 0)` first reaches the plane `z = 2π` at `(b, 2π)`. -/
def ReturnsTo (a b : E 2) : Prop :=
  ∃ γ : ℝ → E 3, ∃ T : ℝ, IsOrbit γ ∧ γ 0 = lift a 0 ∧ 0 < T ∧ γ T = lift b (2 * Real.pi) ∧
    ∀ t ∈ Ico 0 T, (γ t) 2 < 2 * Real.pi

open Classical in
/-- The first-crossing map `P` from `{z = 0}` to `{z = 2π}`; the junk value `a` where no
crossing exists. -/
def retMap (a : E 2) : E 2 := if h : ∃ b, ReturnsTo a b then h.choose else a

/-- The point `r (cos ψ, sin ψ)`. -/
def polarPt (r ψ : ℝ) : E 2 := !₂[r * Real.cos ψ, r * Real.sin ψ]

/-- The closed curve `{g(ψ, s) (cos ψ, sin ψ)}`. -/
def curve (g : ℝ → ℝ → ℝ) (s : ℝ) : Set (E 2) := range fun ψ => polarPt (g ψ s) ψ

end ABC
