import ABC.Flow

/-!
# The first Birkhoff (twist) coefficient

The closed form of the normalisation both checkers run: write `x = p + v w + v̄ w̄` with `v` a
`λ`-eigenvector, take the 3-jet `a_jk` of `w^j w̄^k`, remove the quadratic terms and read `β`, the
`w²w̄` coefficient (the twist is `τ = −iβ/λ`).
-/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real

noncomputable section

namespace ABC

abbrev C2 := Fin 2 → ℂ

abbrev Cn (n : ℕ) := Fin n → ℂ

def jdet (f : E 2 → E 2) (p : E 2) : ℝ := LinearMap.det (fderiv ℝ f p : E 2 →ₗ[ℝ] E 2)

def jtr (f : E 2 → E 2) (p : E 2) : ℝ := LinearMap.trace ℝ (E 2) (fderiv ℝ f p : E 2 →ₗ[ℝ] E 2)

-- the real point `v w + v̄ w̄`, and its inverse (Cramer)
def ofW (v : C2) (w : ℂ) : E 2 := !₂[2 * (v 0 * w).re, 2 * (v 1 * w).re]

def toW (v : C2) (x : E 2) : ℂ :=
  ((x 0 : ℂ) * conj (v 1) - (x 1 : ℂ) * conj (v 0)) / (v 0 * conj (v 1) - v 1 * conj (v 0))

def jetPoly (a : ℕ → ℕ → ℂ) (w : ℂ) : ℂ :=
  ∑ j ∈ Finset.range 4, ∑ k ∈ Finset.range (4 - j), a j k * w ^ j * conj w ^ k

-- `a` is the 3-jet of `f` at `p` in the coordinate `w`
def IsJet3 (f : E 2 → E 2) (p : E 2) (v : C2) (a : ℕ → ℕ → ℂ) : Prop :=
  (fun w => toW v (f (p + ofW v w) - p) - jetPoly a w) =o[𝓝 0] fun w => ‖w‖ ^ 3

-- `w²w̄` coefficient after `w ↦ w + q(w)`, `q_jk = a_jk/(λ^j λ̄^k − λ)`, `λ = a 1 0`
def birkhoffBeta (a : ℕ → ℕ → ℂ) : ℂ :=
  let l := a 1 0
  let m : ℂ := ((‖l‖ ^ 2 : ℝ) : ℂ)
  a 2 1 + 2 * a 2 0 * a 1 1 / (m - l) + a 1 1 * a 2 0 / (l ^ 2 - l)
    + ((‖a 1 1‖ ^ 2 : ℝ) : ℂ) / (m - conj l) + 2 * ((‖a 0 2‖ ^ 2 : ℝ) : ℂ) / (l ^ 2 - conj l)

structure TwistData (f : E 2 → E 2) (p : E 2) (v : C2) (a : ℕ → ℕ → ℂ) : Prop where
  indep : (v 0 * conj (v 1)).im ≠ 0
  jet : IsJet3 f p v a
  fixed : a 0 0 = 0
  diag : a 0 1 = 0
  nonreal : (a 1 0).im ≠ 0
  nonres : a 1 0 ^ 2 ≠ a 1 0 ∧ a 1 0 ^ 2 ≠ conj (a 1 0)

-- first Birkhoff (twist) coefficient `τ = −iβ/λ` nonzero
def TwistNonzero (f : E 2 → E 2) (p : E 2) : Prop :=
  ∃ v a, TwistData f p v a ∧ birkhoffBeta a ≠ 0

end ABC
