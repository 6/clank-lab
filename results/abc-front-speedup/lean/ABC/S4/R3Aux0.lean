import ABC.S4.PeriodMap

/-! R3 auxiliaries: shared definitions (polynomial shears, coefficient functions). -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real

noncomputable section

namespace ABC.S4.R3Aux

open ABC.S4

/-- `w₀² + w₁²` -/
def q2 (w : C2) : ℂ := w 0 ^ 2 + w 1 ^ 2

/-- the linear form `⟨u, w⟩`, `u` real -/
def lin (u : Fin 2 → ℝ) (w : C2) : ℂ := (u 0 : ℂ) * w 0 + (u 1 : ℂ) * w 1

/-- the exact time-1 map of `c(t) ⟨u, w⟩ ^ k`: `w + k c ⟨u,w⟩^(k-1) J u`, `J u = (u₁, -u₀)` -/
def shear (k : ℕ) (u : Fin 2 → ℝ) (c : ℂ → ℂ) (t : ℂ) (w : C2) : C2 :=
  ![w 0 + k * c t * lin u w ^ (k - 1) * u 1, w 1 - k * c t * lin u w ^ (k - 1) * u 0]

/-- the transformed Hamiltonian `K ∘ shear - ∂ₜc ⟨u, w⟩ ^ k` -/
def shearK (k : ℕ) (u : Fin 2 → ℝ) (c : ℂ → ℂ) (K : C2 → ℂ → ℂ) (w : C2) (t : ℂ) : ℂ :=
  K (shear k u c t w) t - deriv c t * lin u w ^ k

/-- the first-order change `{K₂, c ℓ^k} - ∂ₜ(c ℓ^k)` produced by a shear -/
def shX (k : ℕ) (u : Fin 2 → ℝ) (c : ℂ → ℂ) (ν : ℝ) (w : C2) (t : ℂ) : ℂ :=
  ν * k * c t * lin u w ^ (k - 1) * (w 0 * u 1 - w 1 * u 0) - deriv c t * lin u w ^ k

/-- polynomial of degree `≤ 4` with coefficient `a m n` of `w₀^m w₁^n` -/
def poly4 (a : ℕ → ℕ → ℂ) (w : C2) : ℂ :=
  ∑ m ∈ Finset.range 5, ∑ n ∈ Finset.range (5 - m), a m n * w 0 ^ m * w 1 ^ n

/-- holomorphic, `2π`-periodic and bounded on the strip -/
structure HolPer (g : ℂ → ℂ) (s : ℝ) : Prop where
  holo : DifferentiableOn ℂ g (strip s)
  per : ∀ t, g (t + 2 * π) = g t
  bdd : ∃ B, ∀ t ∈ strip s, ‖g t‖ ≤ B

/-- `HolPer`, and real on the real axis -/
structure CoefFn (g : ℂ → ℂ) (s : ℝ) : Prop extends HolPer g s where
  real : ∀ x : ℝ, (g x).im = 0

/-- `Ψ` carries solutions of `K'` in `polydisc r` to solutions of `K` in `polydisc R` -/
structure IsConj (K' K : C2 → ℂ → ℂ) (Ψ : ℂ → C2 → C2) (r R s : ℝ) : Prop where
  holo : DifferentiableOn ℂ (fun q : ℂ × C2 => Ψ q.1 q.2) (strip s ×ˢ polydisc r)
  maps : ∀ t ∈ strip s, ∀ w ∈ polydisc r, Ψ t w ∈ polydisc R
  real : ∀ (x : E 2) (t : ℝ), ‖ofR x‖ < r → ∃ y : E 2, Ψ t (ofR x) = ofR y
  per : ∀ t w, Ψ (t + 2 * π) w = Ψ t w
  zero : ∀ t, Ψ t 0 = 0
  lin : ∀ t, HasFDerivAt (Ψ t) (ContinuousLinearMap.id ℂ C2) 0
  sol : ∀ γ a b, Solves K' γ a b → (∀ t ∈ Icc a b, γ t ∈ polydisc r) →
    Solves K (fun t => Ψ t (γ t)) a b

/-- normalised Cauchy coefficient `(2πi)⁻¹ ∮ ζ^(-n-1) f ζ` on the circle of radius `r` -/
def cI (r : ℝ) (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  (2 * π * Complex.I)⁻¹ * ∮ ζ in C(0, r), (ζ ^ (n + 1))⁻¹ * f ζ

end ABC.S4.R3Aux
