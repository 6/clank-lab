import ABC.Cert
import ABC.Cited.Poschel

/-! Stage 4 definitions: the KAM input, steps R1–R7 of the paper's appendix. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)

noncomputable section

namespace ABC.S4

def phi (a : E 2) : E 2 := !₂[a 0 * Real.sin (a 1) + Real.sin (a 0), a 1]

-- checker 2's literal fact: twist of `Φ ∘ P ∘ Φ⁻¹` at `Φ p`
def TwistNonzeroPhi (p : E 2) : Prop :=
  ∀ ψ : E 2 → E 2, (∀ᶠ X in 𝓝 (phi p), phi (ψ X) = X) → (∀ᶠ x in 𝓝 p, ψ (phi x) = x) →
    TwistNonzero (phi ∘ retMap ∘ ψ) (phi p)

def ofR (x : E 2) : C2 := fun i => (x i : ℂ)

def strip (s : ℝ) : Set ℂ := {t | |t.im| < s}

def polydisc (ρ : ℝ) : Set C2 := {w | ‖w‖ < ρ}

-- `J∇H`, `J = [[0,1],[-1,0]]`
def hamVF (H : C2 → ℂ) (w : C2) : C2 :=
  ![fderiv ℂ H w (Pi.single 1 1), -fderiv ℂ H w (Pi.single 0 1)]

structure IsTPHam (H : C2 → ℂ → ℂ) (ρ s : ℝ) : Prop where
  holo : DifferentiableOn ℂ (fun q : C2 × ℂ => H q.1 q.2) (polydisc ρ ×ˢ strip s)
  real : ∀ (x : E 2) (t : ℝ), ‖ofR x‖ < ρ → (H (ofR x) t).im = 0
  per : ∀ w t, H w (t + 2 * π) = H w t

def Solves (H : C2 → ℂ → ℂ) (γ : ℝ → C2) (a b : ℝ) : Prop :=
  ∀ t ∈ Icc a b, HasDerivWithinAt γ (hamVF (fun w => H w t) (γ t)) (Icc a b) t

def IsPeriodMap (H : C2 → ℂ → ℂ) (P : E 2 → E 2) (r : ℝ) : Prop :=
  ∀ x : E 2, ‖x‖ < r → ∃ γ : ℝ → C2, Solves H γ 0 (2 * π) ∧ γ 0 = ofR x ∧
    γ (2 * π) = ofR (P x)

def Bound (R : C2 → ℂ → ℂ) (ρ s C : ℝ) (k : ℕ) : Prop :=
  ∀ w ∈ polydisc ρ, ∀ t ∈ strip s, ‖R w t‖ ≤ C * ‖w‖ ^ k

def NonRes4 (ν : ℝ) : Prop := ∀ q : ℕ, 1 ≤ q → q ≤ 4 → ∀ m : ℤ, (q : ℝ) * ν ≠ m

def IsChart (h : OpenPartialHomeomorph (E 2) (E 2)) (p : E 2) (r : ℝ) : Prop :=
  h 0 = p ∧ ball (0 : E 2) r ⊆ h.source ∧ IsOpen h.source ∧
    ContDiffOn ℝ ⊤ h h.source ∧ ContDiffOn ℝ ⊤ h.symm h.target

-- `K′ = ν p + b p² + R`, `p = (w₀² + w₁²)/2`
def Kbnf (ν b : ℝ) (R : C2 → ℂ → ℂ) (w : C2) (t : ℂ) : ℂ :=
  ν / 2 * (w 0 ^ 2 + w 1 ^ 2) + b / 4 * (w 0 ^ 2 + w 1 ^ 2) ^ 2 + R w t

-- output of R1–R3; `h₀ = Φ⁻¹ ∘ (Φ p + ·) ∘ Q(0) ∘ Ψ(0)`
structure BNF (p : E 2) (ν b : ℝ) (R : C2 → ℂ → ℂ) (ρ s C : ℝ)
    (h₀ : OpenPartialHomeomorph (E 2) (E 2)) (P' : E 2 → E 2) : Prop where
  pos : 0 < ρ ∧ 0 < s ∧ s ≤ 1
  ham : IsTPHam (Kbnf ν b R) ρ s
  rem : Bound R ρ s C 5
  nonres : NonRes4 ν
  chart : IsChart h₀ p ρ
  period : IsPeriodMap (Kbnf ν b R) P' ρ
  conjP : ∀ x : E 2, ‖x‖ < ρ → retMap (h₀ x) = h₀ (P' x)

-- the body of `ABC.KAMInput` (Hand.lean), verbatim
def KAMCurves (p : E 2) (δ : ℝ) : Prop :=
  ∃ (h : OpenPartialHomeomorph (E 2) (E 2)) (ρ L : ℝ) (K : Set ℝ) (g : ℝ → ℝ → ℝ),
    0 < ρ ∧ 0 < L ∧ closedBall (0 : E 2) ρ ⊆ h.source ∧ h 0 = p ∧
    (∀ u ∈ closedBall (0 : E 2) ρ, ∀ v ∈ closedBall (0 : E 2) ρ,
      dist (h u) (h v) ≤ L * dist u v ∧ dist u v ≤ L * dist (h u) (h v)) ∧
    h '' closedBall 0 ρ ⊆ ball p δ ∧ IsCompact K ∧ 0 < MeasureTheory.volume K ∧
    (∀ s ∈ K, Continuous (fun ψ => g ψ s) ∧ (∀ ψ, g (ψ + 2 * π) s = g ψ s) ∧
      ∀ ψ, 0 < g ψ s ∧ g ψ s < ρ) ∧
    (∀ s ∈ K, ∀ s' ∈ K, ∀ ψ ψ' : ℝ,
      |s - s'| ≤ L * dist (polarPt (g ψ s) ψ) (polarPt (g ψ' s') ψ')) ∧
    ∀ s ∈ K, retMap '' (h '' curve g s) = h '' curve g s

-- R1
def phiC (q : C2) : C2 := ![q 0 * Complex.sin (q 1) + Complex.sin (q 0), q 1]

def Hraw (q : C2) (z : ℂ) : ℂ :=
  q 1 * Complex.sin z + Complex.sin (q 1) + Complex.cos (q 0) - q 0 * Complex.cos z

def zField (q : C2) (z : ℂ) : C2 :=
  ![(Complex.sin z + Complex.cos (q 1)) / (Complex.sin (q 1) + Complex.cos (q 0)),
    (Complex.sin (q 0) + Complex.cos z) / (Complex.sin (q 1) + Complex.cos (q 0))]

def symp (a b : C2) : ℂ := a 0 * b 1 - a 1 * b 0

-- R5–R6
def p0 (ν b : ℝ) (ω : C2) : ℂ := (ω 0 / ω 1 - ν) / (2 * b)

-- clockwise symplectic polar chart: `θ̇ = ∂K/∂P` for `J∇`
def polarW (P θ : ℂ) : C2 :=
  ![(2 * P) ^ (1 / 2 : ℂ) * Complex.cos θ, -((2 * P) ^ (1 / 2 : ℂ) * Complex.sin θ)]

-- `(I₀, θ₀)` = polar action-angle, `(I₁, θ₁) = (E, t)`
def pertP (ν b : ℝ) (R : C2 → ℂ → ℂ) (x : Pt 2) : ℂ :=
  x.2.2 1 * (b * x.1 0 ^ 2 + R (polarW (p0 ν b x.2.2 + x.1 0) (x.2.1 0)) (x.2.1 1))

def eNP (ν b : ℝ) (ω : C2) : ℂ := ω 1 * (ν * p0 ν b ω + b * p0 ν b ω ^ 2)

def OmegaE (ν b ε : ℝ) : Set (Fin 2 → ℝ) :=
  {ω | |ω 1 - 1| < 1 / 2 ∧ ∃ P ∈ Ioo (ε / 2) ε, ω 0 / ω 1 = ν + 2 * b * P}

def DomA (ν b ε s : ℝ) : Set (Pt 2) :=
  DO (ε ^ (5 / 4 : ℝ)) s
    (OmegaAlpha 2 (OmegaE ν b ε) (ε ^ (9 / 8 : ℝ))) (ε ^ (9 / 8 : ℝ) * s ^ (3 : ℝ))

end ABC.S4
