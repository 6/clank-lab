import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace FT23

/-- The inverse generator; its value off t >= 0 is immaterial. -/
def psi (t : ℝ) : ℝ := max (Real.exp (-t)) (Real.exp (-t / 2) / 4)
def phi (u : ℝ) : ℝ := max (-Real.log u) (-2 * Real.log u - Real.log 16)

/-- Positive-coordinate inverse-generator construction, with explicit zero convention. -/
def C (u v : ℝ) : ℝ := if 0 < u ∧ 0 < v then psi (phi u + phi v) else 0

def delta (F : ℝ → ℝ → ℝ) (a b d e : ℝ) : ℝ :=
  F b e - F a e - F b d + F a d

def nu1 (F : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ := v - F (1-u) v
def nu2 (F : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ := u - F u (1-v)
def nu (F : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ := u + v - 1 + F (1-u) (1-v)
def E (F : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  F u v - nu1 F u v - nu2 F u v + nu F u v

lemma E_expanded (F : ℝ → ℝ → ℝ) (u v : ℝ) :
    E F u v = F u v + F (1-u) v + F u (1-v) + F (1-u) (1-v) - 1 := by
  unfold E nu1 nu2 nu
  ring

/-- Strict admissibility on the positive interval, including the extended value at 0 by a limit. -/
structure StrictGenerator (f p : ℝ → ℝ) : Prop where
  phi_nonneg : ∀ u ∈ Ioc (0:ℝ) 1, 0 ≤ f u
  phi_continuous : ContinuousOn f (Ioc (0:ℝ) 1)
  phi_strictAnti : StrictAntiOn f (Ioc (0:ℝ) 1)
  phi_convex : ConvexOn ℝ (Ioc (0:ℝ) 1) f
  phi_one : f 1 = 0
  phi_at_zero : Tendsto f (𝓝[>] 0) atTop
  psi_continuous : ContinuousOn p (Ici (0:ℝ))
  psi_strictAnti : StrictAntiOn p (Ici (0:ℝ))
  psi_convex : ConvexOn ℝ (Ici (0:ℝ)) p
  psi_pos : ∀ t ∈ Ici (0:ℝ), 0 < p t
  psi_zero : p 0 = 1
  psi_at_infinity : Tendsto p atTop (𝓝 0)
  psi_phi : ∀ u ∈ Ioc (0:ℝ) 1, p (f u) = u
  phi_psi : ∀ t ∈ Ici (0:ℝ), f (p t) = t

/-- Closed-square copula axioms. Repeated endpoints and every zero boundary are included. -/
structure IsCopula (F : ℝ → ℝ → ℝ) : Prop where
  grounded_left : ∀ v ∈ Icc (0:ℝ) 1, F 0 v = 0
  grounded_right : ∀ u ∈ Icc (0:ℝ) 1, F u 0 = 0
  margin_left : ∀ v ∈ Icc (0:ℝ) 1, F 1 v = v
  margin_right : ∀ u ∈ Icc (0:ℝ) 1, F u 1 = u
  two_increasing : ∀ a ∈ Icc (0:ℝ) 1, ∀ b ∈ Icc (0:ℝ) 1,
    ∀ d ∈ Icc (0:ℝ) 1, ∀ e ∈ Icc (0:ℝ) 1,
    a ≤ b → d ≤ e → 0 ≤ delta F a b d e

/-- The usual unit-square codomain follows from the axioms, including boundaries. -/
theorem copula_range {F : ℝ → ℝ → ℝ} (h : IsCopula F)
    {u v : ℝ} (hu : u ∈ Icc (0:ℝ) 1) (hv : v ∈ Icc (0:ℝ) 1) :
    F u v ∈ Icc (0:ℝ) 1 := by
  have hz : (0:ℝ) ∈ Icc (0:ℝ) 1 := by norm_num
  have ho : (1:ℝ) ∈ Icc (0:ℝ) 1 := by norm_num
  have hl := h.two_increasing 0 hz u hu 0 hz v hv hu.1 hv.1
  have hh := h.two_increasing 0 hz u hu v hv 1 ho hu.1 hv.2
  have hn : 0 ≤ F u v := by
    simpa [delta, h.grounded_left v hv, h.grounded_right u hu,
      h.grounded_left 0 hz] using hl
  have hub : F u v ≤ u := by
    rw [delta, h.margin_right u hu, h.grounded_left 1 ho, h.grounded_left v hv] at hh
    linarith
  exact ⟨hn, le_trans hub hu.2⟩

/-- Stronger closed-square version of the primary's interior PQD condition. -/
def PQD (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ u ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1, u*v ≤ F u v

def ValidRect (a b d e : ℝ) : Prop :=
  0 < a ∧ a < b ∧ b < 1/2 ∧ 0 < d ∧ d < e ∧ e < 1/2

def halfSquare : Set (ℝ × ℝ) := Ioo (0:ℝ) (1/2) ×ˢ Ioo (0:ℝ) (1/2)
abbrev HalfSquare := {z : ℝ × ℝ // z ∈ halfSquare}
def rect (a b d e : ℝ) : Set (ℝ × ℝ) := Ioc a b ×ˢ Ioc d e

/-- Literal local positive Borel generating measure, expressed by its finite rectangle values.
The finiteness clause prevents toReal(top)=0 from silently representing an infinite value.
This represents “E induces a measure on the open square (0,1/2)^2”, not pointwise positivity. -/
def PrimaryPMI (F : ℝ → ℝ → ℝ) : Prop :=
  ∃ μ : Measure HalfSquare, ∀ a b d e : ℝ, ValidRect a b d e →
    μ (Subtype.val ⁻¹' rect a b d e) ≠ ⊤ ∧
    (μ (Subtype.val ⁻¹' rect a b d e)).toReal = delta (E F) a b d e

/-- Ambient necessary predicate used by the finite-rectangle contradiction. -/
def HasPositiveRectangleMeasure (F : ℝ → ℝ → ℝ) : Prop :=
  ∃ μ : Measure (ℝ × ℝ), ∀ a b d e : ℝ, ValidRect a b d e →
    μ (rect a b d e) ≠ ⊤ ∧ (μ (rect a b d e)).toReal = delta (E F) a b d e

def radius (j : ℕ) : ℝ := ((2:ℝ) ^ j)⁻¹
def leftX (j : ℕ) : ℝ := 1/4 - radius j
def rightX (j : ℕ) : ℝ := 1/4 + radius j
def leftY (j : ℕ) : ℝ := 1/12 - radius j
def rightY (j : ℕ) : ℝ := 1/12 + radius j

def AllowedNegativeRectangle : Prop := ∃ j : ℕ, 8 ≤ j ∧ j ≤ 24 ∧
  ValidRect (leftX j) (rightX j) (leftY j) (rightY j) ∧
  delta (E C) (leftX j) (rightX j) (leftY j) (rightY j) < 0

end FT23
