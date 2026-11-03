import Mathlib


noncomputable section
open Set MeasureTheory
namespace Geneson

abbrev Plane := ℝ × ℝ

def X (R : Set Plane) : Set ℝ := Prod.fst '' R

def Y (R : Set Plane) : Set ℝ := Prod.snd '' R

/-- The source's projection-domain, projection-codomain, ratio definition. -/
def Contains (R S : Set Plane) : Prop :=
  ∃ (f : X R → X S) (g : Y R → Y S),
    (∀ x x' : X R, (x : ℝ) < x' →
      1 ≤ ((f x' : ℝ) - f x) / ((x' : ℝ) - x)) ∧
    (∀ y y' : Y R, (y : ℝ) < y' →
      1 ≤ ((g y' : ℝ) - g y) / ((y' : ℝ) - y)) ∧
    ∀ (p : R),
      ((f ⟨p.1.1, ⟨p.1, p.2, rfl⟩⟩ : ℝ),
       (g ⟨p.1.2, ⟨p.1, p.2, rfl⟩⟩ : ℝ)) ∈ S

def Square (n : ℝ) : Set Plane := Icc 0 n ×ˢ Icc 0 n

def Area (S : Set Plane) : ℝ := (volume S).toReal

/-- Ambient openness in ℝ × ℝ, and the source's real supremum. -/
def opx (n : ℝ) (R : Set Plane) : ℝ :=
  sSup {a : ℝ | ∃ S : Set Plane,
    IsOpen S ∧ S ⊆ Square n ∧ ¬ Contains R S ∧ a = Area S}

/-- The full endpoint; this proposition is not a theorem assertion. -/
def Conjecture63 : Prop :=
  ∀ (n : ℝ), 0 < n → ∀ (P Q : Set Plane) (c d : ℝ),
    (c,d) ∈ P → (c,d) ∈ Q →
    (∀ p ∈ P, p.1 ≤ c ∧ p.2 ≤ d) →
    (∀ q ∈ Q, c ≤ q.1 ∧ d ≤ q.2) →
    opx n (P ∪ Q) ≤ opx n P + opx n Q

/-- Difference expansion is imposed only on the indicated projection domain. -/
def Expands {D : Set ℝ} (f : D → ℝ) : Prop :=
  ∀ x y : D, (x : ℝ) ≤ y → (y : ℝ) - x ≤ f y - f x

abbrev Maps (R : Set Plane) := (X R → ℝ) × (Y R → ℝ)

def ImagePoint {R : Set Plane} (w : Maps R) (p : R) : Plane :=
  (w.1 ⟨p.1.1, ⟨p.1, p.2, rfl⟩⟩,
   w.2 ⟨p.1.2, ⟨p.1, p.2, rfl⟩⟩)

def IsWitness (R S : Set Plane) (w : Maps R) : Prop :=
  Expands w.1 ∧ Expands w.2 ∧ ∀ p : R, ImagePoint w p ∈ S

def HasCopy (R S : Set Plane) : Prop := ∃ w : Maps R, IsWitness R S w

end Geneson
