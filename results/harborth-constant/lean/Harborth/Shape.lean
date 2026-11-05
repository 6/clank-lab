import Mathlib
import Harborth.ShapeLarge
import Harborth.ShapeSmall

/-! Shape Lemma: every concentrated profile has an SLC witness or is exceptional.

Proof: `Harborth.ShapeAux.shape_large` (odd `p ≥ 17`, Sections 4 and 5 of the paper) and
`Harborth.ShapeAux.shape_small` (`p = 11, 13`, kernel-checked enumeration, Section 6). -/

namespace Harborth

/-- Hypotheses of the Symmetric Layer Criterion (Section 3 of the paper) for a profile `v` and depths `r`.
Layer `i + 1` is `{g | i + 1 ≤ r g}`. -/
def SLCWitness (p : ℕ) [NeZero p] (v r : ZMod p → ℕ) : Prop :=
  (∀ g, r g ≤ v g) ∧ (∀ g, r g % 2 = v g % 2) ∧
  (∑ g, ((r g : ℤ)) ^ 2 ≤ ∑ g, ((v g : ℤ) - 2) ^ 2) ∧
  p - 1 ≤ ∑ i ∈ Finset.range p, (Finset.univ.filter (fun g => i + 1 ≤ r g)).card ^ 2 / 4

/-- The three position-dependent exceptional shapes `(p-1, p-1, 1)`, `(p-1, p-2, 2)`,
`(p-1, p-3, 3)` (Section 5 of the paper). -/
def Exceptional (p : ℕ) (v : ZMod p → ℕ) : Prop :=
  ∃ a b c : ZMod p, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ v a = p - 1 ∧ v b + v c = p ∧
    1 ≤ v c ∧ v c ≤ 3 ∧ ∀ g, g ≠ a → g ≠ b → g ≠ c → v g = 0

/-- Shape Lemma (Sections 4–6 of the paper). -/
theorem shape_lemma {p : ℕ} [Fact p.Prime] (hp : 11 ≤ p) (v : ZMod p → ℕ)
    (hv : ∀ g, v g ≤ p - 1) (hsum : ∑ g, v g = 2 * p - 1)
    (hconc : 2 * p - 4 ≤ ∑ g, (v g).choose 2) :
    (∃ r : ZMod p → ℕ, SLCWitness p v r) ∨ Exceptional p v := by
  have hpr : p.Prime := Fact.out
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have h : ShapeAux.ShapeConcl (ZMod p) p v := by
    by_cases h17 : 17 ≤ p
    · have hodd : p % 2 = 1 := by have := hpr.eq_two_or_odd; omega
      exact ShapeAux.shape_large p hcard h17 hodd v hv hsum hconc
    · have h1113 : p = 11 ∨ p = 13 := by
        interval_cases p <;> first | (left; rfl) | (right; rfl) | (exfalso; norm_num at hpr)
      exact ShapeAux.shape_small p h1113 hcard v hv hsum hconc
  exact h

end Harborth
