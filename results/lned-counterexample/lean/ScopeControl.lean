import ScopeRadical
import Beta

namespace LNEDScope
open Polynomial LNEDPilot LNEDBeta

lemma beta_one_image_iff (f : ℚ[X]) : f ∈ VBeta 1 ↔ f.eval 0 = 0 := by
  simpa using (integer_image_iff 1 (by omega) f)

/-- Changed-endpoint control: the beta=1 image is literally the nonzero ideal (X). -/
theorem beta_one_image_eq_Xideal : VBeta 1 = ((Ideal.span {(X : ℚ[X])} : Ideal ℚ[X]) : Set ℚ[X]) := by
  ext f
  rw [beta_one_image_iff, SetLike.mem_coe, Ideal.mem_span_singleton]
  simpa only [C_0, sub_zero] using (dvd_iff_isRoot (p := f) (a := (0 : ℚ))).symm

theorem beta_one_contains_nonzero_ideal :
    ∃ J : Ideal ℚ[X], J ≠ ⊥ ∧ (J : Set ℚ[X]) ⊆ VBeta 1 := by
  refine ⟨Ideal.span {(X : ℚ[X])}, ?_, ?_⟩
  · intro hz
    have hx : (X : ℚ[X]) ∈ (Ideal.span {(X : ℚ[X])} : Ideal ℚ[X]) := Ideal.subset_span (by simp)
    rw [hz, Ideal.mem_bot] at hx
    exact X_ne_zero hx
  · rw [beta_one_image_eq_Xideal]

theorem beta_one_X_strong_radical : (X : ℚ[X]) ∈ StrongRadical (VBeta 1) := by
  intro b
  refine ⟨1, ?_⟩
  intro m hm
  apply (beta_one_image_iff _).mpr
  simp [zero_pow (show m ≠ 0 by omega)]

theorem beta_one_strong_radical_nonzero : StrongRadical (VBeta 1) ≠ {0} := by
  intro hz
  have hx := beta_one_X_strong_radical
  rw [hz, Set.mem_singleton_iff] at hx
  exact X_ne_zero hx

#print axioms beta_one_image_eq_Xideal
#print axioms beta_one_contains_nonzero_ideal
#print axioms beta_one_strong_radical_nonzero
end LNEDScope
