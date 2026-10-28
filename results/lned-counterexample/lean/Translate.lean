import Half

namespace LNEDBeta
open Polynomial LNEDPilot

noncomputable def trans (t : ℚ) : ℚ[X] ≃ₐ[ℚ] ℚ[X] := algEquivAevalXAddC t
lemma trans_apply (t : ℚ) (f : ℚ[X]) : trans t f = f.comp (X + C t) := by
  simp [trans, algEquivAevalXAddC_apply, comp_eq_aeval]
lemma trans_inverse (t : ℚ) (f : ℚ[X]) : trans (-t) (trans t f) = f := by
  rw [show trans (-t) = (trans t).symm by exact (algEquivAevalXAddC_symm t).symm]
  exact (trans t).symm_apply_apply f

/-- The signed symmetry endpoints. -/
def NegativeHalfEndpoint : Prop := ∀ r : ℕ,
  ¬ TwoSidedMathieu (VBeta (-((r : ℚ) + 1 / 2)))
def NegativeIntegerEndpoint : Prop := ∀ N : ℕ, 0 < N →
  TwoSidedMathieu (VBeta (-(N : ℚ)))

lemma delta_trans (t : ℚ) (f : ℚ[X]) : delta (trans t f) = trans t (delta f) := by
  simp only [trans_apply, delta, phi, sub_comp, comp_assoc]
  congr 1
  congr 1
  simp only [add_comp, X_comp, C_comp, one_comp]
  ring

lemma trans_ideal (t : ℚ) (ht : t ≠ 0) (f : ℚ[X]) :
    f ∈ IBeta t ↔ trans t f ∈ IBeta (-t) := by
  rw [mem_IBeta_iff t ht, mem_IBeta_iff (-t) (neg_ne_zero.mpr ht)]
  simp only [trans_apply, eval_comp, eval_add, eval_X, eval_C, zero_add, neg_add_cancel]
  exact and_comm

lemma trans_image_forward (t : ℚ) (ht : t ≠ 0) (f : ℚ[X])
    (hf : f ∈ VBeta t) : trans t f ∈ VBeta (-t) := by
  obtain ⟨g, hg, rfl⟩ := hf
  exact ⟨trans t g, (trans_ideal t ht g).mp hg, delta_trans t g⟩

theorem trans_image_iff (t : ℚ) (ht : t ≠ 0) (f : ℚ[X]) :
    f ∈ VBeta t ↔ trans t f ∈ VBeta (-t) := by
  constructor
  · exact trans_image_forward t ht f
  · intro hf
    have hg := trans_image_forward (-t) (neg_ne_zero.mpr ht) (trans t f) hf
    simpa only [neg_neg, trans_inverse] using hg

lemma mathieu_transport (S W : Set ℚ[X]) (e : ℚ[X] ≃ₐ[ℚ] ℚ[X])
    (he : ∀ f, f ∈ S ↔ e f ∈ W) (hS : TwoSidedMathieu S) : TwoSidedMathieu W := by
  intro a ha b c
  have hpow : ∀ m : ℕ, 1 ≤ m → e.symm a ^ m ∈ S := by
    intro m hm
    apply (he _).mpr
    simpa only [map_pow, AlgEquiv.apply_symm_apply] using ha m hm
  obtain ⟨N, hN⟩ := hS (e.symm a) hpow (e.symm b) (e.symm c)
  refine ⟨N, ?_⟩
  intro m hm
  have h := (he _).mp (hN m hm)
  simpa only [map_mul, map_pow, AlgEquiv.apply_symm_apply] using h

theorem mathieu_neg_iff (t : ℚ) (ht : t ≠ 0) :
    TwoSidedMathieu (VBeta t) ↔ TwoSidedMathieu (VBeta (-t)) := by
  constructor
  · exact mathieu_transport _ _ (trans t) (trans_image_iff t ht)
  · intro h
    have hn := mathieu_transport _ _ (trans (-t))
      (trans_image_iff (-t) (neg_ne_zero.mpr ht)) h
    simpa only [neg_neg] using hn

theorem all_negative_half_not_mathieu : NegativeHalfEndpoint := by
  intro r h
  have ht : (r : ℚ) + 1 / 2 ≠ 0 := by positivity
  exact all_positive_half_not_mathieu r ((mathieu_neg_iff _ ht).mpr h)

theorem all_negative_integer_mathieu : NegativeIntegerEndpoint := by
  intro N hN
  have ht : (N : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  exact (mathieu_neg_iff _ ht).mp (positive_integer_mathieu N hN)

/-- Explicit translated witnesses, including the transported multiplier. -/
theorem negative_half_witness (r : ℕ) :
    (∀ m : ℕ, 1 ≤ m → (trans ((r : ℚ) + 1 / 2) (P r)) ^ m ∈
      VBeta (-((r : ℚ) + 1 / 2))) ∧
    (∀ m : ℕ, 1 ≤ m → (X + C ((r : ℚ) + 1 / 2)) *
      (trans ((r : ℚ) + 1 / 2) (P r)) ^ m ∉ VBeta (-((r : ℚ) + 1 / 2))) := by
  have ht : (r : ℚ) + 1 / 2 ≠ 0 := by positivity
  constructor
  · intro m hm
    have h := (trans_image_iff _ ht (P r ^ m)).mp ((half_witness_all r).1 m hm)
    simpa only [map_pow] using h
  · intro m hm hin
    apply (half_witness_all r).2 m hm
    apply (trans_image_iff _ ht _).mpr
    simpa only [map_mul, map_pow, trans_apply, X_comp] using hin

#print axioms all_negative_half_not_mathieu
#print axioms all_negative_integer_mathieu
#print axioms negative_half_witness
end LNEDBeta
