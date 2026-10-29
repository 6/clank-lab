import AdjacencyGeometry

namespace ADKZPricing
open Matrix Finset
noncomputable section

theorem realSign_negative_iff (x : ℝ) : realSign x = -1 ↔ x < 0 := by
  unfold realSign
  split_ifs <;> simp_all

theorem realSign_positive_iff (x : ℝ) : realSign x = 1 ↔ 0 < x := by
  unfold realSign
  split_ifs <;> simp_all
  all_goals first | linarith | exact lt_of_le_of_ne (by assumption) (Ne.symm (by assumption))

theorem realSign_sum_compatible (x y : ℝ)
    (hc : x = 0 ∨ y = 0 ∨ realSign x = realSign y) :
    realSign (x + y) = if realSign x = 0 then realSign y else realSign x := by
  rcases hc with hx | hy | he
  · simp [hx, realSign]
  · subst y
    simp only [add_zero, show realSign 0 = 0 by simp [realSign]]
    split_ifs with h
    · exact h
    · rfl
  · by_cases hx : x = 0
    · simp [hx, realSign]
    have hs : realSign x ≠ 0 := (realSign_zero_iff _).not.mpr hx
    rw [if_neg hs]
    by_cases hxn : x < 0
    · have hyn := (realSign_negative_iff y).mp (he.symm.trans ((realSign_negative_iff x).mpr hxn))
      rw [(realSign_negative_iff _).mpr (add_neg hxn hyn), (realSign_negative_iff _).mpr hxn]
    · have hxp : 0 < x := lt_of_le_of_ne (le_of_not_gt hxn) (Ne.symm hx)
      have hyp := (realSign_positive_iff y).mp (he.symm.trans ((realSign_positive_iff x).mpr hxp))
      rw [(realSign_positive_iff _).mpr (add_pos hxp hyp), (realSign_positive_iff _).mpr hxp]

theorem commuting_signs_compatible {X Y : SignVector}
    (hc : compose X Y = compose Y X) (i : Fin 80) : X i = 0 ∨ Y i = 0 ∨ X i = Y i := by
  by_cases hx : X i = 0
  · exact Or.inl hx
  by_cases hy : Y i = 0
  · exact Or.inr (Or.inl hy)
  · exact Or.inr (Or.inr (by
      have he := congrArg (fun Z : SignVector => Z i) hc
      simpa [compose, hx, hy] using he))

/-- Commuting composition of two realized covectors is realized by the
    sum of representatives. This is the actual frozen Covector predicate. -/
theorem covector_commuting_compose (A : Matrix (Fin 80) (Fin 41) ℚ)
    (X Y : SignVector) (hx : Covector A X) (hy : Covector A Y)
    (hc : compose X Y = compose Y X) : Covector A (compose X Y) := by
  obtain ⟨v, hv⟩ := hx
  obtain ⟨w, hw⟩ := hy
  refine ⟨v + w, ?_⟩
  intro i
  change compose X Y i = realSign (rowValue A (v + w) i)
  rw [rowValue_add]
  have hs : rowValue A v i = 0 ∨ rowValue A w i = 0 ∨
      realSign (rowValue A v i) = realSign (rowValue A w i) := by
    rcases commuting_signs_compatible hc i with h | h | h
    · exact Or.inl ((realSign_zero_iff _).mp ((hv i).symm.trans h))
    · exact Or.inr (Or.inl ((realSign_zero_iff _).mp ((hw i).symm.trans h)))
    · exact Or.inr (Or.inr ((hv i).symm.trans (h.trans (hw i))))
  rw [realSign_sum_compatible _ _ hs]
  simp only [compose, hv i, hw i, rowValue]

theorem compatible_ratio_nonnegative (x z : ℝ)
    (hf : realSign z = 0 ∨ realSign z = realSign x) : 0 ≤ z / x := by
  have hs := sign_face_signed_nonnegative x z hf
  by_cases hx : x = 0
  · simp [hx]
  by_cases hxn : x < 0
  · have hz : z ≤ 0 := by simpa [(realSign_negative_iff x).mpr hxn] using hs
    exact div_nonneg_of_nonpos hz hxn.le
  · have hxp : 0 < x := lt_of_le_of_ne (le_of_not_gt hxn) (Ne.symm hx)
    have hz : 0 ≤ z := by simpa [(realSign_positive_iff x).mpr hxp] using hs
    exact div_nonneg hz hxp.le

#print axioms covector_commuting_compose
#print axioms compatible_ratio_nonnegative
end
end ADKZPricing
