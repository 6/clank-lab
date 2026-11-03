import GR22.EndpointPositional
import GR22.UnitA
import GR22.UnitE

/-! the off-by-one reflection is false, refuted in the kernel by
`h₃[h₂] = s₆ + s₄₂ + s₂₂₂`, whose `γ = 0` sequence is `(1, 1, 1)`: `b(0,0) = 1` but the
off-by-one partner `b(3,0)` is `0`. -/

namespace GR22

open MvPolynomial

/-- The Schur expansion of `h₃[h₂]`. -/
noncomputable def h3h2Coeffs : List ℕ →₀ ℚ :=
  Finsupp.single [6] 1 + Finsupp.single [4, 2] 1 + Finsupp.single [2, 2, 2] 1

lemma h3h2_expansion : SchurExpansion 6 (plethysm (complete 3) (complete 2)) h3h2Coeffs := by
  refine ⟨fun μ hμ => ?_, ?_⟩
  · have hs : μ ∈ ({[6], [4, 2], [2, 2, 2]} : Finset (List ℕ)) := by
      have := Finsupp.support_add hμ
      rcases Finset.mem_union.mp this with h | h
      · rcases Finset.mem_union.mp (Finsupp.support_add h) with h' | h'
        · simp at h'; simp [h']
        · simp at h'; simp [h']
      · simp at h; simp [h]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl <;> refine ⟨by decide, by decide, by decide⟩
  · rw [anchor_h3_h2, h3h2Coeffs, Finsupp.sum_add_index' (by simp) (by intros; simp [add_mul]),
      Finsupp.sum_add_index' (by simp) (by intros; simp [add_mul])]
    simp

theorem offByOne_false : ¬ FullEndpointOffByOne := by
  intro h
  have := h 3 2 (complete 3) h3h2Coeffs (by norm_num) le_rfl (unitE_complete_isWH 3)
    h3h2_expansion 0 0
  norm_num [hookCoeff, h3h2Coeffs] at this

end GR22
