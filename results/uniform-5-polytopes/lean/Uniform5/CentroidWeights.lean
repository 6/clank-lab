import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-! Arithmetic of the centroid after removing one vertex. These statements
supply the negative axial point used in the corrected centroid argument. -/

namespace Uniform5

open scoped BigOperators RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [DecidableEq E]

/-- The negative axial point obtained by removing a vertex from a zero-centroid set. -/
noncomputable def erasedCentroid (V : Finset E) (v : E) : E :=
  (-1 / ((V.card : ℝ) - 1)) • v

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma erased_card_pos {V : Finset E} {v : E} (hv : v ∈ V) (hcard : 1 < V.card) :
    0 < ((V.erase v).card : ℝ) := by
  exact_mod_cast (show 0 < (V.erase v).card by rw [Finset.card_erase_of_mem hv]; omega)

/-- The negative axial point is exactly the arithmetic mean of the other vertices. -/
theorem erasedCentroid_eq_mean {V : Finset E} {v : E} (hv : v ∈ V)
    (hsum : ∑ x ∈ V, x = 0) :
    erasedCentroid V v = ((V.erase v).card : ℝ)⁻¹ • ∑ x ∈ V.erase v, x := by
  have hsum' : ∑ x ∈ V.erase v, x = -v := by
    have hh := Finset.sum_erase_add V (fun x : E => x) hv
    rw [hsum] at hh
    exact eq_neg_of_add_eq_zero_left hh
  have hcard : ((V.erase v).card : ℝ) = (V.card : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem hv, Nat.cast_sub (Finset.one_le_card.mpr ⟨v, hv⟩)]
    norm_num
  rw [hsum', hcard]
  simp [erasedCentroid, div_eq_mul_inv, neg_smul]

/-- The same identity using Mathlib's finite centre of mass with unit weights. -/
theorem erasedCentroid_eq_centerMass {V : Finset E} {v : E} (hv : v ∈ V)
    (hsum : ∑ x ∈ V, x = 0) :
    erasedCentroid V v = (V.erase v).centerMass (fun _ => (1 : ℝ)) id := by
  rw [erasedCentroid_eq_mean hv hsum]
  simp [Finset.centerMass]

/-- Positive equal weights put the negative axial point in the deleted hull. -/
theorem erasedCentroid_mem_convexHull {V : Finset E} {v : E} (hv : v ∈ V)
    (hcard : 1 < V.card) (hsum : ∑ x ∈ V, x = 0) :
    erasedCentroid V v ∈ convexHull ℝ (↑(V.erase v) : Set E) := by
  rw [erasedCentroid_eq_centerMass hv hsum]
  apply Finset.centerMass_mem_convexHull
  · intro x hx
    norm_num
  · simpa using erased_card_pos hv hcard
  · intro x hx
    exact hx

/-- A common upper bound for the axial coordinates bounds their mean. -/
theorem erasedCentroid_inner_le {V : Finset E} {v : E} (hv : v ∈ V)
    (hcard : 1 < V.card) (hsum : ∑ x ∈ V, x = 0) {h : ℝ}
    (hle : ∀ x ∈ V.erase v, ⟪x, v⟫ ≤ h) :
    ⟪erasedCentroid V v, v⟫ ≤ h := by
  rw [erasedCentroid_eq_mean hv hsum, real_inner_smul_left, sum_inner]
  rw [← div_eq_inv_mul, div_le_iff₀ (erased_card_pos hv hcard)]
  simpa [mul_comm] using Finset.sum_le_sum hle

/-- If one deleted vertex is strictly below the common bound, so is the mean. -/
theorem erasedCentroid_inner_lt {V : Finset E} {v : E} (hv : v ∈ V)
    (hcard : 1 < V.card) (hsum : ∑ x ∈ V, x = 0) {h : ℝ}
    (hle : ∀ x ∈ V.erase v, ⟪x, v⟫ ≤ h)
    (hlt : ∃ x ∈ V.erase v, ⟪x, v⟫ < h) :
    ⟪erasedCentroid V v, v⟫ < h := by
  rw [erasedCentroid_eq_mean hv hsum, real_inner_smul_left, sum_inner]
  rw [← div_eq_inv_mul, div_lt_iff₀ (erased_card_pos hv hcard)]
  simpa [mul_comm] using Finset.sum_lt_sum hle hlt

/-- If all deleted vertices lie in the same axial hyperplane, so does the mean. -/
theorem erasedCentroid_inner_eq {V : Finset E} {v : E} (hv : v ∈ V)
    (hcard : 1 < V.card) (hsum : ∑ x ∈ V, x = 0) {h : ℝ}
    (heq : ∀ x ∈ V.erase v, ⟪x, v⟫ = h) :
    ⟪erasedCentroid V v, v⟫ = h := by
  rw [erasedCentroid_eq_mean hv hsum, real_inner_smul_left, sum_inner]
  rw [Finset.sum_congr rfl heq]
  simp only [Finset.sum_const, nsmul_eq_mul]
  exact inv_mul_cancel_left₀ (ne_of_gt (erased_card_pos hv hcard)) h

end Uniform5
