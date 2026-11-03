import DeterministicGap
import ExpectationTail

/-! Every matrix has at most m bad middles: emptying large columns keeps every
isolated path, and the packing argument then bounds their number. -/
namespace ADG
open Finset

/-- Delete supports of size at least four; preserve the actual column order. -/
def truncateLargeColumns {m n : ℕ} (A : Matrix m n) : Matrix m n :=
  fun j => if (A j).card ≤ 3 then A j else ∅

lemma truncateLargeColumns_noLarge {m n : ℕ} (A : Matrix m n) :
    noLargeColumns (truncateLargeColumns A) := by
  intro j
  simp only [truncateLargeColumns]
  split_ifs with h
  · exact h
  · simp

lemma pathOccursAt_truncateLargeColumns {m n : ℕ} (A : Matrix m n)
    (t : PathTuple m) (left middle right : Fin n)
    (h : pathOccursAt A t left middle right) :
    pathOccursAt (truncateLargeColumns A) t left middle right := by
  have hl : truncateLargeColumns A left = A left := by
    simp [truncateLargeColumns, h.2.2.2.1, pathLeft_card]
  have hm : truncateLargeColumns A middle = A middle := by
    simp [truncateLargeColumns, h.2.2.2.2.1, pathMiddle_card]
  have hr : truncateLargeColumns A right = A right := by
    simp [truncateLargeColumns, h.2.2.2.2.2.1, pathRight_card]
  refine ⟨h.1,h.2.1,h.2.2.1,hl.trans h.2.2.2.1,
    hm.trans h.2.2.2.2.1,hr.trans h.2.2.2.2.2.1,?_⟩
  intro j hjl hjm hjr
  by_cases hc : (A j).card ≤ 3
  · simpa [truncateLargeColumns, hc] using h.2.2.2.2.2.2 j hjl hjm hjr
  · simp [truncateLargeColumns, hc, pathForbidden]

lemma badMiddles_subset_truncateLargeColumns {m n : ℕ} (A : Matrix m n) :
    badMiddles A ⊆ badMiddles (truncateLargeColumns A) := by
  classical
  intro j hj
  obtain ⟨t,l,r,h⟩ := (Finset.mem_filter.mp hj).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
    t,l,r,pathOccursAt_truncateLargeColumns A t l j r h⟩

/-- A deterministic upper bound valid on every matrix, including outside the good event. -/
theorem badMiddles_le_rows {m n : ℕ} (A : Matrix m n) : B A ≤ m := by
  have hsub : B A ≤ B (truncateLargeColumns A) :=
    Finset.card_le_card (badMiddles_subset_truncateLargeColumns A)
  have hmass := selected_exchange_mass (truncateLargeColumns A)
    (truncateLargeColumns_noLarge A)
  omega

/-- The actual bad-middle random variable satisfies the global tail theorem's bounds. -/
theorem badMiddles_real_bounds {m n : ℕ} (A : Matrix m n) :
    0 ≤ (B A : ℝ) ∧ (B A : ℝ) ≤ (m : ℝ) := by
  exact ⟨Nat.cast_nonneg _, by exact_mod_cast badMiddles_le_rows A⟩

/-- Positive expectation of the actual bad-middle count yields positive density probability. -/
theorem badMiddles_tail_lower_bound (m n : ℕ) (p : ℝ)
    (hm : 0 < m) (hp : 0 ≤ p) (hp' : p ≤ 1) (a e : ℝ) (ha : 0 ≤ a)
    (he : e ≤ matrixExpectation m n p (fun A => (B A : ℝ))) :
    (e-a)/(m : ℝ) ≤ matrixProb m n p (fun A => a ≤ (B A : ℝ)) := by
  apply matrixProb_threshold_lower_bound m n p hp hp' (fun A => (B A : ℝ))
    (m : ℝ) a e (by exact_mod_cast hm) badMiddles_real_bounds ha he

end ADG
