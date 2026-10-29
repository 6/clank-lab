import PathVariation

namespace ADKZPricing
open Finset
noncomputable section

def allVisitedNegative {n : ℕ} (p : ℕ → Fin n → ℤ) (L : ℕ) : Finset (Fin n) :=
  univ.filter (fun i => ∃ j, j ≤ L ∧ p j i = -1)

/-- A genuine shared ridge of two regular closed-cell vertices spends
    exactly two sign transitions. The original zero rows are counted. -/
theorem shared_ridge_total_variation {n d : ℕ} (X Y : Fin n → ℤ)
    (hX : ∀ i, X i = -1 ∨ X i = 0 ∨ X i = 1)
    (hY : ∀ i, Y i = -1 ∨ Y i = 0 ∨ Y i = 1)
    (hc : ∀ i, X i = 0 ∨ Y i = 0 ∨ X i = Y i)
    (hzX : (univ.filter (fun i => X i = 0)).card = d)
    (hzY : (univ.filter (fun i => Y i = 0)).card = d)
    (hzXY : (univ.filter (fun i => X i = 0 ∧ Y i = 0)).card + 1 = d) :
    ∑ i, |Y i - X i| = (2 : ℤ) := by
  classical
  have he : (∑ i, |Y i - X i|) =
      (∑ i, (if X i = 0 then 1 else 0 : ℤ)) +
      (∑ i, (if Y i = 0 then 1 else 0 : ℤ)) -
      2 * (∑ i, (if X i = 0 ∧ Y i = 0 then 1 else 0 : ℤ)) := by
    simp only [← sum_add_distrib, ← sum_sub_distrib, Finset.mul_sum]
    exact sum_congr rfl (fun i _ => compatible_sign_difference (X i) (Y i) (hX i) (hY i) (hc i))
  have h1 : (∑ i, (if X i = 0 then 1 else 0 : ℤ)) =
      (univ.filter (fun i => X i = 0)).card := by simp
  have h2 : (∑ i, (if Y i = 0 then 1 else 0 : ℤ)) =
      (univ.filter (fun i => Y i = 0)).card := by simp
  have h3 : (∑ i, (if X i = 0 ∧ Y i = 0 then 1 else 0 : ℤ)) =
      (univ.filter (fun i => X i = 0 ∧ Y i = 0)).card := by simp
  rw [he, h1, h2, h3, hzX, hzY]
  omega

/-- Dimension-independent form of the primary transition argument. The
    edge hypothesis is the sum over ALL original coordinates, not a count
    after removing the exceptional facet. -/
theorem signed_path_transition_bound {n : ℕ} (p : ℕ → Fin n → ℤ) (L : ℕ)
    (hend : ∀ i, (p 0 i = 0 ∧ p L i = 1) ∨ (p 0 i = 1 ∧ p L i = 0))
    (hedge : ∀ j, j < L → ∑ i, |p (j + 1) i - p j i| ≤ (2 : ℤ)) :
    n + 2 * (allVisitedNegative p L).card ≤ 2 * L := by
  classical
  have hcoord : ∀ i : Fin n, (1 : ℤ) + (if i ∈ allVisitedNegative p L then 2 else 0) ≤
      variation (fun j => p j i) L := by
    intro i
    by_cases hi : i ∈ allVisitedNegative p L
    · obtain ⟨j, hj, hneg⟩ := (mem_filter.mp hi).2
      have hb := variation_visit_bound (fun j => p j i) L j hj
      rcases hend i with ⟨h0, hL⟩ | ⟨h0, hL⟩ <;>
        simpa [hi, h0, hL, hneg] using hb
    · have hb := variation_endpoint_bound (fun j => p j i) L
      rcases hend i with ⟨h0, hL⟩ | ⟨h0, hL⟩ <;>
        simpa [hi, h0, hL] using hb
  have hsum := Finset.sum_le_sum (s := univ) (fun i _ => hcoord i)
  have hleft : (∑ i : Fin n, ((1 : ℤ) + (if i ∈ allVisitedNegative p L then 2 else 0))) =
      n + 2 * ((allVisitedNegative p L).card : ℤ) := by
    rw [Finset.sum_add_distrib]
    simp
    ring
  have hright : (∑ i : Fin n, variation (fun j => p j i) L) ≤ 2 * (L : ℤ) := by
    unfold variation
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _j ∈ range L, (2 : ℤ) :=
        sum_le_sum (fun j hj => hedge j (mem_range.mp hj))
      _ = _ := by simp [mul_comm]
  rw [hleft] at hsum
  exact_mod_cast hsum.trans hright

/-- For the rank-21 factor, a path with at most twenty edges cannot
    visit even one negative coordinate. Consequently any such two-cell
    union path would already be a path in the central closed cell. -/
theorem short_factor_path_nonnegative (p : ℕ → Fin 40 → ℤ) (L : ℕ) (hL : L ≤ 20)
    (hend : ∀ i, (p 0 i = 0 ∧ p L i = 1) ∨ (p 0 i = 1 ∧ p L i = 0))
    (hvalues : ∀ j, j ≤ L → ∀ i, p j i = -1 ∨ p j i = 0 ∨ p j i = 1)
    (hedge : ∀ j, j < L → ∑ i, |p (j + 1) i - p j i| ≤ (2 : ℤ)) :
    ∀ j, j ≤ L → ∀ i, 0 ≤ p j i := by
  have hb := signed_path_transition_bound p L hend hedge
  have hc : (allVisitedNegative p L).card = 0 := by omega
  have he := card_eq_zero.mp hc
  intro j hj i
  rcases hvalues j hj i with hn | hz | hp
  · have hm : i ∈ allVisitedNegative p L := mem_filter.mpr ⟨mem_univ _, j, hj, hn⟩
    rw [he] at hm
    exact False.elim (not_mem_empty i hm)
  · omega
  · omega

/-- Once the central source distance and faithful cell-edge transport are
    supplied, the transition count gives the factor-union lower bound.
    It requires no neighboring-cell graph census. -/
theorem factor_union_transition_lower_bound (p : ℕ → Fin 40 → ℤ) (L : ℕ)
    (hend : ∀ i, (p 0 i = 0 ∧ p L i = 1) ∨ (p 0 i = 1 ∧ p L i = 0))
    (hvalues : ∀ j, j ≤ L → ∀ i, p j i = -1 ∨ p j i = 0 ∨ p j i = 1)
    (hedge : ∀ j, j < L → ∑ i, |p (j + 1) i - p j i| ≤ (2 : ℤ))
    (hcentral : (∀ j, j ≤ L → ∀ i, 0 ≤ p j i) → 21 ≤ L) : 21 ≤ L := by
  by_contra hn
  have hL : L ≤ 20 := by omega
  exact hn (hcentral (short_factor_path_nonnegative p L hL hend hvalues hedge))

#print axioms signed_path_transition_bound
#print axioms shared_ridge_total_variation
#print axioms short_factor_path_nonnegative
#print axioms factor_union_transition_lower_bound
end
end ADKZPricing
