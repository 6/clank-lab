import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic


noncomputable section
open scoped BigOperators ENNReal
open Set MeasureTheory
namespace BLSUnit1

/-- ALL L-subsets of Fin n; this is the source coordinate set E. -/
def Edge (n L : ℕ) := {e : Finset (Fin n) // e ∈ (Finset.univ : Finset (Fin n)).powersetCard L}
instance (n L : ℕ) : Fintype (Edge n L) := inferInstanceAs (Fintype {e : Finset (Fin n) // e ∈ (Finset.univ : Finset (Fin n)).powersetCard L})
instance (n L : ℕ) : DecidableEq (Edge n L) := inferInstanceAs (DecidableEq {e : Finset (Fin n) // e ∈ (Finset.univ : Finset (Fin n)).powersetCard L})

/-- Inclusive prefix: the current edge participates in its own denominator. -/
def inclusivePrefix {n L d : ℕ} (s : Fin d → Edge n L) (i : Fin d) : Finset (Fin n) :=
  (Finset.univ.filter (fun j : Fin d => j ≤ i)).biUnion (fun j => (s j).val)

/-- Literal source ordered-tuple polynomial, with repetitions and real division. -/
def sourcePolynomial (n L d : ℕ) (x : Edge n L → ℝ) : ℝ :=
  ∑ s : Fin d → Edge n L, ∏ i : Fin d, x (s i) / ((inclusivePrefix s i).card : ℝ)

end BLSUnit1
namespace BLSUnit2
open BLSUnit1

/-- Union of every edge of an ordered tuple, with repetitions allowed. -/
def tupleUnion {n L d : ℕ} (s : Fin d → Edge n L) : Finset (Fin n) :=
  Finset.univ.biUnion (fun i => (s i).val)

/-- Literal global-coordinate tuple weight, retaining inclusive prefixes. -/
def weight {n L d : ℕ} (x : Edge n L → ℝ) (s : Fin d → Edge n L) : ℝ :=
  ∏ i : Fin d, x (s i) / ((inclusivePrefix s i).card : ℝ)

/-- Filtered global tuple sum; every edge is contained in S iff its union is. -/
def restricted (n L d : ℕ) (S : Finset (Fin n)) (x : Edge n L → ℝ) : ℝ :=
  ∑ s : Fin d → Edge n L, if tupleUnion s ⊆ S then weight x s else 0

def rate (n L : ℕ) (S : Finset (Fin n)) (x : Edge n L → ℝ) : ℝ :=
  ∑ e : Edge n L, if e.val ⊆ S then x e else 0

/-- The deletion recurrence as a proposition. -/
def DeletionRecurrence : Prop :=
  ∀ (n L d : ℕ), 1 ≤ L → 1 ≤ d → ∀ (S : Finset (Fin n)) (x : Edge n L → ℝ),
    (S.card : ℝ) * restricted n L d S x =
      rate n L S x * restricted n L (d-1) S x +
        ∑ v ∈ S, restricted n L d (S.erase v) x

theorem supported_iff {n L d : ℕ} (S : Finset (Fin n)) (s : Fin d → Edge n L) :
    tupleUnion s ⊆ S ↔ ∀ i, (s i).val ⊆ S := by
  simp [tupleUnion]

theorem restricted_univ (n L d : ℕ) (x : Edge n L → ℝ) :
    restricted n L d Finset.univ x = sourcePolynomial n L d x := by
  simp [restricted, weight, sourcePolynomial]

theorem restricted_zero (n L : ℕ) (S : Finset (Fin n)) (x : Edge n L → ℝ) :
    restricted n L 0 S x = 1 := by
  simp [restricted, tupleUnion, weight]

theorem edge_card {n L : ℕ} (e : Edge n L) : e.val.card = L :=
  (Finset.mem_powersetCard.mp e.property).2

theorem restricted_small {n L d : ℕ} (hd : 1 ≤ d) (S : Finset (Fin n))
    (hS : S.card < L) (x : Edge n L → ℝ) : restricted n L d S x = 0 := by
  apply Finset.sum_eq_zero
  intro s hs
  have hnot : ¬ tupleUnion s ⊆ S := by
    intro h
    have he := (supported_iff S s).mp h ⟨0, by omega⟩
    have hc := Finset.card_le_card he
    rw [edge_card] at hc
    omega
  simp [hnot]

theorem union_snoc {n L d : ℕ} (s : Fin d → Edge n L) (e : Edge n L) :
    tupleUnion (Fin.snoc s e) = tupleUnion s ∪ e.val := by
  ext v
  simp [tupleUnion, Fin.exists_iff_castSucc, or_comm]

theorem prefix_last {n L d : ℕ} (s : Fin (d+1) → Edge n L) :
    inclusivePrefix s (Fin.last d) = tupleUnion s := by
  have h : (Finset.univ.filter (fun j : Fin (d+1) => j ≤ Fin.last d)) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro j hj
    exact Fin.le_last j
  simp only [inclusivePrefix, h, tupleUnion]

theorem prefix_snoc {n L d : ℕ} (s : Fin d → Edge n L) (e : Edge n L) (i : Fin d) :
    inclusivePrefix (Fin.snoc s e) i.castSucc = inclusivePrefix s i := by
  ext v
  simp only [inclusivePrefix, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨j, hj, hv⟩
    have hne : j ≠ Fin.last d := ne_of_lt (lt_of_le_of_lt hj (Fin.castSucc_lt_last i))
    obtain ⟨k, rfl⟩ := Fin.exists_castSucc_eq.mpr hne
    exact ⟨k, by simpa using hj, by simpa using hv⟩
  · rintro ⟨j, hj, hv⟩
    exact ⟨j.castSucc, by simpa using hj, by simpa using hv⟩


theorem weight_snoc {n L d : ℕ} (x : Edge n L → ℝ)
    (s : Fin d → Edge n L) (e : Edge n L) :
    weight x (Fin.snoc s e) = weight x s *
      (x e / ((tupleUnion s ∪ e.val).card : ℝ)) := by
  unfold weight
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, prefix_snoc, prefix_last, union_snoc]

theorem cancel_last {n L d : ℕ} (hL : 1 ≤ L) (x : Edge n L → ℝ)
    (s : Fin d → Edge n L) (e : Edge n L) :
    ((tupleUnion (Fin.snoc s e)).card : ℝ) * weight x (Fin.snoc s e) =
      x e * weight x s := by
  have he : 0 < e.val.card := by rw [edge_card]; omega
  have hc : 0 < (tupleUnion s ∪ e.val).card :=
    lt_of_lt_of_le he (Finset.card_le_card Finset.subset_union_right)
  have hn : ((tupleUnion s ∪ e.val).card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hc)
  rw [union_snoc, weight_snoc]
  field_simp

theorem deletion_weight {n L d : ℕ} (S : Finset (Fin n))
    (x : Edge n L → ℝ) (s : Fin d → Edge n L) :
    (∑ v ∈ S, if tupleUnion s ⊆ S.erase v then weight x s else 0) =
      if tupleUnion s ⊆ S then ((S \ tupleUnion s).card : ℝ) * weight x s else 0 := by
  by_cases h : tupleUnion s ⊆ S
  · simp only [Finset.subset_erase, h, true_and, ite_true]
    rw [← Finset.sum_filter]
    have hf : S.filter (fun v => v ∉ tupleUnion s) = S \ tupleUnion s := by
      ext v
      simp
    rw [hf]
    simp
  · simp [Finset.subset_erase, h]

theorem deletion_sum {n L d : ℕ} (S : Finset (Fin n)) (x : Edge n L → ℝ) :
    (∑ v ∈ S, restricted n L d (S.erase v) x) =
      ∑ s : Fin d → Edge n L,
        if tupleUnion s ⊆ S then ((S \ tupleUnion s).card : ℝ) * weight x s else 0 := by
  unfold restricted
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  exact deletion_weight S x s

theorem split_cardinality {n L d : ℕ} (S : Finset (Fin n)) (x : Edge n L → ℝ) :
    (S.card : ℝ) * restricted n L d S x =
      (∑ s : Fin d → Edge n L,
        if tupleUnion s ⊆ S then ((tupleUnion s).card : ℝ) * weight x s else 0) +
      ∑ v ∈ S, restricted n L d (S.erase v) x := by
  rw [deletion_sum]
  unfold restricted
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h : tupleUnion s ⊆ S
  · simp only [h, ite_true]
    have hc : ((S \ tupleUnion s).card : ℝ) + ((tupleUnion s).card : ℝ) = S.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card h
    rw [← hc]
    ring
  · simp [h]


/-- The actual tuple sum is reindexed, not replaced by a recursive definition. -/
theorem sum_tuples_succ {n L d : ℕ} (g : (Fin (d+1) → Edge n L) → ℝ) :
    (∑ t, g t) = ∑ e : Edge n L, ∑ s : Fin d → Edge n L, g (Fin.snoc s e) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (d+1) => Edge n L)).sum_comp g,
    Fintype.sum_prod_type]
  rfl

theorem weighted_sum_succ {n L d : ℕ} (hL : 1 ≤ L)
    (S : Finset (Fin n)) (x : Edge n L → ℝ) :
    (∑ t : Fin (d+1) → Edge n L,
      if tupleUnion t ⊆ S then ((tupleUnion t).card : ℝ) * weight x t else 0) =
        rate n L S x * restricted n L d S x := by
  rw [sum_tuples_succ]
  unfold rate restricted
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hu : tupleUnion (Fin.snoc s e) ⊆ S ↔ tupleUnion s ⊆ S ∧ e.val ⊆ S := by
    rw [union_snoc, Finset.union_subset_iff]
  by_cases h₁ : tupleUnion s ⊆ S <;> by_cases h₂ : e.val ⊆ S
  · simp only [hu, h₁, h₂, and_self, ite_true]
    exact cancel_last hL x s e
  · simp [hu, h₁, h₂]
  · simp [hu, h₁, h₂]
  · simp [hu, h₁, h₂]

/-- General deletion recurrence, all real coordinates, no positivity assumption. -/
theorem deletion_recurrence_succ {n L d : ℕ} (hL : 1 ≤ L)
    (S : Finset (Fin n)) (x : Edge n L → ℝ) :
    (S.card : ℝ) * restricted n L (d+1) S x =
      rate n L S x * restricted n L d S x +
        ∑ v ∈ S, restricted n L (d+1) (S.erase v) x := by
  rw [split_cardinality, weighted_sum_succ hL]

/-- The recurrence for positive degrees. -/
theorem deletion_recurrence : DeletionRecurrence := by
  intro n L d hL hd S x
  obtain ⟨k, rfl⟩ : ∃ k, d = k+1 := ⟨d-1, by omega⟩
  simpa using deletion_recurrence_succ hL S x

/-- The degree zero base is one even when S is empty. -/
theorem empty_zero (n L : ℕ) (x : Edge n L → ℝ) :
    restricted n L 0 ∅ x = 1 := restricted_zero n L ∅ x

/-- A positive degree source on an empty surviving set is zero for L≥1. -/
theorem empty_positive {n L d : ℕ} (hL : 1 ≤ L) (hd : 1 ≤ d)
    (x : Edge n L → ℝ) : restricted n L d ∅ x = 0 := by
  apply restricted_small hd
  simpa only [Finset.card_empty] using (show 0 < L by omega)

/-- No global coordinate edge survives when the surviving set is too small. -/
theorem rate_small {n L : ℕ} (S : Finset (Fin n)) (hS : S.card < L)
    (x : Edge n L → ℝ) : rate n L S x = 0 := by
  apply Finset.sum_eq_zero
  intro e he
  have hn : ¬ e.val ⊆ S := by
    intro h
    have hc := Finset.card_le_card h
    rw [edge_card] at hc
    omega
  simp [hn]


/-- Explicit deletion base at degree zero; no recurrence division is needed. -/
theorem deletion_zero (n L : ℕ) (S : Finset (Fin n)) (x : Edge n L → ℝ) :
    (∑ v ∈ S, restricted n L 0 (S.erase v) x) = (S.card : ℝ) := by
  simp [restricted_zero]

/-- Explicit small-set deletion contribution, including the empty surviving set. -/
theorem deletion_small {n L d : ℕ} (hd : 1 ≤ d) (S : Finset (Fin n))
    (hS : S.card < L) (x : Edge n L → ℝ) :
    (∑ v ∈ S, restricted n L d (S.erase v) x) = 0 := by
  apply Finset.sum_eq_zero
  intro v hv
  apply restricted_small hd
  exact lt_of_le_of_lt (Finset.card_le_card (Finset.erase_subset v S)) hS

end BLSUnit2
