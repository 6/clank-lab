import BaseREhrhart.Statement
import Mathlib.Tactic

/-! The actual convex hull to nonnegative lifted coordinates. -/
noncomputable section
open scoped BigOperators
open Finset
namespace BaseREhrhart

lemma mem_hull_iff {m d : ℕ} (v : Fin m → (Fin d → ℝ)) (x : Fin d → ℝ) :
    x ∈ convexHull ℝ (Set.range v) ↔
    ∃ w : Fin m → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • v i = x := by
  classical
  constructor
  · rw [convexHull_range_eq_exists_affineCombination]
    rintro ⟨s, w, hw, hs, hx⟩
    refine ⟨fun i => if i ∈ s then w i else 0, ?_, ?_, ?_⟩
    · intro i
      dsimp only
      split_ifs with hi
      · exact hw i hi
      · exact le_rfl
    · simpa using hs
    · simpa [ite_smul, Finset.affineCombination_eq_linear_combination _ _ _ hs] using hx
  · rintro ⟨w, hw, hs, hx⟩
    exact mem_convexHull_of_exists_fintype w v hw hs (fun i => Set.mem_range_self i) hx

lemma sum_vertex {d : ℕ} (c : Fin d → ℝ) (w : Fin (d+1) → ℝ) (i : Fin d) :
    (∑ j, w j • simplexVertex c j) i = w i.succ - c i * w 0 := by
  classical
  simp [simplexVertex, Fin.sum_univ_succ, Finset.sum_apply, mul_comm, sub_eq_add_neg]
  <;> ring

/-- Every nonnegative coordinate vector is a point of the scalar image of the
literal convex hull. Zero height is handled separately inside the proof. -/
lemma dilate_hull_iff {d : ℕ} (c : Fin d → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (x : Fin d → ℝ) :
    x ∈ (fun y : Fin d → ℝ => t • y) '' convexHull ℝ (Set.range (simplexVertex c)) ↔
    ∃ μ : Fin (d+1) → ℝ, (∀ j, 0 ≤ μ j) ∧ ∑ j, μ j = t ∧
      ∀ i, x i = μ i.succ - c i * μ 0 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨w, hw, hs, hx⟩ := (mem_hull_iff _ _).mp hy
    refine ⟨fun j => t * w j, fun j => mul_nonneg ht (hw j), ?_, ?_⟩
    · rw [← Finset.mul_sum, hs, mul_one]
    · intro i
      have h := congrFun hx i
      rw [sum_vertex] at h
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← h]
      ring
  · rintro ⟨μ, hμ, hs, hx⟩
    by_cases hzero : t = 0
    · have hm : ∀ j, μ j = 0 := by
        intro j
        have hj := Finset.single_le_sum (fun j _ => hμ j) (Finset.mem_univ j)
        rw [hs, hzero] at hj
        exact le_antisymm hj (hμ j)
      have hx0 : x = 0 := by ext i; simp [hx i, hm]
      refine ⟨simplexVertex c 0, subset_convexHull ℝ _ (Set.mem_range_self 0), ?_⟩
      simp [hzero, hx0]
    · have hpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
      let w : Fin (d+1) → ℝ := fun j => μ j / t
      have hw : ∀ j, 0 ≤ w j := fun j => div_nonneg (hμ j) ht
      have hws : ∑ j, w j = 1 := by simp [w, ← Finset.sum_div, hs, hzero]
      refine ⟨∑ j, w j • simplexVertex c j, (mem_hull_iff _ _).mpr ⟨w, hw, hws, rfl⟩, ?_⟩
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, sum_vertex]
      rw [hx i]
      dsimp [w]
      field_simp

lemma mem_dilate_iff (t : ℕ) (x : Fin 5 → ℤ) :
    (fun i => (x i : ℝ)) ∈ dilate t ↔
    ∃ μ : Fin 6 → ℝ, (∀ j, 0 ≤ μ j) ∧ ∑ j, μ j = t ∧
      ∀ i, (x i : ℝ) = μ i.succ - (coefficients i : ℝ) * μ 0 :=
  dilate_hull_iff _ _ (Nat.cast_nonneg t) _

end BaseREhrhart
