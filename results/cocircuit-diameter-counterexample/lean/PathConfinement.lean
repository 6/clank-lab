import PathVariation

namespace ADKZPricing
open Finset
noncomputable section

def CentralSigns (X : SignVector) : Prop := ∀ i, 0 ≤ X i

def NeighborSigns (e : Fin 80) (X : SignVector) : Prop :=
  X e ≤ 0 ∧ ∀ i, i ≠ e → 0 ≤ X i

/-- These are TWO CLOSED cell sign cones. Their shared facet remains in
    both; no inequality or shared vertex/edge is deleted or merged. -/
theorem two_cell_vertex {e : Fin 80} {X : SignVector}
    (h : ∀ i, i ≠ e → 0 ≤ X i) : CentralSigns X ∨ NeighborSigns e X := by
  by_cases he : 0 ≤ X e
  · left
    intro i
    by_cases hi : i = e
    · simpa [hi] using he
    · exact h i hi
  · right
    exact ⟨le_of_not_ge he, h⟩

/-- A compatible full-graph edge in the union belongs to at least one
    of the two closed cells, including edges on their common facet. -/
theorem two_cell_edge {e : Fin 80} {X Y : SignVector}
    (hX : ∀ i, i ≠ e → 0 ≤ X i) (hY : ∀ i, i ≠ e → 0 ≤ Y i)
    (hc : compose X Y = compose Y X) :
    (CentralSigns X ∧ CentralSigns Y) ∨ (NeighborSigns e X ∧ NeighborSigns e Y) := by
  have hp : X e = 0 ∨ Y e = 0 ∨ X e = Y e := commuting_signs_compatible hc e
  by_cases hxe : X e ≤ 0
  · by_cases hye : Y e ≤ 0
    · exact Or.inr ⟨⟨hxe, hX⟩, ⟨hye, hY⟩⟩
    · have hypos : 0 < Y e := lt_of_not_ge hye
      have hx0 : X e = 0 := by rcases hp with h | h | h <;> omega
      left
      constructor
      · intro i
        by_cases hi : i = e
        · simp [hi, hx0]
        · exact hX i hi
      · intro i
        by_cases hi : i = e
        · simpa [hi] using hypos.le
        · exact hY i hi
  · have hxpos : 0 < X e := lt_of_not_ge hxe
    have hypos : 0 ≤ Y e := by rcases hp with h | h | h <;> omega
    left
    constructor
    · intro i
      by_cases hi : i = e
      · simpa [hi] using hxpos.le
      · exact hX i hi
    · intro i
      by_cases hi : i = e
      · simpa [hi] using hypos
      · exact hY i hi

/-- A full path of length at most 41 between the frozen complementary
    endpoints stays in one FIXED pair of closed star cells. The exceptional
    row is fixed for the entire path, not chosen separately at each edge. -/
theorem finite_path_two_cell_confinement (A : Matrix (Fin 80) (Fin 41) ℚ)
    (hu : Uniform A) (L : ℕ) (hL : L ≤ 41) (p : Fin (L + 1) → SignVector)
    (hend : Complementary (p 0) (p (Fin.last L)))
    (hv : ∀ k, Cocircuit A (p k))
    (he : ∀ k : Fin L, Adjacent A (p k.castSucc) (p k.succ)) :
    ∃ e : Fin 80,
      (∀ k, CentralSigns (p k) ∨ NeighborSigns e (p k)) ∧
      (∀ k : Fin L,
        (CentralSigns (p k.castSucc) ∧ CentralSigns (p k.succ)) ∨
        (NeighborSigns e (p k.castSucc) ∧ NeighborSigns e (p k.succ))) := by
  classical
  let q : ℕ → SignVector := fun j => p ⟨min j L, by omega⟩
  have hq (j : Fin (L + 1)) : q j.val = p j := by
    dsimp only [q]
    apply congrArg p
    apply Fin.ext
    exact min_eq_left (by omega)
  have hendq : Complementary (q 0) (q L) := by
    have h0 := hq 0
    have hlast := hq (Fin.last L)
    change q 0 = p 0 at h0
    change q L = p (Fin.last L) at hlast
    rw [h0, hlast]
    exact hend
  have heq : ∀ j, j < L → Adjacent A (q j) (q (j + 1)) := by
    intro j hj
    let k : Fin L := ⟨j, hj⟩
    change Adjacent A (q k.castSucc.val) (q k.succ.val)
    rw [hq, hq]
    exact he k
  have hc := full_path_transition_count A hu q L hendq heq
  have hneg : (visitedNegative q L).card ≤ 1 := by omega
  obtain ⟨e, hexc⟩ : ∃ e : Fin 80, ∀ i ∈ visitedNegative q L, i = e := by
    by_cases hn : (visitedNegative q L).Nonempty
    · obtain ⟨e, he⟩ := hn
      exact ⟨e, fun i hi => (card_le_one.mp hneg) i hi e he⟩
    · refine ⟨0, ?_⟩
      intro i hi
      exact (hn ⟨i, hi⟩).elim
  have hnonneg (k : Fin (L + 1)) (i : Fin 80) (hi : i ≠ e) : 0 ≤ p k i := by
    rcases covector_sign_cases A (p k) (hv k).1 i with hn | hz | hp
    · have hm : i ∈ visitedNegative q L := by
        apply mem_filter.mpr
        refine ⟨mem_univ _, k.val, by omega, ?_⟩
        rw [hq]
        exact hn
      exact (hi (hexc i hm)).elim
    · simp [hz]
    · simp [hp]
  refine ⟨e, fun k => two_cell_vertex (hnonneg k), ?_⟩
  intro k
  exact two_cell_edge (hnonneg k.castSucc) (hnonneg k.succ) (he k).2.2.2.1

/-- Direct consequence for the exact frozen ShortWalk definition. -/
theorem short_walk_two_cell_confinement (A : Matrix (Fin 80) (Fin 41) ℚ)
    (hu : Uniform A) (X Y : SignVector) (hcomp : Complementary X Y)
    (hw : ShortWalk A X Y) :
    ∃ L : ℕ, L ≤ 41 ∧ ∃ p : Fin (L + 1) → SignVector,
      p 0 = X ∧ p (Fin.last L) = Y ∧
      (∀ k, Cocircuit A (p k)) ∧
      (∀ k : Fin L, Adjacent A (p k.castSucc) (p k.succ)) ∧
      ∃ e : Fin 80, (∀ k, CentralSigns (p k) ∨ NeighborSigns e (p k)) ∧
        (∀ k : Fin L,
          (CentralSigns (p k.castSucc) ∧ CentralSigns (p k.succ)) ∨
          (NeighborSigns e (p k.castSucc) ∧ NeighborSigns e (p k.succ))) := by
  obtain ⟨L, hL, p, h0, hlast, hv, he⟩ := hw
  refine ⟨L, hL, p, h0, hlast, hv, he, ?_⟩
  exact finite_path_two_cell_confinement A hu L hL p (by simpa only [h0, hlast] using hcomp) hv he

#print axioms two_cell_edge
#print axioms finite_path_two_cell_confinement
#print axioms short_walk_two_cell_confinement
end
end ADKZPricing
