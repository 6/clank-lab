import Greedy

/-! An isolated middle with the smallest index is chosen by Greedy; small
control matrices. -/
namespace ADG
open Finset

/-- The recursive tie rule picks the least-index maximizing entry in an increasing list. -/
lemma best_leftmost {m n : ℕ} (A : Matrix m n) (U : Finset (Fin m))
    (l : List (Fin n)) (hs : l.Pairwise (· < ·)) (j : Fin n)
    (hb : best A U l = some j) (t : Fin n) (ht : t ∈ l)
    (hg : gain A U j ≤ gain A U t) : j ≤ t := by
  induction l generalizing j with
  | nil => simp at ht
  | cons a l ih =>
    have hsort := List.pairwise_cons.mp hs
    simp only [best] at hb
    cases htail : best A U l with
    | none =>
      simp only [htail] at hb
      cases hb
      rcases List.mem_cons.mp ht with rfl | ht
      · exact le_rfl
      · exact le_of_lt (hsort.1 t ht)
    | some b =>
      simp only [htail] at hb
      split at hb
      · cases hb
        rcases List.mem_cons.mp ht with rfl | ht
        · exact le_rfl
        · exact le_of_lt (hsort.1 t ht)
      · rename_i hab
        cases hb
        rcases List.mem_cons.mp ht with rfl | ht
        · omega
        · exact ih hsort.2 j htail ht hg

/-- An isolated earliest middle is chosen by the actual full greedy trace.
The isolation premise lists all size-three columns touching P; no trace is assumed. -/
theorem isolated_middle_triple_mem_trace {m n : ℕ} (A : Matrix m n)
    (hn : noLargeColumns A) (P : Finset (Fin m)) (middle left right : Fin n)
    (hcard : (A middle).card = 3) (hsub : A middle ⊆ P)
    (hml : middle < left) (hmr : middle < right)
    (hiso : ∀ j, (A j).card = 3 → ¬ Disjoint (A j) P →
      j = middle ∨ j = left ∨ j = right)
    (fuel : ℕ) (U : Finset (Fin m)) (hfu : U.card ≤ fuel) (hP : P ⊆ U) :
    (middle, 3) ∈ trace A fuel U := by
  induction fuel generalizing U with
  | zero =>
    have hle : 3 ≤ U.card := by
      rw [← hcard]
      exact Finset.card_le_card (hsub.trans hP)
    omega
  | succ fuel ih =>
    have hgain : gain A U middle = 3 := by
      simp only [gain]
      rw [Finset.inter_eq_right.mpr (hsub.trans hP), hcard]
    have hu : U ≠ ∅ := by
      intro he
      simpa [he, gain] using hgain
    obtain ⟨j, hb⟩ : ∃ j, best A U (List.finRange n) = some j := by
      cases hb : best A U (List.finRange n) with
      | none =>
        have he := (best_none_iff A U _).mp hb
        have hm : middle ∈ List.finRange n := List.mem_finRange middle
        simpa [he] using hm
      | some j => exact ⟨j, rfl⟩
    have hg : gain A U j = 3 := by
      have hmax := (best_mem_max A U _ j hb).2 middle (List.mem_finRange middle)
      have hupper := (gain_le_column A U j).trans (hn j)
      omega
    have hjm : j ≤ middle := best_leftmost A U _ (List.pairwise_lt_finRange n)
      j hb middle (List.mem_finRange middle) (by omega)
    have heq : trace A (fuel+1) U = (j, 3) :: trace A fuel (U \ A j) := by
      simp [trace, hu, hb, hg]
    by_cases hj : j = middle
    · simp [heq, hj]
    have hdis : Disjoint (A j) P := by
      by_contra hd
      have hcj : (A j).card = 3 := by
        have hlow := gain_le_column A U j
        have hupp := hn j
        omega
      rcases hiso j hcj hd with hj' | hj' | hj'
      · exact hj hj'
      · subst j; omega
      · subst j; omega
    have hPres : P ⊆ U \ A j := by
      intro i hi
      exact Finset.mem_sdiff.mpr ⟨hP hi, fun ha => (Finset.disjoint_left.mp hdis) ha hi⟩
    have hmass : (U \ A j).card + gain A U j = U.card :=
      Finset.card_sdiff_add_card_inter U (A j)
    have hres : (U \ A j).card ≤ fuel := by omega
    have him := ih (U \ A j) hres hPres
    simp only [heq, List.mem_cons]
    exact Or.inr him

/-- Specialization of isolated-middle selection to the endpoint's actual m-fuel trace. -/
theorem isolated_middle_triple_mem_greedy {m n : ℕ} (A : Matrix m n)
    (hn : noLargeColumns A) (P : Finset (Fin m)) (middle left right : Fin n)
    (hcard : (A middle).card = 3) (hsub : A middle ⊆ P)
    (hml : middle < left) (hmr : middle < right)
    (hiso : ∀ j, (A j).card = 3 → ¬ Disjoint (A j) P →
      j = middle ∨ j = left ∨ j = right) :
    (middle, 3) ∈ greedyTrace A := by
  exact isolated_middle_triple_mem_trace A hn P middle left right hcard hsub hml hmr hiso
    m univ (by simp) (Finset.subset_univ P)

/-- One genuine seven-row loose path followed by every ordered exact pair. -/
def onePathControl : Matrix 7 52 := fun j =>
  if j.val = 0 then {2,3,4} else
  if j.val = 1 then {0,1,2} else
  if j.val = 2 then {4,5,6} else
    {⟨((j.val-3)/7)%7, Nat.mod_lt _ (by omega)⟩,
     ⟨(j.val-3)%7, Nat.mod_lt _ (by omega)⟩}

/-- Two disjoint genuine seven-row loose paths, followed by every ordered exact pair. -/
def twoPathControl : Matrix 14 202 := fun j =>
  if j.val = 0 then {2,3,4} else
  if j.val = 1 then {0,1,2} else
  if j.val = 2 then {4,5,6} else
  if j.val = 3 then {9,10,11} else
  if j.val = 4 then {7,8,9} else
  if j.val = 5 then {11,12,13} else
    {⟨((j.val-6)/14)%14, Nat.mod_lt _ (by omega)⟩,
     ⟨(j.val-6)%14, Nat.mod_lt _ (by omega)⟩}

def onePathCover : Finset (Fin 52) := {1,2,6}
def twoPathCover : Finset (Fin 202) := {1,2,4,5,58}

def coversBy {m n : ℕ} (A : Matrix m n) (C : Finset (Fin n)) : Prop :=
  ∀ i, ∃ j ∈ C, i ∈ A j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem one_path_greedy_control : G onePathControl = 3 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem two_path_greedy_control : G twoPathControl = 6 := by decide

theorem one_path_cover_control : onePathCover.card = 3 ∧ coversBy onePathControl onePathCover := by
  unfold coversBy
  decide
theorem two_path_cover_control : twoPathCover.card = 5 ∧ coversBy twoPathControl twoPathCover := by
  unfold coversBy
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem one_path_good_control : noLargeColumns onePathControl ∧ allExactPairs onePathControl := by
  unfold noLargeColumns allExactPairs
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem two_path_good_control : noLargeColumns twoPathControl ∧ allExactPairs twoPathControl := by
  unfold noLargeColumns allExactPairs
  decide

end ADG
