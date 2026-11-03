import Endpoint

/-! Facts about the LP value. No LP optimum is replaced by a bound: all
statements concern `ADG.L`, the real infimum. -/
namespace ADG
open Finset

 theorem lpDomain_nonempty {m n : ℕ} (A : Matrix m n) (hA : feasible A) :
    (lpDomain A).Nonempty := by
  refine ⟨fun _ => 1, ?_⟩
  constructor
  · intro j; constructor <;> norm_num
  · intro i
    obtain ⟨j, hj⟩ := hA i
    exact le_trans (by simp [hj])
      (single_le_sum (fun c _ => by split_ifs <;> norm_num) (mem_univ j))

 theorem lpCosts_bddBelow {m n : ℕ} (A : Matrix m n) :
    BddBelow ((fun x : Fin n → ℝ => ∑ j, x j) '' lpDomain A) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨x,hx,rfl⟩
  exact sum_nonneg (fun j _ => (hx.1 j).1)

 theorem lp_one_le {m n : ℕ} (A : Matrix m n) (hm : 0 < m) (hA : feasible A) :
    1 ≤ L A := by
  apply le_csInf ((lpDomain_nonempty A hA).image _)
  rintro _ ⟨x,hx,rfl⟩
  refine le_trans (hx.2 ⟨0,hm⟩) ?_
  apply sum_le_sum
  intro j _
  split_ifs
  · exact le_refl _
  · exact (hx.1 j).1

 theorem lp_pos {m n : ℕ} (A : Matrix m n) (hm : 0 < m) (hA : feasible A) :
    0 < L A := lt_of_lt_of_le zero_lt_one (lp_one_le A hm hA)

 theorem lp_le_cover {m n : ℕ} (A : Matrix m n) (C : Finset (Fin n))
    (hC : ∀ i, ∃ j ∈ C, i ∈ A j) : L A ≤ C.card := by
  let x : Fin n → ℝ := fun j => if j ∈ C then 1 else 0
  have hx : x ∈ lpDomain A := by
    constructor
    · intro j; dsimp [x]; split_ifs <;> constructor <;> norm_num
    · intro i
      obtain ⟨j,hj,hij⟩ := hC i
      calc
        (1 : ℝ) = (if i ∈ A j then x j else 0) := by simp [x,hj,hij]
        _ ≤ ∑ c, if i ∈ A c then x c else 0 :=
          single_le_sum (f := fun c => if i ∈ A c then x c else 0)
            (fun c _ => by dsimp [x]; split_ifs <;> norm_num) (mem_univ j)
  calc
    L A ≤ ∑ j, x j := csInf_le (lpCosts_bddBelow A) ⟨x,hx,rfl⟩
    _ = C.card := by simp [x]

end ADG
