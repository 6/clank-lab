import EKG.FiniteBase

/-! Unit tests of the definition: the first 30 terms of the sequence, as
listed in OEIS A064413, are the greedy sequence `EKG.actualA` (zero-based,
so `actualA (n-1)` is the paper's `a(n)`). In particular the two equality
cases of the theorem hold: `a(7) = 12` and `a(28) = 13`. -/
namespace EKG.FirstTerms

def value (n : ℕ) : ℕ :=
  ([1, 2, 4, 6, 3, 9, 12, 8, 10, 5, 15, 18, 14, 7, 21, 24, 16, 20, 22, 11,
    33, 27, 30, 25, 35, 28, 26, 13, 39, 36] : List ℕ)[n]?.getD 0

theorem checked_rows : ∀ n : Fin 30, 2 ≤ n.val → FiniteBase.GreedyRow value n.val := by
  decide

theorem certified : FiniteBase.CertifiedPrefix value 30 := by
  refine ⟨by decide, by decide, ?_⟩
  intro n hn hN
  exact checked_rows ⟨n, hN⟩ hn

theorem actualA_first_thirty {n : ℕ} (hn : n < 30) : actualA n = value n :=
  certified.agrees canonical n hn

/-- `a(7) = 12`: the upper bound `a(n) ≤ 12n/7` is attained at `n = 7`. -/
theorem a7 : actualA 6 = 12 := by
  rw [actualA_first_thirty (by norm_num)]; decide

/-- `a(28) = 13`: the lower bound `a(n) ≥ 13n/28` is attained at `n = 28`. -/
theorem a28 : actualA 27 = 13 := by
  rw [actualA_first_thirty (by norm_num)]; decide

end EKG.FirstTerms
