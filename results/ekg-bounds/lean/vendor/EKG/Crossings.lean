import EKG.Basic
import Mathlib.Data.Finset.Card

namespace EKG

def above (a : ℕ → ℕ) (X n : ℕ) : ℕ := if X ≤ a n then 1 else 0

def upCount (a : ℕ → ℕ) (X : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => upCount a X n + if a n < X ∧ X ≤ a (n + 1) then 1 else 0

def downCount (a : ℕ → ℕ) (X : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => downCount a X n + if X ≤ a n ∧ a (n + 1) < X then 1 else 0

theorem crossing_balance (a : ℕ → ℕ) (X n : ℕ) :
    upCount a X n + above a X 0 = downCount a X n + above a X n := by
  induction n with
  | zero => simp [upCount, downCount]
  | succ n ih =>
    simp only [upCount, downCount]
    by_cases h : X ≤ a n <;> by_cases h' : X ≤ a (n + 1)
    all_goals simp [above, h, h', Nat.not_lt_of_ge, Nat.lt_of_not_ge] at *
    all_goals omega

theorem downCount_le_upCount (a : ℕ → ℕ) (X n : ℕ) (hstart : a 0 < X) :
    downCount a X n ≤ upCount a X n := by
  have h := crossing_balance a X n
  have hzero : above a X 0 = 0 := by simp [above, Nat.not_le_of_lt hstart]
  rw [hzero] at h
  omega

/-- Direct consequence of the actual greedy rule; no crossing assumption. -/
theorem smaller_multiple_used (s : GreedySeq) {n q m : ℕ}
    (hn : 2 ≤ n) (hq : q.Prime) (hqb : q ∣ s.a (n-1))
    (hm : 0 < m) (hqm : q ∣ m) (hlt : m < s.a n) : UsedBefore s.a n m := by
  by_contra hfree
  have := s.minimal n hn m hm hfree ⟨q, hq, hqb, hqm⟩
  omega

end EKG
