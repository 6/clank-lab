import Harborth.CPL
import Harborth.LiftAvg

/-! Lifting lemma, full lines, averaging over directions, and the main theorems. -/

namespace Harborth

/-- `S` contains `p` distinct elements whose sum is `0`. -/
def HasZeroSumPSubset (p : ℕ) (S : Finset (ZMod p × ZMod p)) : Prop :=
  ∃ T ⊆ S, T.card = p ∧ ∑ x ∈ T, x = 0

theorem upper_aux (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p)
    (S : Finset (ZMod p × ZMod p)) (hS : S.card = 2 * p - 1) :
    HasZeroSumPSubset p S := by
  obtain ⟨i, hi⟩ := exists_dense_dir hp S hS
  by_cases hfull : ∃ g, p ≤ ((dirOf i).fib S g).card
  · obtain ⟨g, hg⟩ := hfull
    exact full_line hp (dirOf i) S g hg
  · push Not at hfull
    obtain ⟨t, ht1, ht2, ht3, ht4⟩ := cpl hp (fun g => ((dirOf i).fib S g).card)
      (fun g => by have := hfull g; omega)
      (by
        rw [← hS]
        exact (Finset.card_eq_sum_card_fiberwise (f := (dirOf i).φ) (t := Finset.univ)
          (fun _ _ => Finset.mem_univ _)).symm)
      hi
    exact lift_core (dirOf i) S t ht1 ht2 ht3 ht4

end Harborth
