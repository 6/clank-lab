import EKG.OrdinaryPositions
import EKG.HoleCounting

/-! Unconditional bridge from the geometric missing-composite theorem to
the real lower position estimate. Every composite is covered, including
tick values; no non-tick or rate hypothesis is required. -/
namespace EKG

/-- The actual selected term is absent from the preceding prefix. -/
theorem GreedySeq.selected_term_missing_from_previous_prefix (s : GreedySeq)
    {n : ℕ} (hn : 1 ≤ n) : ¬ UsedBefore s.a (n-1+1) (s.a n) := by
  rw [show n-1+1 = n by omega]
  exact term_unused s n

/-- Natural version of the composite-position bridge. -/
theorem GreedySeq.composite_positions_lower_nat (s : GreedySeq) {n : ℕ}
    (hn : 9 ≤ n) (hh : 1 < s.a n) (hnp : ¬ (s.a n).Prime) :
    frontier s (n-1) ≤ s.a n +
      2*Nat.sqrt (frontier s (n-1))*
        (13*Nat.primeCounting (Nat.sqrt (frontier s (n-1)))+724) := by
  by_cases hlarge : frontier s (n-1) ≤ s.a n
  · omega
  have hbelow : s.a n < frontier s (n-1) := lt_of_not_ge hlarge
  have hfree := s.selected_term_missing_from_previous_prefix (by omega : 1 ≤ n)
  have h15 := HoleCounting.missing_composite_ge_fifteen s
    (t := n-1) (by omega) hh hnp hbelow hfree
  have hhole := s.missing_composite_bound h15 hnp hbelow hfree
  exact composite_lower_of_geometric_hole_bound hh hnp hbelow hhole

/-- Required assembly interface: real lower distance from the previous
frontier is bounded by the analyst's position-hole majorant. -/
theorem GreedySeq.composite_positions_lower_real (s : GreedySeq) {n : ℕ}
    (hn : 9 ≤ n) (hh : 1 < s.a n) (hnp : ¬ (s.a n).Prime) :
    (frontier s (n-1) : ℝ) - (s.a n : ℝ) ≤
      positionHoleMajorant (frontier s (n-1) : ℝ) :=
  real_lower_of_nat_position_bound (s.composite_positions_lower_nat hn hh hnp)

theorem actualA_composite_positions_lower_real {n : ℕ} (hn : 9 ≤ n)
    (hh : 1 < actualA n) (hnp : ¬ (actualA n).Prime) :
    (frontier canonical (n-1) : ℝ) - (actualA n : ℝ) ≤
      positionHoleMajorant (frontier canonical (n-1) : ℝ) :=
  canonical.composite_positions_lower_real hn hh hnp

/-- Exact export consumed by MainRate. -/
theorem composite_position_lower (s : GreedySeq) {n : ℕ}
    (hn : 9 ≤ n) (hbig : 1 < s.a n) (hnp : ¬ (s.a n).Prime) :
    (frontier s (n-1) : ℝ) - (s.a n : ℝ) ≤
      positionHoleMajorant (frontier s (n-1) : ℝ) :=
  s.composite_positions_lower_real hn hbig hnp

/-- Pointwise transfer to the position clock. The prefix at time `n-1`
has exactly `n` entries, explaining the time center in the hypothesis. -/
theorem GreedySeq.composite_positions_time_lower (s : GreedySeq)
    {n : ℕ} {B : ℝ} (hn : 9 ≤ n) (hh : 1 < s.a n)
    (hnp : ¬ (s.a n).Prime)
    (hclock : |(frontier s (n-1) : ℝ) - (n : ℝ)| ≤ B) :
    (n : ℝ) - (s.a n : ℝ) ≤
      B + positionHoleMajorant (frontier s (n-1) : ℝ) := by
  have hclocklower := neg_le_of_abs_le hclock
  have hposition := s.composite_positions_lower_real hn hh hnp
  linarith

end EKG
