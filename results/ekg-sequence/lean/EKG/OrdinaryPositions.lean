import EKG.Span
import EKG.Asymptotic
import EKG.HoleCounting

/-! Lower position estimates for every composite EKG term. Tick values
are included. The finite hole bound is converted first to a natural
frontier bound and then to the analyst's real position-hole majorant. -/
namespace EKG

/-- Enlarge both the controlling least prime factor and its prime-count
coefficient from the missing value to the observation frontier. -/
theorem composite_lower_of_geometric_hole_bound {h e : ℕ}
    (hh : 1 < h) (hnp : ¬ h.Prime) (hbelow : h < e)
    (hgap : e-h ≤ 2*h.minFac*(13*Nat.primeCounting (Nat.sqrt h)+724)) :
    e ≤ h + 2*Nat.sqrt e*(13*Nat.primeCounting (Nat.sqrt e)+724) := by
  have hsq := Nat.minFac_sq_le_self (by omega : 0 < h) hnp
  have hfac : h.minFac ≤ Nat.sqrt e := Nat.le_sqrt'.mpr (hsq.trans hbelow.le)
  have hpi := Nat.monotone_primeCounting (Nat.sqrt_le_sqrt hbelow.le)
  have hcoefficient : 13*Nat.primeCounting (Nat.sqrt h)+724 ≤
      13*Nat.primeCounting (Nat.sqrt e)+724 := by omega
  have hproduct := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hfac) hcoefficient
  have hgap' := hgap.trans hproduct
  omega

/-- Real subtraction, with no truncation or assumption that the term
lies below the frontier. -/
theorem real_lower_of_nat_position_bound {h e : ℕ}
    (hbound : e ≤ h + 2*Nat.sqrt e*(13*Nat.primeCounting (Nat.sqrt e)+724)) :
    (e : ℝ) - (h : ℝ) ≤ positionHoleMajorant (e : ℝ) := by
  have hcast : (e : ℝ) ≤ (h : ℝ) +
      ((2*Nat.sqrt e*(13*Nat.primeCounting (Nat.sqrt e)+724) : ℕ) : ℝ) := by
    exact_mod_cast hbound
  have hmajorant := positionHoleMajorant_nat_le e
  linarith

theorem truncated_lower_of_nat_position_bound {h e : ℕ}
    (hbound : e ≤ h + 2*Nat.sqrt e*(13*Nat.primeCounting (Nat.sqrt e)+724)) :
    ((e-h : ℕ) : ℝ) ≤ positionHoleMajorant (e : ℝ) := by
  have hgap : e-h ≤ 2*Nat.sqrt e*(13*Nat.primeCounting (Nat.sqrt e)+724) := by omega
  have hcast : ((e-h : ℕ) : ℝ) ≤
      ((2*Nat.sqrt e*(13*Nat.primeCounting (Nat.sqrt e)+724) : ℕ) : ℝ) := by
    exact_mod_cast hgap
  exact hcast.trans (positionHoleMajorant_nat_le e)

/-- Natural lower bound for every composite at index at least nine.
There is no non-tick hypothesis. Before selection the current term is
missing; the below-frontier case is therefore the geometric hole bound. -/
theorem GreedySeq.composite_position_lower (s : GreedySeq) {n : ℕ}
    (hn : 9 ≤ n) (hcomp : 1 < s.a n ∧ ¬ (s.a n).Prime) :
    frontier s (n-1) ≤ s.a n +
      2*Nat.sqrt (frontier s (n-1))*
        (13*Nat.primeCounting (Nat.sqrt (frontier s (n-1)))+724) := by
  by_cases hlarge : frontier s (n-1) ≤ s.a n
  · omega
  have hbelow : s.a n < frontier s (n-1) := lt_of_not_ge hlarge
  have hfree : ¬ UsedBefore s.a (n-1+1) (s.a n) := by
    rw [show n-1+1 = n by omega]
    exact term_unused s n
  have h15 := HoleCounting.missing_composite_ge_fifteen s
    (t := n-1) (by omega) hcomp.1 hcomp.2 hbelow hfree
  have hgap := s.missing_composite_bound h15 hcomp.2 hbelow hfree
  exact composite_lower_of_geometric_hole_bound hcomp.1 hcomp.2 hbelow hgap

/-- Assembly interface in the analyst's real majorant. The subtraction
is real subtraction and covers the above-frontier case as well. -/
theorem GreedySeq.composite_position_lower_real (s : GreedySeq) {n : ℕ}
    (hn : 9 ≤ n) (hcomp : 1 < s.a n ∧ ¬ (s.a n).Prime) :
    (frontier s (n-1) : ℝ) - (s.a n : ℝ) ≤
      positionHoleMajorant (frontier s (n-1) : ℝ) :=
  real_lower_of_nat_position_bound (s.composite_position_lower hn hcomp)

theorem GreedySeq.composite_position_lower_truncated (s : GreedySeq) {n : ℕ}
    (hn : 9 ≤ n) (hcomp : 1 < s.a n ∧ ¬ (s.a n).Prime) :
    ((frontier s (n-1) - s.a n : ℕ) : ℝ) ≤
      positionHoleMajorant (frontier s (n-1) : ℝ) :=
  truncated_lower_of_nat_position_bound (s.composite_position_lower hn hcomp)

theorem actualA_composite_position_lower {n : ℕ} (hn : 9 ≤ n)
    (hcomp : 1 < actualA n ∧ ¬ (actualA n).Prime) :
    frontier canonical (n-1) ≤ actualA n +
      2*Nat.sqrt (frontier canonical (n-1))*
        (13*Nat.primeCounting (Nat.sqrt (frontier canonical (n-1)))+724) :=
  canonical.composite_position_lower hn hcomp

theorem actualA_composite_position_lower_real {n : ℕ} (hn : 9 ≤ n)
    (hcomp : 1 < actualA n ∧ ¬ (actualA n).Prime) :
    (frontier canonical (n-1) : ℝ) - (actualA n : ℝ) ≤
      positionHoleMajorant (frontier canonical (n-1) : ℝ) :=
  canonical.composite_position_lower_real hn hcomp

/-- Pointwise combination with any supplied scalar majorant bound. This
exposes the exact local hypothesis needed by a clock-rate assembly. -/
theorem GreedySeq.composite_position_lower_of_majorant_bound (s : GreedySeq)
    {n : ℕ} {B : ℝ} (hn : 9 ≤ n)
    (hcomp : 1 < s.a n ∧ ¬ (s.a n).Prime)
    (hmajorant : positionHoleMajorant (frontier s (n-1) : ℝ) ≤ B) :
    (frontier s (n-1) : ℝ) - (s.a n : ℝ) ≤ B :=
  (s.composite_position_lower_real hn hcomp).trans hmajorant

/-- The previous prefix contains exactly `n` terms, so its clock is
centered at `n`. This pointwise interface consumes only the stated clock
error and adds the unconditional composite-hole error. -/
theorem GreedySeq.composite_position_time_lower_of_clock_error (s : GreedySeq)
    {n : ℕ} {C : ℝ} (hn : 9 ≤ n)
    (hcomp : 1 < s.a n ∧ ¬ (s.a n).Prime)
    (hclock : |(frontier s (n-1) : ℝ) - (n : ℝ)| ≤ C) :
    (n : ℝ) - (s.a n : ℝ) ≤
      C + positionHoleMajorant (frontier s (n-1) : ℝ) := by
  have hclocklower := neg_le_of_abs_le hclock
  have hlower := s.composite_position_lower_real hn hcomp
  linarith

end EKG
