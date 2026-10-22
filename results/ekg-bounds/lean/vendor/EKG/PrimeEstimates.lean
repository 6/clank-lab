import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Unconditional analytic estimates. These use only mathlib's proved
Chebyshev bound; no EKG combinatorial statement or prime number theorem
is a hypothesis. All real prime counts mean primes at most the floor. -/
namespace EKG

open Real Filter Asymptotics
open scoped Topology

noncomputable def realPrimeCount (x : ℝ) : ℝ := Nat.primeCounting ⌊x⌋₊
noncomputable def sqrtPrimeCount (x : ℝ) : ℝ := realPrimeCount (Real.sqrt x)
noncomputable def logRate (x : ℝ) : ℝ := x / Real.log x
noncomputable def sqrtLogRate (x : ℝ) : ℝ := Real.sqrt x / Real.log x
noncomputable def logSqRate (x : ℝ) : ℝ := x / Real.log x ^ 2

theorem logRate_nonneg {x : ℝ} (hx : 1 < x) : 0 ≤ logRate x :=
  div_nonneg (by linarith) (Real.log_pos hx).le

theorem sqrtLogRate_nonneg {x : ℝ} (hx : 1 < x) : 0 ≤ sqrtLogRate x :=
  div_nonneg (Real.sqrt_nonneg x) (Real.log_pos hx).le

theorem eventually_realPrimeCount_le :
    ∀ᶠ x : ℝ in atTop, realPrimeCount x ≤ 3 * logRate x := by
  have hlog : Real.log 4 ≤ (2 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    have he : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith
  filter_upwards [Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num),
    eventually_gt_atTop (1 : ℝ)] with x hx hx1
  dsimp [realPrimeCount, logRate]
  calc
    _ ≤ (Real.log 4 + 1) * x / Real.log x := hx
    _ ≤ 3 * (x / Real.log x) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith)
        (div_nonneg (by linarith) (Real.log_pos hx1).le)

theorem realPrimeCount_isBigO : realPrimeCount =O[atTop] logRate := by
  apply IsBigO.of_bound 3
  filter_upwards [eventually_realPrimeCount_le, eventually_gt_atTop (1 : ℝ)]
    with x hx hx1
  simpa [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ realPrimeCount x by
    unfold realPrimeCount; positivity),
    abs_of_nonneg (logRate_nonneg hx1)] using hx

theorem eventually_sqrtPrimeCount_le :
    ∀ᶠ x : ℝ in atTop, sqrtPrimeCount x ≤ 6 * sqrtLogRate x := by
  filter_upwards [Real.tendsto_sqrt_atTop.eventually eventually_realPrimeCount_le,
    eventually_gt_atTop (1 : ℝ)] with x hx hx1
  dsimp [sqrtPrimeCount, logRate] at hx
  dsimp [sqrtLogRate]
  rw [Real.log_sqrt (by linarith)] at hx
  convert hx using 1 <;> first | rfl | ring

theorem sqrtPrimeCount_isBigO : sqrtPrimeCount =O[atTop] sqrtLogRate := by
  apply IsBigO.of_bound 6
  filter_upwards [eventually_sqrtPrimeCount_le, eventually_gt_atTop (1 : ℝ)]
    with x hx hx1
  simpa [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ sqrtPrimeCount x by
    unfold sqrtPrimeCount realPrimeCount; positivity),
    abs_of_nonneg (sqrtLogRate_nonneg hx1)] using hx

theorem eventually_one_le_sqrtLogRate :
    ∀ᶠ x : ℝ in atTop, 1 ≤ sqrtLogRate x := by
  have h : Real.log =o[atTop] Real.sqrt := by
    change Real.log =o[atTop] (fun x : ℝ => Real.sqrt x)
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num))
  filter_upwards [h.bound (show (0 : ℝ) < 1 by norm_num),
    eventually_gt_atTop (1 : ℝ)] with x hx hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.log_pos hx1), abs_of_nonneg (Real.sqrt_nonneg x), one_mul] at hx
  exact (le_div_iff₀ (Real.log_pos hx1)).mpr (by simpa [sqrtLogRate] using hx)

theorem const_isBigO_sqrtLogRate (A : ℝ) :
    (fun _ : ℝ => A) =O[atTop] sqrtLogRate := by
  apply IsBigO.of_bound ‖A‖
  filter_upwards [eventually_one_le_sqrtLogRate] with x hx
  have hn : 1 ≤ ‖sqrtLogRate x‖ := hx.trans (le_norm_self _)
  simpa using mul_le_mul_of_nonneg_left hn (norm_nonneg A)

theorem sqrtLogRate_sq {x : ℝ} (hx : 0 ≤ x) :
    sqrtLogRate x ^ 2 = logSqRate x := by
  unfold sqrtLogRate logSqRate
  rw [div_pow, Real.sq_sqrt hx]

theorem sqrtPrimeCount_affine_isBigO (c A : ℝ) :
    (fun x => c * sqrtPrimeCount x + A) =O[atTop] sqrtLogRate :=
  (sqrtPrimeCount_isBigO.const_mul_left c).add (const_isBigO_sqrtLogRate A)

theorem sqrtPrimeCount_product_isBigO (c A : ℝ) :
    (fun x => sqrtPrimeCount x * (c * sqrtPrimeCount x + A)) =O[atTop] logSqRate := by
  have h := sqrtPrimeCount_isBigO.mul (sqrtPrimeCount_affine_isBigO c A)
  apply h.congr' (Filter.EventuallyEq.rfl)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact (by simpa only [pow_two] using sqrtLogRate_sq hx)

/-- Exact analytic majorant used to count missing composites. -/
theorem holes_majorant_isBigO :
    (fun x => sqrtPrimeCount x * (13 * sqrtPrimeCount x + 725))
      =O[atTop] logSqRate := sqrtPrimeCount_product_isBigO 13 725

theorem eventually_holes_majorant_le :
    ∀ᶠ x : ℝ in atTop,
      sqrtPrimeCount x * (13 * sqrtPrimeCount x + 725) ≤ 4818 * logSqRate x := by
  filter_upwards [eventually_sqrtPrimeCount_le, eventually_one_le_sqrtLogRate,
    eventually_ge_atTop (0 : ℝ)] with x hp hr hx
  have hp0 : 0 ≤ sqrtPrimeCount x := by
    unfold sqrtPrimeCount realPrimeCount; positivity
  have hr0 : 0 ≤ sqrtLogRate x := by linarith
  calc
    _ ≤ (6 * sqrtLogRate x) * (803 * sqrtLogRate x) := by
      apply mul_le_mul hp (by linarith) (by positivity) (by positivity)
    _ = 4818 * logSqRate x := by rw [← sqrtLogRate_sq hx]; ring

/-- A natural-number cutoff for the unconditional Chebyshev estimate. -/
theorem primeCounting_nat_bound : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (Nat.primeCounting n : ℝ) ≤ 3 * (n : ℝ) / Real.log (n : ℝ) := by
  have h := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually eventually_realPrimeCount_le
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨N, fun n hn => ?_⟩
  simpa [realPrimeCount, logRate, mul_div_assoc] using hN n hn

theorem primeCounting_sqrt_nat_le (n : ℕ) :
    (Nat.primeCounting (Nat.sqrt n) : ℝ) ≤ sqrtPrimeCount (n : ℝ) := by
  simp [sqrtPrimeCount, realPrimeCount]

theorem primeCounting_sqrt_nat_eq (n : ℕ) :
    (Nat.primeCounting (Nat.sqrt n) : ℝ) = sqrtPrimeCount (n : ℝ) := by
  simp [sqrtPrimeCount, realPrimeCount]

theorem primeCounting_sqrt_nat_bound : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (Nat.primeCounting (Nat.sqrt n) : ℝ) ≤
      6 * Real.sqrt (n : ℝ) / Real.log (n : ℝ) := by
  have h := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually eventually_sqrtPrimeCount_le
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨N, fun n hn => ?_⟩
  exact (primeCounting_sqrt_nat_le n).trans (by
    simpa [sqrtLogRate, mul_div_assoc] using hN n hn)

theorem holes_majorant_nat_bound : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ((Nat.primeCounting (Nat.sqrt n) *
      (13 * Nat.primeCounting (Nat.sqrt n) + 725) : ℕ) : ℝ) ≤
      4818 * (n : ℝ) / Real.log (n : ℝ) ^ 2 := by
  have h := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually eventually_holes_majorant_le
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨N, fun n hn => ?_⟩
  have hp := primeCounting_sqrt_nat_le n
  have hp0 : 0 ≤ (Nat.primeCounting (Nat.sqrt n) : ℝ) := by positivity
  push_cast
  calc
    _ ≤ sqrtPrimeCount n * (13 * sqrtPrimeCount n + 725) := by
      apply mul_le_mul hp (by linarith) (by positivity) (by linarith)
    _ ≤ _ := by simpa [logSqRate, mul_div_assoc] using hN n hn

end EKG
