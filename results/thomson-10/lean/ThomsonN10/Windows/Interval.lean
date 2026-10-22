/- Adapted from aravindkarthigeyan/thomson-n9-lean, proof/lean/ClaudeWindow/Interval.lean
   MIT, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e. See certificate/Windows/LICENSE-N9. -/
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs

/-!
# Exact rational interval arithmetic (L3, window classification)

A minimal closed-interval type with rational endpoints, designed for kernel
evaluation (`decide +kernel`), together with soundness lemmas into `ℝ`.
Endpoint arithmetic is exact (no rounding), so soundness is purely order theory.
Independently written for the N=9 project (namespace `ThomsonN10.Windows`).
-/

namespace ThomsonN10.Windows

/-- Closed interval `[lo, hi]` with rational endpoints. -/
structure Iv where
  lo : ℚ
  hi : ℚ
  deriving Repr

namespace Iv

/-- Real membership. -/
def Mem (I : Iv) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

def qmin (x y : ℚ) : ℚ := if x ≤ y then x else y
def qmax (x y : ℚ) : ℚ := if x ≤ y then y else x

def const (q : ℚ) : Iv := ⟨q, q⟩
def add (a b : Iv) : Iv := ⟨a.lo + b.lo, a.hi + b.hi⟩
def sub (a b : Iv) : Iv := ⟨a.lo - b.hi, a.hi - b.lo⟩

/-- Exact range of a product (four corner products). -/
def mul (a b : Iv) : Iv :=
  ⟨qmin (qmin (a.lo * b.lo) (a.lo * b.hi)) (qmin (a.hi * b.lo) (a.hi * b.hi)),
   qmax (qmax (a.lo * b.lo) (a.lo * b.hi)) (qmax (a.hi * b.lo) (a.hi * b.hi))⟩

/-- Exact range of a square. -/
def sq (a : Iv) : Iv :=
  if 0 ≤ a.lo then ⟨a.lo * a.lo, a.hi * a.hi⟩
  else if a.hi ≤ 0 then ⟨a.hi * a.hi, a.lo * a.lo⟩
  else ⟨0, qmax (a.lo * a.lo) (a.hi * a.hi)⟩

/-- `true` when the interval certainly omits `0`. -/
def excl (I : Iv) : Bool := decide (0 < I.lo) || decide (I.hi < 0)

theorem qmin_eq (x y : ℚ) : qmin x y = min x y := by
  unfold qmin; split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_lt (not_le.mp h))).symm

theorem qmax_eq (x y : ℚ) : qmax x y = max x y := by
  unfold qmax; split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (le_of_lt (not_le.mp h))).symm

theorem mem_const (q : ℚ) : (const q).Mem (q : ℝ) := ⟨le_rfl, le_rfl⟩

theorem mem_add {a b : Iv} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) :
    (add a b).Mem (x + y) := by
  constructor <;> simp only [add, Rat.cast_add]
  · exact add_le_add hx.1 hy.1
  · exact add_le_add hx.2 hy.2

theorem mem_sub {a b : Iv} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) :
    (sub a b).Mem (x - y) := by
  constructor <;> simp only [sub, Rat.cast_sub]
  · linarith [hx.1, hy.2]
  · linarith [hx.2, hy.1]

private theorem seg (a b x y : ℝ) (hax : a ≤ x) (hxb : x ≤ b) :
    min (a * y) (b * y) ≤ x * y ∧ x * y ≤ max (a * y) (b * y) := by
  rcases le_total 0 y with hy | hy
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hax hy),
      (mul_le_mul_of_nonneg_right hxb hy).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hxb hy),
      (mul_le_mul_of_nonpos_right hax hy).trans (le_max_left _ _)⟩

theorem mem_mul {a b : Iv} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) :
    (mul a b).Mem (x * y) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hxy := seg _ _ x y hx1 hx2
  have hay : min ((a.lo : ℝ) * b.lo) ((a.lo : ℝ) * b.hi) ≤ (a.lo : ℝ) * y ∧
      (a.lo : ℝ) * y ≤ max ((a.lo : ℝ) * b.lo) ((a.lo : ℝ) * b.hi) := by
    have := seg _ _ y (a.lo : ℝ) hy1 hy2
    simpa only [mul_comm] using this
  have hby : min ((a.hi : ℝ) * b.lo) ((a.hi : ℝ) * b.hi) ≤ (a.hi : ℝ) * y ∧
      (a.hi : ℝ) * y ≤ max ((a.hi : ℝ) * b.lo) ((a.hi : ℝ) * b.hi) := by
    have := seg _ _ y (a.hi : ℝ) hy1 hy2
    simpa only [mul_comm] using this
  constructor
  · simp only [mul, qmin_eq, Rat.cast_min, Rat.cast_mul]
    exact (le_min ((min_le_left _ _).trans hay.1) ((min_le_right _ _).trans hby.1)).trans hxy.1
  · simp only [mul, qmax_eq, Rat.cast_max, Rat.cast_mul]
    exact hxy.2.trans (max_le (hay.2.trans (le_max_left _ _)) (hby.2.trans (le_max_right _ _)))

theorem mem_sq {a : Iv} {x : ℝ} (hx : a.Mem x) : (sq a).Mem (x ^ 2) := by
  obtain ⟨h1, h2⟩ := hx
  unfold sq
  split_ifs with ha hb
  · have ha' : (0 : ℝ) ≤ a.lo := by exact_mod_cast ha
    constructor <;> simp only [Rat.cast_mul] <;> nlinarith
  · have hb' : (a.hi : ℝ) ≤ 0 := by exact_mod_cast hb
    constructor <;> simp only [Rat.cast_mul] <;> nlinarith
  · have ha' : (a.lo : ℝ) < 0 := by exact_mod_cast (not_le.mp ha)
    have hb' : (0 : ℝ) < a.hi := by exact_mod_cast (not_le.mp hb)
    constructor
    · simp only [Rat.cast_zero]; positivity
    · simp only [qmax_eq, Rat.cast_max, Rat.cast_mul]
      rcases le_total 0 x with hx0 | hx0
      · exact le_trans (by nlinarith) (le_max_right _ _)
      · exact le_trans (by nlinarith) (le_max_left _ _)

theorem mem_widen {a : Iv} {x : ℝ} {lo hi : ℚ} (hx : a.Mem x) (hlo : lo ≤ a.lo) (hhi : a.hi ≤ hi) :
    (⟨lo, hi⟩ : Iv).Mem x :=
  ⟨le_trans (by exact_mod_cast hlo) hx.1, le_trans hx.2 (by exact_mod_cast hhi)⟩

/-- If the real value `x` lies in `I`, the checker cannot have excluded `0` unless `x ≠ 0`. -/
theorem ne_zero_of_excl {I : Iv} {x : ℝ} (hx : I.Mem x) (h : I.excl = true) : x ≠ 0 := by
  intro h0
  subst h0
  unfold excl at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · have : (0 : ℝ) < I.lo := by exact_mod_cast (of_decide_eq_true h)
    linarith [hx.1]
  · have : (I.hi : ℝ) < 0 := by exact_mod_cast (of_decide_eq_true h)
    linarith [hx.2]

theorem not_excl_of_mem_zero {I : Iv} (hx : I.Mem 0) : I.excl = false := by
  cases h : I.excl
  · rfl
  · exact absurd rfl (ne_zero_of_excl hx h)

end Iv

end ThomsonN10.Windows
