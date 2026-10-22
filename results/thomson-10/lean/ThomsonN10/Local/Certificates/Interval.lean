/- Adapted from proof/lean/ThomsonN9/Certificates/Interval.lean,
   aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-! Rational enclosures and sound arithmetic, independent of certificate generation. -/

namespace ThomsonN10.Local.Certificates

structure RatInterval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

namespace RatInterval

def Contains (a : RatInterval) (x : ℝ) : Prop := (a.lo : ℝ) ≤ x ∧ x ≤ (a.hi : ℝ)

def singleton (q : ℚ) : RatInterval := ⟨q, q⟩
def add (a b : RatInterval) : RatInterval := ⟨a.lo+b.lo, a.hi+b.hi⟩
def neg (a : RatInterval) : RatInterval := ⟨-a.hi, -a.lo⟩
def sub (a b : RatInterval) : RatInterval := add a (neg b)

def mul (a b : RatInterval) : RatInterval :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩

def inv (a : RatInterval) : RatInterval := ⟨1/a.hi, 1/a.lo⟩
def div (a b : RatInterval) : RatInterval := mul a (inv b)

def pow (a : RatInterval) : ℕ → RatInterval
  | 0 => singleton 1
  | n+1 => mul (pow a n) a

theorem contains_singleton (q : ℚ) : (singleton q).Contains (q : ℝ) := by
  exact ⟨le_rfl, le_rfl⟩

theorem contains_widen {a b : RatInterval} {x : ℝ}
    (hx : a.Contains x) (hlo : b.lo ≤ a.lo) (hhi : a.hi ≤ b.hi) : b.Contains x := by
  constructor
  · exact le_trans (by exact_mod_cast hlo) hx.1
  · exact le_trans hx.2 (by exact_mod_cast hhi)

theorem contains_add {a b : RatInterval} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (add a b).Contains (x+y) := by
  constructor <;> simp only [add, Rat.cast_add]
  · exact add_le_add hx.1 hy.1
  · exact add_le_add hx.2 hy.2

theorem contains_neg {a : RatInterval} {x : ℝ}
    (hx : a.Contains x) : (neg a).Contains (-x) := by
  constructor <;> simp only [neg, Rat.cast_neg]
  · exact neg_le_neg hx.2
  · exact neg_le_neg hx.1

theorem contains_sub {a b : RatInterval} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (sub a b).Contains (x-y) := by
  simpa only [sub, sub_eq_add_neg] using contains_add hx (contains_neg hy)

private theorem mul_segment (a b x y : ℝ) (hax : a ≤ x) (hxb : x ≤ b) :
    min (a*y) (b*y) ≤ x*y ∧ x*y ≤ max (a*y) (b*y) := by
  rcases le_total 0 y with hy | hy
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hax hy),
      (mul_le_mul_of_nonneg_right hxb hy).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hxb hy),
      (mul_le_mul_of_nonpos_right hax hy).trans (le_max_left _ _)⟩

private theorem mul_rectangle (a b c d x y : ℝ)
    (hax : a ≤ x) (hxb : x ≤ b) (hcy : c ≤ y) (hyd : y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ∧
      x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  have hxy := mul_segment a b x y hax hxb
  have hay : min (a*c) (a*d) ≤ a*y ∧ a*y ≤ max (a*c) (a*d) := by
    simpa only [mul_comm] using mul_segment c d y a hcy hyd
  have hby : min (b*c) (b*d) ≤ b*y ∧ b*y ≤ max (b*c) (b*d) := by
    simpa only [mul_comm] using mul_segment c d y b hcy hyd
  constructor
  · exact (le_min ((min_le_left _ _).trans hay.1)
      ((min_le_right _ _).trans hby.1)).trans hxy.1
  · exact hxy.2.trans (max_le (hay.2.trans (le_max_left _ _))
      (hby.2.trans (le_max_right _ _)))

theorem contains_mul {a b : RatInterval} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (mul a b).Contains (x*y) := by
  simp only [Contains, mul, Rat.cast_min, Rat.cast_max, Rat.cast_mul]
  exact mul_rectangle _ _ _ _ _ _ hx.1 hx.2 hy.1 hy.2

theorem contains_inv_of_pos {a : RatInterval} {x : ℝ}
    (hx : a.Contains x) (ha : 0 < a.lo) : (inv a).Contains x⁻¹ := by
  have hlo : (0 : ℝ) < a.lo := by exact_mod_cast ha
  have hpos : 0 < x := lt_of_lt_of_le hlo hx.1
  constructor <;> simp only [inv, Rat.cast_div, Rat.cast_one]
  · simpa only [one_div] using one_div_le_one_div_of_le hpos hx.2
  · simpa only [one_div] using one_div_le_one_div_of_le hlo hx.1

theorem contains_inv_of_neg {a : RatInterval} {x : ℝ}
    (hx : a.Contains x) (ha : a.hi < 0) : (inv a).Contains x⁻¹ := by
  have hhi : (a.hi : ℝ) < 0 := by exact_mod_cast ha
  have hneg : x < 0 := lt_of_le_of_lt hx.2 hhi
  constructor <;> simp only [inv, Rat.cast_div, Rat.cast_one]
  · simpa only [one_div] using one_div_le_one_div_of_neg_of_le hhi hx.2
  · simpa only [one_div] using one_div_le_one_div_of_neg_of_le hneg hx.1

theorem contains_inv {a : RatInterval} {x : ℝ}
    (hx : a.Contains x) (ha : 0 < a.lo ∨ a.hi < 0) : (inv a).Contains x⁻¹ := by
  exact ha.elim (contains_inv_of_pos hx) (contains_inv_of_neg hx)

theorem contains_div {a b : RatInterval} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) (hb : 0 < b.lo ∨ b.hi < 0) :
    (div a b).Contains (x/y) := by
  simpa only [div, div_eq_mul_inv] using contains_mul hx (contains_inv hy hb)

theorem contains_pow {a : RatInterval} {x : ℝ} (hx : a.Contains x) (n : ℕ) :
    (pow a n).Contains (x^n) := by
  induction n with
  | zero => simp [pow, Contains, singleton]
  | succ n ih => simpa only [pow, pow_succ] using contains_mul ih hx

theorem positive_of_contains {a : RatInterval} {x : ℝ}
    (hx : a.Contains x) (ha : 0 < a.lo) : 0 < x :=
  lt_of_lt_of_le (by exact_mod_cast ha) hx.1

theorem negative_of_contains {a : RatInterval} {x : ℝ}
    (hx : a.Contains x) (ha : a.hi < 0) : x < 0 :=
  lt_of_le_of_lt hx.2 (by exact_mod_cast ha)

/-- Exact rational inequalities sufficient for an outward square-root enclosure. -/
def SqrtBounds (a out : RatInterval) : Prop :=
  0 ≤ a.lo ∧ 0 ≤ out.lo ∧ 0 ≤ out.hi ∧ out.lo^2 ≤ a.lo ∧ a.hi ≤ out.hi^2

instance (a out : RatInterval) : Decidable (SqrtBounds a out) := by
  unfold SqrtBounds
  infer_instance

theorem contains_sqrt {a out : RatInterval} {x : ℝ}
    (hx : a.Contains x) (h : SqrtBounds a out) : out.Contains (Real.sqrt x) := by
  rcases h with ⟨ha, hlo, hhi, hlower, hupper⟩
  constructor
  · apply Real.le_sqrt_of_sq_le
    exact le_trans (by exact_mod_cast hlower) hx.1
  · apply Real.sqrt_le_iff.mpr
    exact ⟨by exact_mod_cast hhi, le_trans hx.2 (by exact_mod_cast hupper)⟩

def horner : List ℚ → RatInterval → RatInterval
  | [], _ => singleton 0
  | c :: cs, x => add (singleton c) (mul x (horner cs x))

def realHorner : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => c+x*realHorner cs x

theorem contains_horner (coefficients : List ℚ) {a : RatInterval} {x : ℝ}
    (hx : a.Contains x) : (horner coefficients a).Contains (realHorner coefficients x) := by
  induction coefficients with
  | nil => simpa [horner, realHorner] using contains_singleton (0 : ℚ)
  | cons c cs ih => exact contains_add (contains_singleton c) (contains_mul hx ih)

theorem sqrt_two_enclosure :
    (⟨1414/1000, 1415/1000⟩ : RatInterval).Contains (Real.sqrt 2) := by
  apply contains_sqrt (a := singleton 2) (contains_singleton 2)
  norm_num [SqrtBounds, singleton]

theorem rejected_sqrt_two_upper :
    ¬ SqrtBounds (singleton 2) (⟨1, 1414/1000⟩ : RatInterval) := by
  norm_num [SqrtBounds, singleton]

/-- Positive interval-enclosed LDL pivots suffice once factorization and invertibility are proved. -/
theorem posDef_of_ldl_enclosures {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A L : Matrix ι ι ℝ) (d : ι → ℝ) (bounds : ι → RatInterval)
    (hfactor : A = L * Matrix.diagonal d * star L) (hL : IsUnit L)
    (henclose : ∀ i, (bounds i).Contains (d i)) (hpositive : ∀ i, 0 < (bounds i).lo) :
    A.PosDef := by
  rw [hfactor]
  apply (Matrix.IsUnit.posDef_star_right_conjugate_iff hL).mpr
  exact Matrix.PosDef.diagonal fun i => positive_of_contains (henclose i) (hpositive i)

#print axioms contains_mul
#print axioms contains_inv
#print axioms contains_sqrt
#print axioms contains_horner
#print axioms sqrt_two_enclosure
#print axioms rejected_sqrt_two_upper
#print axioms posDef_of_ldl_enclosures

end RatInterval
end ThomsonN10.Local.Certificates
