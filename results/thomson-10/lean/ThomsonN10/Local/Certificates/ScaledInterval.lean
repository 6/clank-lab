/- Adapted from proof/lean/ThomsonN9/Certificates/ScaledInterval.lean,
   aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.Interval

/-! Sound integer endpoint checks for a common positive denominator. -/

namespace ThomsonN10.Local.Certificates

structure ScaledInterval where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

namespace ScaledInterval

def Contains (scale : ℤ) (a : ScaledInterval) (x : ℝ) : Prop :=
  (a.lo : ℝ) ≤ (scale : ℝ)*x ∧ (scale : ℝ)*x ≤ (a.hi : ℝ)

def raw (a : ScaledInterval) : RatInterval := ⟨a.lo, a.hi⟩

def rational (scale : ℤ) (a : ScaledInterval) : RatInterval :=
  ⟨(a.lo : ℚ)/scale, (a.hi : ℚ)/scale⟩

theorem contains_raw {scale : ℤ} {a : ScaledInterval} {x : ℝ}
    (hx : Contains scale a x) : a.raw.Contains ((scale : ℝ)*x) := by
  simpa only [Contains, raw, RatInterval.Contains, Rat.cast_intCast] using hx

theorem contains_rational {scale : ℤ} (hs : 0 < scale) {a : ScaledInterval} {x : ℝ}
    (hx : Contains scale a x) : (a.rational scale).Contains x := by
  have hsR : (0 : ℝ) < scale := by exact_mod_cast hs
  constructor
  · simp only [rational, Rat.cast_div, Rat.cast_intCast]
    exact (div_le_iff₀ hsR).mpr (by simpa only [mul_comm] using hx.1)
  · simp only [rational, Rat.cast_div, Rat.cast_intCast]
    exact (le_div_iff₀ hsR).mpr (by simpa only [mul_comm] using hx.2)

def ConstCheck (scale numerator denominator : ℤ) (out : ScaledInterval) : Prop :=
  0 < denominator ∧ out.lo*denominator ≤ numerator*scale ∧
    numerator*scale ≤ out.hi*denominator

def AddCheck (a b out : ScaledInterval) : Prop :=
  out.lo ≤ a.lo+b.lo ∧ a.hi+b.hi ≤ out.hi

def NegCheck (a out : ScaledInterval) : Prop :=
  out.lo ≤ -a.hi ∧ -a.lo ≤ out.hi

def MulCheck (scale : ℤ) (a b out : ScaledInterval) : Prop :=
  out.lo*scale ≤ a.lo*b.lo ∧ out.lo*scale ≤ a.lo*b.hi ∧
  out.lo*scale ≤ a.hi*b.lo ∧ out.lo*scale ≤ a.hi*b.hi ∧
  a.lo*b.lo ≤ out.hi*scale ∧ a.lo*b.hi ≤ out.hi*scale ∧
  a.hi*b.lo ≤ out.hi*scale ∧ a.hi*b.hi ≤ out.hi*scale

def InvCheck (scale : ℤ) (a out : ScaledInterval) : Prop :=
  0 < a.lo ∧ 0 ≤ out.lo ∧ 0 ≤ out.hi ∧ out.lo*a.hi ≤ scale*scale ∧
    scale*scale ≤ out.hi*a.lo

def SqrtCheck (scale : ℤ) (a out : ScaledInterval) : Prop :=
  0 ≤ a.lo ∧ 0 ≤ out.lo ∧ 0 ≤ out.hi ∧ out.lo*out.lo ≤ a.lo*scale ∧
    a.hi*scale ≤ out.hi*out.hi

instance (scale numerator denominator : ℤ) (out : ScaledInterval) :
    Decidable (ConstCheck scale numerator denominator out) := by unfold ConstCheck; infer_instance
instance (a b out : ScaledInterval) : Decidable (AddCheck a b out) := by
  unfold AddCheck; infer_instance
instance (a out : ScaledInterval) : Decidable (NegCheck a out) := by
  unfold NegCheck; infer_instance
instance (scale : ℤ) (a b out : ScaledInterval) : Decidable (MulCheck scale a b out) := by
  unfold MulCheck; infer_instance
instance (scale : ℤ) (a out : ScaledInterval) : Decidable (InvCheck scale a out) := by
  unfold InvCheck; infer_instance
instance (scale : ℤ) (a out : ScaledInterval) : Decidable (SqrtCheck scale a out) := by
  unfold SqrtCheck; infer_instance

theorem const_sound {scale numerator denominator : ℤ} {out : ScaledInterval}
    (h : ConstCheck scale numerator denominator out) :
    Contains scale out ((numerator : ℝ)/denominator) := by
  have hd : (0 : ℝ) < denominator := by exact_mod_cast h.1
  constructor
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ hd).mpr
    have h' : (out.lo : ℝ)*denominator ≤ (numerator : ℝ)*scale := by exact_mod_cast h.2.1
    nlinarith
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).mpr
    have h' : (numerator : ℝ)*scale ≤ (out.hi : ℝ)*denominator := by exact_mod_cast h.2.2
    nlinarith

theorem add_sound {scale : ℤ} {a b out : ScaledInterval} {x y : ℝ}
    (hx : Contains scale a x) (hy : Contains scale b y) (h : AddCheck a b out) :
    Contains scale out (x+y) := by
  have hlo : (out.lo : ℝ) ≤ a.lo+b.lo := by exact_mod_cast h.1
  have hhi : (a.hi : ℝ)+b.hi ≤ out.hi := by exact_mod_cast h.2
  constructor <;> dsimp [Contains] at * <;> nlinarith

theorem neg_sound {scale : ℤ} {a out : ScaledInterval} {x : ℝ}
    (hx : Contains scale a x) (h : NegCheck a out) : Contains scale out (-x) := by
  have hlo : (out.lo : ℝ) ≤ -a.hi := by exact_mod_cast h.1
  have hhi : -(a.lo : ℝ) ≤ out.hi := by exact_mod_cast h.2
  constructor <;> dsimp [Contains] at * <;> nlinarith

theorem mul_sound {scale : ℤ} (hs : 0 < scale) {a b out : ScaledInterval} {x y : ℝ}
    (hx : Contains scale a x) (hy : Contains scale b y) (h : MulCheck scale a b out) :
    Contains scale out (x*y) := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  have hlo : out.lo*scale ≤ min (min (a.lo*b.lo) (a.lo*b.hi))
      (min (a.hi*b.lo) (a.hi*b.hi)) := le_min (le_min h1 h2) (le_min h3 h4)
  have hhi : max (max (a.lo*b.lo) (a.lo*b.hi))
      (max (a.hi*b.lo) (a.hi*b.hi)) ≤ out.hi*scale :=
    max_le (max_le h5 h6) (max_le h7 h8)
  have hp := RatInterval.contains_mul (contains_raw hx) (contains_raw hy)
  have hw : (⟨(out.lo*scale : ℤ), (out.hi*scale : ℤ)⟩ : RatInterval).Contains
      (((scale : ℝ)*x)*((scale : ℝ)*y)) := by
    apply RatInterval.contains_widen hp
    · dsimp [RatInterval.mul, raw]
      exact_mod_cast hlo
    · dsimp [RatInterval.mul, raw]
      exact_mod_cast hhi
  have hsR : (0 : ℝ) < scale := by exact_mod_cast hs
  simp only [RatInterval.Contains, Rat.cast_mul, Rat.cast_intCast, Int.cast_mul] at hw
  constructor
  · apply (mul_le_mul_iff_right₀ hsR).mp
    calc
      (scale : ℝ)*out.lo = (out.lo : ℝ)*scale := by ring
      _ ≤ ((scale : ℝ)*x)*((scale : ℝ)*y) := hw.1
      _ = (scale : ℝ)*((scale : ℝ)*(x*y)) := by ring
  · apply (mul_le_mul_iff_right₀ hsR).mp
    calc
      (scale : ℝ)*((scale : ℝ)*(x*y)) = ((scale : ℝ)*x)*((scale : ℝ)*y) := by ring
      _ ≤ (out.hi : ℝ)*scale := hw.2
      _ = (scale : ℝ)*out.hi := by ring

theorem inv_sound {scale : ℤ} (hs : 0 < scale) {a out : ScaledInterval} {x : ℝ}
    (hx : Contains scale a x) (h : InvCheck scale a out) : Contains scale out x⁻¹ := by
  rcases h with ⟨ha, hlo, hhi, hlower, hupper⟩
  have hsR : (0 : ℝ) < scale := by exact_mod_cast hs
  have haR : (0 : ℝ) < a.lo := by exact_mod_cast ha
  have hloR : (0 : ℝ) ≤ out.lo := by exact_mod_cast hlo
  have hhiR : (0 : ℝ) ≤ out.hi := by exact_mod_cast hhi
  have hxpos : 0 < x := by nlinarith [hx.1]
  have hl : (out.lo : ℝ)*x ≤ scale := by
    apply (mul_le_mul_iff_right₀ hsR).mp
    calc
      (scale : ℝ)*((out.lo : ℝ)*x) = (out.lo : ℝ)*((scale : ℝ)*x) := by ring
      _ ≤ (out.lo : ℝ)*a.hi := mul_le_mul_of_nonneg_left hx.2 hloR
      _ ≤ (scale : ℝ)*scale := by exact_mod_cast hlower
  have hu : (scale : ℝ) ≤ (out.hi : ℝ)*x := by
    apply (mul_le_mul_iff_right₀ hsR).mp
    calc
      (scale : ℝ)*scale ≤ (out.hi : ℝ)*a.lo := by exact_mod_cast hupper
      _ ≤ (out.hi : ℝ)*((scale : ℝ)*x) := mul_le_mul_of_nonneg_left hx.1 hhiR
      _ = (scale : ℝ)*((out.hi : ℝ)*x) := by ring
  constructor
  · simpa only [div_eq_mul_inv] using (le_div_iff₀ hxpos).mpr hl
  · simpa only [div_eq_mul_inv] using (div_le_iff₀ hxpos).mpr hu

theorem sqrt_sound {scale : ℤ} (hs : 0 < scale) {a out : ScaledInterval} {x : ℝ}
    (hx : Contains scale a x) (h : SqrtCheck scale a out) :
    Contains scale out (Real.sqrt x) := by
  rcases h with ⟨ha, hlo, hhi, hlower, hupper⟩
  have hsR : (0 : ℝ) < scale := by exact_mod_cast hs
  have haR : (0 : ℝ) ≤ a.lo := by exact_mod_cast ha
  have hloR : (0 : ℝ) ≤ out.lo := by exact_mod_cast hlo
  have hhiR : (0 : ℝ) ≤ out.hi := by exact_mod_cast hhi
  have hxnonneg : 0 ≤ x := by nlinarith [hx.1]
  have hroot : 0 ≤ (scale : ℝ)*Real.sqrt x := mul_nonneg hsR.le (Real.sqrt_nonneg _)
  have hsq : ((scale : ℝ)*Real.sqrt x)^2 = (scale : ℝ)^2*x := by
    rw [mul_pow, Real.sq_sqrt hxnonneg]
  have hl : (out.lo : ℝ)*out.lo ≤ (a.lo : ℝ)*scale := by exact_mod_cast hlower
  have hu : (a.hi : ℝ)*scale ≤ (out.hi : ℝ)*out.hi := by exact_mod_cast hupper
  have hlx := mul_le_mul_of_nonneg_right hx.1 hsR.le
  have hux := mul_le_mul_of_nonneg_right hx.2 hsR.le
  constructor <;> nlinarith

#print axioms contains_rational
#print axioms const_sound
#print axioms mul_sound
#print axioms inv_sound
#print axioms sqrt_sound

end ScaledInterval
end ThomsonN10.Local.Certificates
