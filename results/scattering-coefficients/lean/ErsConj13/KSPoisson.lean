import ErsConj13.KS
import ErsConj13.Pieces

/-!
# Poisson substitutions: `{a₀, a₁} = a₀a₁` implies `f ↦ f(a)` preserves the bracket
-/

noncomputable section

namespace ErsConj13.Scat

open MvPowerSeries
open ErsConj13 (bracket zd)

lemma bracket_antisymm (f g : B) : bracket f g = -bracket g f := by
  simp only [bracket]; ring

lemma bracket_mul_right' (f g h : B) : bracket f (g * h) = g * bracket f h + h * bracket f g := by
  rw [bracket_antisymm, bracket_mul_left, bracket_antisymm h f, bracket_antisymm g f]; ring

lemma bracket_add_right' (f g h : B) : bracket f (g + h) = bracket f g + bracket f h := by
  rw [bracket_antisymm, bracket_add_left, bracket_antisymm g f, bracket_antisymm h f]; ring

lemma bracket_smul_left' (c : ℚ) (f g : B) : bracket (c • f) g = c • bracket f g := by
  rw [smul_eq_C_mul, bracket_mul_left, smul_eq_C_mul]
  have : bracket (C c) g = 0 := by
    simp only [bracket]
    have h : ∀ i, zd i (C c : B) = 0 := by
      intro i; ext e; rw [coeff_zd, coeff_C]; split_ifs with h <;> simp [h]
    rw [h, h]; ring
  rw [this, mul_zero, add_zero]

lemma bracket_smul_right' (c : ℚ) (f g : B) : bracket f (c • g) = c • bracket f g := by
  rw [bracket_antisymm, bracket_smul_left', bracket_antisymm g f, smul_neg, neg_neg]

lemma bracket_sub_left' (f g h : B) : bracket (f - g) h = bracket f h - bracket g h := by
  simp only [bracket, zd_sub]; ring

lemma bracket_sub_right' (f g h : B) : bracket f (g - h) = bracket f g - bracket f h := by
  simp only [bracket, zd_sub]; ring

lemma bracket_sum_left' {ι : Type*} (s : Finset ι) (g : ι → B) (h : B) :
    bracket (∑ i ∈ s, g i) h = ∑ i ∈ s, bracket (g i) h := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bracket, show ∀ i, zd i (0 : B) = 0 from fun i => by ext; simp [coeff_zd]]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, bracket_add_left, ih]

lemma bracket_sum_right' {ι : Type*} (s : Finset ι) (g : ι → B) (h : B) :
    bracket h (∑ i ∈ s, g i) = ∑ i ∈ s, bracket h (g i) := by
  rw [bracket_antisymm, bracket_sum_left', ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => (bracket_antisymm _ _).symm

/-- `zd` preserves `𝔪^N`. -/
lemma Ord.zd {N : ℕ} {f : B} (hf : Ord N f) (i : Fin 2) : Ord N (zd i f) := by
  rw [ord_iff] at *; intro e he; rw [coeff_zd, hf e he, mul_zero]

lemma ord_bracket {a b : ℕ} {f g : B} (hf : Ord a f) (hg : Ord b g) : Ord (a + b) (bracket f g) := by
  simp only [ErsConj13.bracket]; exact ((hf.zd 0).mul (hg.zd 1)).sub ((hf.zd 1).mul (hg.zd 0))

lemma ord_bracket_left {a : ℕ} {f : B} (hf : Ord a f) (g : B) : Ord a (bracket f g) := by
  simpa using ord_bracket hf (ord_zero_left g)

lemma ord_bracket_right {a : ℕ} (f : B) {g : B} (hg : Ord a g) : Ord a (bracket f g) := by
  simpa using ord_bracket (ord_zero_left f) hg

lemma bracket_self' (p : B) : bracket p p = 0 := by simp only [ErsConj13.bracket]; ring

lemma eq_zero_of_ord_all {g : B} (h : ∀ N, Ord N g) : g = 0 := by
  ext e; rw [map_zero]; exact ord_iff.mp (h (e.degree + 1)) e (Nat.lt_succ_self _)

/-- The monomial `a^m = a₀^{m₀} a₁^{m₁}`. -/
def amon (a : Fin 2 → B) (m : Fin 2 →₀ ℕ) : B := a 0 ^ m 0 * a 1 ^ m 1

lemma bracket_pow_gen {p q : B} (n : ℕ) :
    bracket (p ^ n) q = (n : B) * p ^ (n - 1) * bracket p q := by
  rcases n with _ | n
  · simp [ErsConj13.bracket, show ∀ i, zd i (1 : B) = 0 from zd_one]
  · rw [bracket_pow_left]; push_cast; simp

lemma bracket_amon_gen {a : Fin 2 → B} (ha : bracket (a 0) (a 1) = a 0 * a 1) (m : Fin 2 →₀ ℕ) :
    bracket (amon a m) (a 0) = -((m 1 : B) * amon a m * a 0) ∧
    bracket (amon a m) (a 1) = (m 0 : B) * amon a m * a 1 := by
  have h10 : bracket (a 1) (a 0) = -(a 0 * a 1) := by rw [bracket_antisymm, ha]
  have h00 : bracket (a 0) (a 0) = 0 := bracket_self' _
  have h11 : bracket (a 1) (a 1) = 0 := bracket_self' _
  simp only [amon]
  constructor
  · rw [bracket_mul_left, bracket_pow_gen, bracket_pow_gen, h00, h10]
    rcases (m 1) with _ | k
    · simp
    · simp only [Nat.add_sub_cancel]; push_cast; ring
  · rw [bracket_mul_left, bracket_pow_gen, bracket_pow_gen, h11, ha]
    rcases (m 0) with _ | k
    · simp
    · simp only [Nat.add_sub_cancel]; push_cast; ring

lemma bracket_pow_gen_right {p q : B} (n : ℕ) :
    bracket q (p ^ n) = (n : B) * p ^ (n - 1) * bracket q p := by
  rw [bracket_antisymm, bracket_pow_gen, bracket_antisymm p q]; ring

lemma bracket_amon {a : Fin 2 → B} (ha : bracket (a 0) (a 1) = a 0 * a 1) (m n : Fin 2 →₀ ℕ) :
    bracket (amon a m) (amon a n) =
      ((m 0 : B) * n 1 - (m 1 : B) * n 0) * amon a (m + n) := by
  obtain ⟨h0, h1⟩ := bracket_amon_gen ha m
  have e : amon a (m + n) = amon a m * amon a n := by
    simp only [amon, Finsupp.add_apply, pow_add]; ring
  rw [e]
  conv_lhs => rw [show amon a n = a 0 ^ n 0 * a 1 ^ n 1 from rfl]
  rw [bracket_mul_right', bracket_pow_gen_right, bracket_pow_gen_right, h0, h1]
  simp only [amon]
  rcases (n 0) with _ | k <;> rcases (n 1) with _ | l <;> simp <;> push_cast <;> ring


lemma bracket_monomial' (m n : Fin 2 →₀ ℕ) (c c' : ℚ) :
    bracket (monomial m c : B) (monomial n c') =
      monomial (m + n) (c * c' * ((m 0 : ℚ) * n 1 - (m 1 : ℚ) * n 0)) := by
  have hz : ∀ (i : Fin 2) (k : Fin 2 →₀ ℕ) (c : ℚ),
      zd i (monomial k c : B) = monomial k ((k i : ℚ) * c) := by
    intro i k c; ext e
    show (e i : ℚ) * coeff e (monomial k c : B) = coeff e (monomial k ((k i : ℚ) * c))
    rw [coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; ring
    · simp
  simp only [ErsConj13.bracket, hz, monomial_mul_monomial, ← map_sub]
  congr 1; ring

lemma subst_bracket_monomial {a : Fin 2 → B} (hsv : SubVec a)
    (ha : bracket (a 0) (a 1) = a 0 * a 1) (m n : Fin 2 →₀ ℕ) (c c' : ℚ) :
    subst a (bracket (monomial m c : B) (monomial n c')) =
      bracket (subst a (monomial m c : B)) (subst a (monomial n c' : B)) := by
  rw [bracket_monomial', subst_monomial' a hsv, subst_monomial' a hsv, subst_monomial' a hsv,
    bracket_smul_left', bracket_smul_right']
  have := bracket_amon ha m n
  simp only [amon] at this
  rw [this]
  simp only [Finsupp.add_apply, smul_smul, smul_eq_C_mul, map_mul, map_sub, map_natCast]
  ring

lemma poly_as_sum (p : MvPolynomial (Fin 2) ℚ) :
    (p : B) = ∑ v ∈ p.support, (monomial v (MvPolynomial.coeff v p) : B) := by
  conv_lhs => rw [p.as_sum]
  rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
  simp [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_monomial]

lemma subst_sum' {a : Fin 2 → B} (hsv : SubVec a) {ι : Type*} (s : Finset ι) (g : ι → B) :
    subst a (∑ i ∈ s, g i) = ∑ i ∈ s, subst a (g i) := by
  rw [← substAlgHom_apply hsv.hasSubst, map_sum]; simp only [substAlgHom_apply]

lemma subst_bracket_poly {a : Fin 2 → B} (hsv : SubVec a)
    (ha : bracket (a 0) (a 1) = a 0 * a 1) (p q : MvPolynomial (Fin 2) ℚ) :
    subst a (bracket (p : B) (q : B)) = bracket (subst a (p : B)) (subst a (q : B)) := by
  rw [poly_as_sum p, poly_as_sum q, bracket_sum_left', subst_sum' hsv, subst_sum' hsv,
    subst_sum' hsv, bracket_sum_left']
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [bracket_sum_right', subst_sum' hsv, bracket_sum_right']
  exact Finset.sum_congr rfl fun w _ => subst_bracket_monomial hsv ha v w _ _

lemma ord_sub_trunc (N : ℕ) (f : B) : Ord N (f - (truncTotal N f : B)) := by
  rw [ord_iff]; intro e he
  rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ he, sub_self]

/-- Substitutions with `{a₀, a₁} = a₀ a₁` preserve the bracket. -/
theorem subst_bracket {a : Fin 2 → B} (hsv : SubVec a)
    (ha : bracket (a 0) (a 1) = a 0 * a 1) (f h : B) :
    subst a (bracket f h) = bracket (subst a f) (subst a h) := by
  rw [← sub_eq_zero]
  apply eq_zero_of_ord_all
  intro N
  have hf := ord_sub_trunc N f
  have hh := ord_sub_trunc N h
  set p := truncTotal N f
  set q := truncTotal N h
  set r := f - (p : B)
  set r' := h - (q : B)
  have ef : f = (p : B) + r := by simp [r]
  have eh : h = (q : B) + r' := by simp [r']
  rw [ef, eh]
  have hS := hsv.hasSubst
  have e : subst a (bracket ((p : B) + r) ((q : B) + r')) -
      bracket (subst a ((p : B) + r)) (subst a ((q : B) + r'))
      = (subst a (bracket (p : B) r') + subst a (bracket r (q : B)) + subst a (bracket r r'))
        - (bracket (subst a (p : B)) (subst a r') + bracket (subst a r) (subst a (q : B))
          + bracket (subst a r) (subst a r')) := by
    rw [bracket_add_left, bracket_add_right', bracket_add_right', subst_add hS, subst_add hS,
      subst_add hS, subst_add hS, subst_add hS, bracket_add_left, bracket_add_right',
      bracket_add_right', subst_bracket_poly hsv ha]
    ring
  rw [e]
  refine Ord.sub (Ord.add (Ord.add ?_ ?_) ?_) (Ord.add (Ord.add ?_ ?_) ?_)
  · exact (ord_bracket_right _ hh).subst hsv
  · exact (ord_bracket_left hf _).subst hsv
  · exact (ord_bracket_left hf _).subst hsv
  · exact ord_bracket_right _ (hh.subst hsv)
  · exact ord_bracket_left (hf.subst hsv) _
  · exact ord_bracket_left (hf.subst hsv) _


/-! ## Walls are Poisson -/

lemma zd_rayEval_rel (s : Slope) (f : PowerSeries ℚ) :
    ((ray s).2 : B) * zd 0 (rayEval s f) = ((ray s).1 : B) * zd 1 (rayEval s f) := by
  classical
  ext e
  rw [coeff_natCast_mul', coeff_natCast_mul', coeff_zd, coeff_zd, coeff_rayEval]
  split_ifs with h
  · have he := h.choose_spec
    have h0 : e 0 = h.choose * (ray s).1 := by
      have := congrArg (fun e => e 0) he; simpa [rvec] using this
    have h1 : e 1 = h.choose * (ray s).2 := by
      have := congrArg (fun e => e 1) he; simpa [rvec] using this
    rw [h0, h1]; push_cast; ring
  · simp

lemma zd_pow' (i : Fin 2) (F : B) (n : ℕ) : zd i (F ^ n) = (n : B) * F ^ (n - 1) * zd i F := by
  induction n with
  | zero => simp [zd_one]
  | succ n ih =>
    rw [pow_succ, zd_mul, ih]
    rcases n with _ | n
    · simp
    · simp only [Nat.add_sub_cancel]; push_cast; ring

lemma zd_inv_of (i : Fin 2) {P Q : B} (h : P * Q = 1) : zd i Q = -(Q * Q * zd i P) := by
  have h2 := congrArg (zd i) h
  rw [zd_mul, zd_one] at h2
  linear_combination Q * h2 - zd i Q * h

lemma bracket_xA_yB (A Bv : B) : bracket (X 0 * A) (X 1 * Bv) =
    X 0 * X 1 * (A * Bv + (A * zd 1 Bv + Bv * zd 0 A + (zd 0 A * zd 1 Bv - zd 1 A * zd 0 Bv))) := by
  simp only [ErsConj13.bracket, zd_mul, zd_X]; simp; ring

lemma wv_bracket (s : Slope) {f : PowerSeries ℚ} (hf : PowerSeries.constantCoeff f = 1) :
    bracket (wv s f 0) (wv s f 1) = wv s f 0 * wv s f 1 := by
  set F := rayEval s f
  have hF1 := (ord_rayEval_sub_one s hf).mono (rlen_pos s)
  have hP : F ^ (ray s).1 * (F ^ (ray s).1)⁻¹ = 1 := mul_inv_of_cc (ord_pow_sub_one hF1 _)
  set Q := (F ^ (ray s).1)⁻¹
  have hrel : ((ray s).2 : B) * zd 0 F = ((ray s).1 : B) * zd 1 F := zd_rayEval_rel s f
  have hQ : ∀ i, zd i Q = -(Q * Q * (((ray s).1 : B) * F ^ ((ray s).1 - 1) * zd i F)) := by
    intro i; rw [zd_inv_of i hP, zd_pow']
  have hw : wv s f 0 = X 0 * F ^ (ray s).2 ∧ wv s f 1 = X 1 * Q := ⟨rfl, rfl⟩
  rw [hw.1, hw.2, bracket_xA_yB, hQ 0, hQ 1, zd_pow', zd_pow']
  have hr := rlen_pos s
  simp only [rlen] at hr
  have hcop := ray_coprime s
  set p := (ray s).1 with hp
  set q := (ray s).2 with hq
  rcases Nat.eq_zero_or_pos q with h0 | h0
  · have hp1 : p = 1 := by rw [h0] at hcop; simpa using hcop
    rw [h0, hp1] at hrel ⊢
    simp at hrel ⊢
    rw [← hrel]; ring
  · obtain ⟨q', hq'⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [hq'] at hrel ⊢
    simp only [Nat.add_sub_cancel]
    have e1 : F ^ (q' + 1) * Q = F ^ q' * (F * Q) := by ring
    rcases Nat.eq_zero_or_pos p with hp0 | hp0
    · have hrel0 : ((q' : B) + 1) * zd 0 F = 0 := by
        rw [hp0] at hrel; push_cast at hrel; rw [hrel]; ring
      rw [hp0] at hP ⊢
      simp only [pow_zero, one_mul] at hP
      simp only [Nat.cast_zero, zero_mul, mul_zero, neg_zero, zero_add, add_zero, sub_zero,
        hP, pow_zero, mul_one, one_mul]
      push_cast
      linear_combination (X 0 * X 1 * F ^ q') * hrel0
    · obtain ⟨p', hp'⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      rw [hp'] at hP hrel ⊢
      simp only [Nat.add_sub_cancel]
      push_cast at hrel ⊢
      linear_combination (X 0 * X 1 * F ^ q' * Q) * hrel
        + (X 0 * X 1 * (-((p' : B) + 1)) * F ^ q' * Q * zd 1 F) * hP


theorem wall_bracket (s : Slope) {f : PowerSeries ℚ} (hf : PowerSeries.constantCoeff f = 1)
    (g h : B) : wall s f (bracket g h) = bracket (wall s f g) (wall s f h) := by
  rw [wall_eq]; exact subst_bracket (subVec_wv s f) (wv_bracket s hf) g h

/-- Substitution vectors of the form `X i (1 + c i)` with `c i ∈ 𝔪`. -/
def Unip (a : Fin 2 → B) : Prop := ∀ i, ∃ c, Ord 1 c ∧ a i = X i * (1 + c)

lemma Unip.subVec {a : Fin 2 → B} (ha : Unip a) : SubVec a := fun i => by
  obtain ⟨c, -, hc⟩ := ha i; rw [hc]; exact (ord_X i).mul_right _

lemma subst_unip {a : Fin 2 → B} (ha : Unip a) {i : Fin 2} {b : B} (hb : Ord 1 b) :
    ∃ b', Ord 1 b' ∧ subst a (X i * (1 + b)) = X i * (1 + b') := by
  obtain ⟨c, hc, hci⟩ := ha i
  refine ⟨c + subst a b + c * subst a b, (hc.add (hb.subst ha.subVec)).add (hc.mul_right _), ?_⟩
  rw [subst_mul ha.subVec.hasSubst, subst_add ha.subVec.hasSubst, subst_X' a ha.subVec,
    show subst a (1 : B) = 1 from by simpa using subst_C' a 1, hci]
  ring

lemma unip_wv (s : Slope) {f : PowerSeries ℚ} (hf : PowerSeries.constantCoeff f = 1) :
    Unip (wv s f) := by
  have hF1 := (ord_rayEval_sub_one s hf).mono (rlen_pos s)
  intro i; fin_cases i
  · exact ⟨rayEval s f ^ (ray s).2 - 1, ord_pow_sub_one hF1 _, by simp [wv]⟩
  · exact ⟨(rayEval s f ^ (ray s).1)⁻¹ - 1, ord_inv_sub_one le_rfl (ord_pow_sub_one hF1 _),
      by simp [wv]⟩

lemma wall_unip (s : Slope) {f : PowerSeries ℚ} (hf : PowerSeries.constantCoeff f = 1)
    {i : Fin 2} {b : B} (hb : Ord 1 b) :
    ∃ b', Ord 1 b' ∧ wall s f (X i * (1 + b)) = X i * (1 + b') :=
  subst_unip (unip_wv s hf) hb

end ErsConj13.Scat
