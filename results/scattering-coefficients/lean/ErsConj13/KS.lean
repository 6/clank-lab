import ErsConj13.ScatDefs
import ErsConj13.Existence

/-!
# Ordered factorization machinery: order calculus and substitution estimates
-/

noncomputable section

namespace ErsConj13.Scat

open MvPowerSeries

/-- `Ord N f`: `f ∈ 𝔪^N`, i.e. all coefficients of total degree `< N` vanish. -/
def Ord (N : ℕ) (f : B) : Prop := (N : ℕ∞) ≤ f.order

lemma degree_fin2 (e : Fin 2 →₀ ℕ) : e.degree = e 0 + e 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

lemma ord_iff {N : ℕ} {f : B} : Ord N f ↔ ∀ e : Fin 2 →₀ ℕ, e.degree < N → coeff e f = 0 :=
  ⟨fun h e he => coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast he) h),
   fun h => nat_le_order h⟩

lemma eqMod_iff {N : ℕ} {f g : B} : EqMod N f g ↔ Ord N (f - g) := by
  rw [ord_iff, EqMod]
  constructor
  · intro h e he; rw [map_sub, h e (by rwa [degree_fin2] at he), sub_self]
  · intro h e he; have := h e (by rwa [degree_fin2]); rwa [map_sub, sub_eq_zero] at this

lemma Ord.zero (N : ℕ) : Ord N (0 : B) := by simp [Ord]
lemma ord_zero_left (f : B) : Ord 0 f := by simp [Ord]
lemma Ord.add {N : ℕ} {f g : B} (hf : Ord N f) (hg : Ord N g) : Ord N (f + g) :=
  le_trans (le_min hf hg) min_order_le_add
lemma Ord.neg {N : ℕ} {f : B} (hf : Ord N f) : Ord N (-f) := by
  rw [Ord, order_neg]; exact hf
lemma Ord.sub {N : ℕ} {f g : B} (hf : Ord N f) (hg : Ord N g) : Ord N (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg
lemma Ord.mul {a b : ℕ} {f g : B} (hf : Ord a f) (hg : Ord b g) : Ord (a + b) (f * g) := by
  rw [Ord]; push_cast; exact le_trans (add_le_add hf hg) le_order_mul
lemma Ord.mul_left {a : ℕ} (f : B) {g : B} (hg : Ord a g) : Ord a (f * g) := by
  simpa using (ord_zero_left f).mul hg
lemma Ord.mul_right {a : ℕ} {f : B} (hf : Ord a f) (g : B) : Ord a (f * g) := by
  rw [mul_comm]; exact hf.mul_left g
lemma Ord.mono {a b : ℕ} (hab : a ≤ b) {f : B} (hf : Ord b f) : Ord a f :=
  le_trans (by exact_mod_cast hab) hf
lemma Ord.pow {a : ℕ} {f : B} (hf : Ord a f) (n : ℕ) : Ord (n * a) (f ^ n) := by
  induction n with
  | zero => simpa using ord_zero_left _
  | succ n ih => rw [pow_succ, add_mul, one_mul]; exact ih.mul hf
lemma Ord.smul {a : ℕ} {f : B} (hf : Ord a f) (c : ℚ) : Ord a (c • f) := by
  rw [MvPowerSeries.smul_eq_C_mul]; exact hf.mul_left _
lemma ord_sum {ι : Type*} (s : Finset ι) {N : ℕ} (g : ι → B) (h : ∀ i ∈ s, Ord N (g i)) :
    Ord N (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Ord.zero N
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma ord_one_iff {f : B} : Ord 1 f ↔ constantCoeff f = 0 := by
  rw [Ord, Nat.cast_one]; exact one_le_order_iff_constCoeff_eq_zero

lemma ord_X (i : Fin 2) : Ord 1 (X i : B) := by
  rw [ord_one_iff]; simp

lemma ord_monomial {e : Fin 2 →₀ ℕ} (c : ℚ) : Ord e.degree (monomial e c : B) := by
  rw [ord_iff]; intro e' he'
  rw [coeff_monomial, if_neg]; rintro rfl; exact lt_irrefl _ he'

lemma EqMod.refl' (N : ℕ) (f : B) : EqMod N f f := fun _ _ => rfl
lemma EqMod.symm' {N : ℕ} {f g : B} (h : EqMod N f g) : EqMod N g f := fun e he => (h e he).symm
lemma EqMod.trans' {N : ℕ} {f g k : B} (h : EqMod N f g) (h' : EqMod N g k) : EqMod N f k :=
  fun e he => (h e he).trans (h' e he)
lemma EqMod.mono' {N M : ℕ} (hNM : N ≤ M) {f g : B} (h : EqMod M f g) : EqMod N f g :=
  fun e he => h e (lt_of_lt_of_le he hNM)

/-! ## Substitution estimates -/

/-- A substitution vector with zero constant terms. -/
def SubVec (a : Fin 2 → B) : Prop := ∀ i, Ord 1 (a i)

lemma SubVec.hasSubst {a : Fin 2 → B} (ha : SubVec a) : HasSubst a :=
  hasSubst_of_constantCoeff_zero fun i => ord_one_iff.mp (ha i)

lemma subVec_X : SubVec (X : Fin 2 → B) := ord_X

lemma subst_X' (a : Fin 2 → B) (ha : SubVec a) (i : Fin 2) : subst a (X i : B) = a i :=
  subst_X ha.hasSubst i

lemma subst_C' (a : Fin 2 → B) (c : ℚ) : subst a (C c : B) = C c := by
  exact subst_C (a := a) c

lemma subst_monomial' (a : Fin 2 → B) (ha : SubVec a) (e : Fin 2 →₀ ℕ) (c : ℚ) :
    subst a (monomial e c : B) = c • (a 0 ^ e 0 * a 1 ^ e 1) := by
  rw [subst_monomial ha.hasSubst, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two,
    Algebra.smul_def]

/-- Substitution preserves `𝔪^N`. -/
lemma Ord.subst {N : ℕ} {f : B} (hf : Ord N f) {a : Fin 2 → B} (ha : SubVec a) :
    Ord N (subst a f) := by
  have h := le_order_subst ha.hasSubst f
  have h1 : (1 : ℕ∞) ≤ ⨅ i, (a i).order := le_iInf fun i => by simpa [Ord] using ha i
  refine le_trans ?_ h
  calc (N : ℕ∞) ≤ f.order := hf
    _ = 1 * f.order := (one_mul _).symm
    _ ≤ (⨅ i, (a i).order) * f.order := mul_le_mul_left h1 _

lemma pow_sub_pow_ord {l : ℕ} {x x' : B} (hx : Ord 1 x) (hx' : Ord 1 x') (hd : Ord l (x - x'))
    (n : ℕ) (hn : 1 ≤ n) : Ord (n - 1 + l) (x ^ n - x' ^ n) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · simpa using hd
    have e : x ^ (n + 1) - x' ^ (n + 1) = x ^ n * (x - x') + (x ^ n - x' ^ n) * x' := by ring
    rw [e]
    refine Ord.add ?_ ?_
    · exact ((hx.pow n).mul hd).mono (by omega)
    · exact ((ih hn').mul hx').mono (by omega)

lemma monomial_sub_ord {l : ℕ} {a a' : Fin 2 → B} (ha : SubVec a) (ha' : SubVec a')
    (hd : ∀ i, Ord l (a i - a' i)) (e : Fin 2 →₀ ℕ) (he : 1 ≤ e.degree) :
    Ord (e.degree - 1 + l) (a 0 ^ e 0 * a 1 ^ e 1 - a' 0 ^ e 0 * a' 1 ^ e 1) := by
  rw [degree_fin2] at he ⊢
  have split : a 0 ^ e 0 * a 1 ^ e 1 - a' 0 ^ e 0 * a' 1 ^ e 1
      = (a 0 ^ e 0 - a' 0 ^ e 0) * a 1 ^ e 1 + a' 0 ^ e 0 * (a 1 ^ e 1 - a' 1 ^ e 1) := by ring
  rw [split]
  refine Ord.add ?_ ?_
  · rcases Nat.eq_zero_or_pos (e 0) with h0 | h0
    · rw [h0]; simpa using Ord.zero _
    · have := (pow_sub_pow_ord (ha 0) (ha' 0) (hd 0) (e 0) h0).mul ((ha 1).pow (e 1))
      exact this.mono (by omega)
  · rcases Nat.eq_zero_or_pos (e 1) with h1 | h1
    · rw [h1]; simpa using Ord.zero _
    · have := ((ha' 0).pow (e 0)).mul (pow_sub_pow_ord (ha 1) (ha' 1) (hd 1) (e 1) h1)
      exact this.mono (by omega)

/-- The Lipschitz estimate: for `f ∈ 𝔪^k` (`k ≥ 1`) and `a ≡ a' mod 𝔪^l`,
`f(a) − f(a') ∈ 𝔪^{k−1+l}`. -/
lemma subst_sub_ord {k l : ℕ} (hk : 1 ≤ k) {f : B} (hf : Ord k f) {a a' : Fin 2 → B}
    (ha : SubVec a) (ha' : SubVec a') (hd : ∀ i, Ord l (a i - a' i)) :
    Ord (k - 1 + l) (subst a f - subst a' f) := by
  classical
  set M := k - 1 + l
  set p := truncTotal M f
  have hr : Ord M (f - (p : B)) := by
    rw [ord_iff]; intro e he
    rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ he, sub_self]
  have e1 : subst a f - subst a' f = (subst a (f - (p : B)) - subst a' (f - (p : B)))
      + (subst a (p : B) - subst a' (p : B)) := by
    rw [subst_sub ha.hasSubst, subst_sub ha'.hasSubst]; ring
  rw [e1]
  refine Ord.add ((hr.subst ha).sub (hr.subst ha')) ?_
  have hp : (p : B) = ∑ v ∈ p.support, (monomial v (MvPolynomial.coeff v p) : B) := by
    conv_lhs => rw [p.as_sum]
    rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
    simp [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_monomial]
  rw [hp, ← substAlgHom_apply ha.hasSubst, ← substAlgHom_apply ha'.hasSubst, map_sum, map_sum,
    ← Finset.sum_sub_distrib]
  refine ord_sum _ _ fun v hv => ?_
  have hcv : MvPolynomial.coeff v p ≠ 0 := MvPolynomial.mem_support_iff.mp hv
  have hdeg : k ≤ v.degree := by
    by_contra hlt
    push Not at hlt
    apply hcv
    rw [show p = truncTotal M f from rfl, coeff_truncTotal_eq_ite]
    split_ifs
    · exact ord_iff.mp hf v hlt
    · rfl
  rw [substAlgHom_apply, substAlgHom_apply, subst_monomial' a ha, subst_monomial' a' ha', ← smul_sub]
  exact ((monomial_sub_ord ha ha' hd v (by omega)).mono (by omega)).smul _


/-- The linear coefficient of `f` along `X i`. -/
def lin (i : Fin 2) (f : B) : ℚ := coeff (Finsupp.single i 1) f

lemma degree_lt_two {e : Fin 2 →₀ ℕ} (he : e.degree < 2) :
    e = 0 ∨ e = Finsupp.single 0 1 ∨ e = Finsupp.single 1 1 := by
  rw [degree_fin2] at he
  have key : ∀ e' : Fin 2 →₀ ℕ, e' 0 = e 0 → e' 1 = e 1 → e = e' := fun e' h0 h1 => by
    ext k; fin_cases k <;> simp [h0, h1]
  rcases (show (e 0 = 0 ∧ e 1 = 0) ∨ (e 0 = 1 ∧ e 1 = 0) ∨ (e 0 = 0 ∧ e 1 = 1) by omega) with
    ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
  · left; exact key 0 (by simp [h0]) (by simp [h1])
  · right; left; exact key _ (by simp [h0]) (by simp [h1])
  · right; right; exact key _ (by simp [h0]) (by simp [h1])

/-- `f` minus its affine part lies in `𝔪 ^ 2`. -/
lemma ord_two_sub_affine (f : B) :
    Ord 2 (f - (C (constantCoeff f) + lin 0 f • X 0 + lin 1 f • X 1)) := by
  have h1 : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 1 := fun h => by
    simpa using congrArg (fun e => e 0) h
  have h2 : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := fun h => by
    simpa using congrArg (fun e => e 1) h
  rw [ord_iff]; intro e he
  rcases degree_lt_two he with rfl | rfl | rfl <;>
    simp [lin, coeff_X, map_sub, map_add, coeff_C, Finsupp.single_eq_single_iff, h1, h2,
      h1.symm, h2.symm]

/-- First-order Taylor estimate for substitution. -/
lemma subst_taylor {l : ℕ} (f : B) {a a' : Fin 2 → B} (ha : SubVec a) (ha' : SubVec a')
    (hd : ∀ i, Ord l (a i - a' i)) :
    Ord (l + 1) (subst a f - subst a' f - (lin 0 f • (a 0 - a' 0) + lin 1 f • (a 1 - a' 1))) := by
  set g := f - (C (constantCoeff f) + lin 0 f • X 0 + lin 1 f • X 1)
  have hg := subst_sub_ord (by norm_num) (ord_two_sub_affine f) ha ha' hd
  have hf : f = g + (C (constantCoeff f) + lin 0 f • X 0 + lin 1 f • X 1) := by
    simp only [g]; ring
  have hlin : ∀ (b : Fin 2 → B), SubVec b →
      subst b (C (constantCoeff f) + lin 0 f • X 0 + lin 1 f • X 1 : B)
        = C (constantCoeff f) + lin 0 f • b 0 + lin 1 f • b 1 := by
    intro b hb
    rw [subst_add hb.hasSubst, subst_add hb.hasSubst, subst_C', subst_smul hb.hasSubst,
      subst_smul hb.hasSubst, subst_X' b hb, subst_X' b hb]
  have hsa : ∀ (b : Fin 2 → B), SubVec b → subst b f
      = subst b g + (C (constantCoeff f) + lin 0 f • b 0 + lin 1 f • b 1) := by
    intro b hb
    conv_lhs => rw [hf]
    rw [subst_add hb.hasSubst, hlin b hb]
  rw [hsa a ha, hsa a' ha']
  have e : subst a g + (C (constantCoeff f) + lin 0 f • a 0 + lin 1 f • a 1) -
      (subst a' g + (C (constantCoeff f) + lin 0 f • a' 0 + lin 1 f • a' 1)) -
      (lin 0 f • (a 0 - a' 0) + lin 1 f • (a 1 - a' 1)) = subst a g - subst a' g := by
    simp only [smul_sub]; ring
  rw [e, show l + 1 = 2 - 1 + l by omega]; exact hg

/-- Congruent substitution vectors give congruent substitutions. -/
lemma subst_congr_vec {N : ℕ} (f : B) {a a' : Fin 2 → B} (ha : SubVec a) (ha' : SubVec a')
    (hd : ∀ i, EqMod N (a i) (a' i)) : EqMod N (subst a f) (subst a' f) := by
  rw [eqMod_iff]
  set g := f - C (constantCoeff f)
  have hg : Ord 1 g := by rw [ord_one_iff]; simp [g]
  have := subst_sub_ord le_rfl hg ha ha' (fun i => eqMod_iff.mp (hd i))
  have hf : f = g + C (constantCoeff f) := by simp [g]
  rw [hf, subst_add ha.hasSubst, subst_add ha'.hasSubst, subst_C', subst_C']
  simpa using this

lemma subst_congr_arg {N : ℕ} {f f' : B} (h : EqMod N f f') {a : Fin 2 → B} (ha : SubVec a) :
    EqMod N (subst a f) (subst a f') := by
  rw [eqMod_iff] at h ⊢
  rw [← subst_sub ha.hasSubst]; exact h.subst ha

lemma subst_self' (f : B) : subst (X : Fin 2 → B) f = f := by
  rw [subst_self]; rfl

/-- Unipotent substitutions move `𝔪^k` by `𝔪^{k+1}`. -/
lemma subst_unipotent {k : ℕ} (hk : 1 ≤ k) {D : B} (hD : Ord k D) {a : Fin 2 → B}
    (ha : SubVec a) (h2 : ∀ i, Ord 2 (a i - X i)) : Ord (k + 1) (subst a D - D) := by
  have := subst_sub_ord hk hD ha subVec_X h2
  rw [subst_self'] at this
  exact this.mono (by omega)


/-! ## Rays and walls -/

lemma ray_coe' (q : ℚ≥0) : ray (q : Slope) = (q.den, q.num) := rfl
lemma ray_top' : ray (⊤ : Slope) = (0, 1) := rfl
lemma ray_zero' : ray ((0 : ℚ≥0) : Slope) = (1, 0) := by rw [ray_coe']; simp
@[simp] lemma ray_zero'' : ray (0 : Slope) = (1, 0) := by rw [← WithTop.coe_zero, ray_coe']; simp

/-- The exponent vector `r` of the ray of slope `s`. -/
def rvec (s : Slope) : Fin 2 →₀ ℕ := Finsupp.single 0 (ray s).1 + Finsupp.single 1 (ray s).2

/-- `|r| = r₁ + r₂`. -/
def rlen (s : Slope) : ℕ := (ray s).1 + (ray s).2

lemma rvec_degree (s : Slope) : (rvec s).degree = rlen s := by
  simp [rvec, rlen, degree_fin2]

lemma rlen_pos (s : Slope) : 1 ≤ rlen s := by
  induction s using WithTop.recTopCoe with
  | top => simp [rlen, ray]
  | coe q => simp only [rlen, ray, WithTop.recTopCoe_coe]; have := q.den_pos; omega

lemma rayMono_eq (s : Slope) : rayMono s = monomial (rvec s) 1 := rfl

lemma hasSubst_rayMono (s : Slope) : PowerSeries.HasSubst (rayMono s) := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero
  rw [rayMono_eq, ← coeff_zero_eq_constantCoeff_apply, coeff_monomial, if_neg]
  intro h
  have := congrArg Finsupp.degree h
  rw [rvec_degree] at this; simp at this; have := rlen_pos s; omega

lemma smul_rvec_inj {s : Slope} {d j : ℕ} (h : d • rvec s = j • rvec s) : d = j := by
  have := congrArg Finsupp.degree h
  simp only [map_nsmul, rvec_degree, smul_eq_mul] at this
  exact Nat.eq_of_mul_eq_mul_right (rlen_pos s) this

open Classical in
lemma coeff_rayEval (s : Slope) (f : PowerSeries ℚ) (e : Fin 2 →₀ ℕ) :
    coeff e (rayEval s f) =
      if h : ∃ j, e = j • rvec s then PowerSeries.coeff h.choose f else 0 := by
  rw [rayEval, PowerSeries.coeff_subst (hasSubst_rayMono s)]
  simp_rw [rayMono_eq, monomial_pow, coeff_monomial, one_pow]
  split_ifs with h
  · rw [finsum_eq_single _ h.choose]
    · simp [← h.choose_spec]
    · intro d hd
      rw [if_neg]; · simp
      intro he; apply hd
      exact smul_rvec_inj (he.symm.trans h.choose_spec)
  · rw [finsum_eq_zero_of_forall_eq_zero]
    intro d; rw [if_neg]; · simp
    intro he; exact h ⟨d, he⟩

lemma coeff_rayEval_smul (s : Slope) (f : PowerSeries ℚ) (j : ℕ) :
    coeff (j • rvec s) (rayEval s f) = PowerSeries.coeff j f := by
  have hc : ∀ h : ∃ j', j • rvec s = j' • rvec s, h.choose = j :=
    fun h => (smul_rvec_inj h.choose_spec).symm
  rw [coeff_rayEval, dif_pos ⟨j, rfl⟩, hc]

lemma ord_rayEval_sub (s : Slope) {f f' : PowerSeries ℚ} {d : ℕ}
    (h : ∀ j, j * rlen s < d → PowerSeries.coeff j f = PowerSeries.coeff j f') :
    Ord d (rayEval s f - rayEval s f') := by
  rw [ord_iff]; intro e he
  rw [map_sub, coeff_rayEval, coeff_rayEval]
  split_ifs with hx
  · rw [h _ ?_, sub_self]
    have := hx.choose_spec
    rw [this, map_nsmul, rvec_degree, smul_eq_mul] at he
    exact he
  · simp

lemma rayEval_one (s : Slope) : rayEval s 1 = 1 := by
  rw [rayEval, ← map_one (PowerSeries.C (R := ℚ)), PowerSeries.subst_C]; simp

lemma ord_rayEval_sub_one (s : Slope) {f : PowerSeries ℚ} (hf : PowerSeries.constantCoeff f = 1) :
    Ord (rlen s) (rayEval s f - 1) := by
  rw [← rayEval_one s]
  apply ord_rayEval_sub
  intro j hj
  have : j = 0 := by have := rlen_pos s; nlinarith
  subst this; simp [hf]

/-! ### Power and inverse estimates -/

lemma ord_pow_sub_one {l : ℕ} {F : B} (hF : Ord l (F - 1)) (n : ℕ) : Ord l (F ^ n - 1) := by
  induction n with
  | zero => simpa using Ord.zero l
  | succ n ih =>
    have e : F ^ (n + 1) - 1 = F ^ n * (F - 1) + (F ^ n - 1) := by ring
    rw [e]; exact (hF.mul_left _).add ih

lemma ord_pow_sub_pow {d : ℕ} {F F' : B} (hd : Ord d (F - F')) (n : ℕ) :
    Ord d (F ^ n - F' ^ n) := by
  induction n with
  | zero => simpa using Ord.zero d
  | succ n ih =>
    have e : F ^ (n + 1) - F' ^ (n + 1) = F ^ n * (F - F') + (F ^ n - F' ^ n) * F' := by ring
    rw [e]; exact (hd.mul_left _).add (ih.mul_right _)

lemma ord_pow_sub_pow_lin {d : ℕ} {F F' : B} (hF : Ord 1 (F - 1)) (hF' : Ord 1 (F' - 1))
    (hd : Ord d (F - F')) (n : ℕ) : Ord (d + 1) (F ^ n - F' ^ n - (n : B) * (F - F')) := by
  induction n with
  | zero => simpa using Ord.zero _
  | succ n ih =>
    have e : F ^ (n + 1) - F' ^ (n + 1) - ((n + 1 : ℕ) : B) * (F - F')
        = (F ^ n - 1) * (F - F') + (F' - 1) * (F ^ n - F' ^ n)
          + (F ^ n - F' ^ n - (n : B) * (F - F')) := by push_cast; ring
    rw [e]
    refine Ord.add (Ord.add ?_ ?_) ih
    · rw [add_comm]; exact (ord_pow_sub_one hF n).mul hd
    · rw [add_comm]; exact hF'.mul (ord_pow_sub_pow hd n)

lemma mul_inv_of_cc {G : B} (hG : Ord 1 (G - 1)) : G * G⁻¹ = 1 := by
  apply MvPowerSeries.mul_inv_cancel
  have := ord_one_iff.mp hG
  rw [map_sub, map_one, sub_eq_zero] at this; rw [this]; norm_num

lemma ord_inv_sub_one {l : ℕ} {G : B} (hl : 1 ≤ l) (hG : Ord l (G - 1)) : Ord l (G⁻¹ - 1) := by
  have h1 := mul_inv_of_cc (hG.mono hl)
  have e : G⁻¹ - 1 = -(G - 1) * G⁻¹ := by linear_combination h1
  rw [e]; exact hG.neg.mul_right _

lemma ord_inv_sub_inv_lin {d : ℕ} {G G' : B} (hG : Ord 1 (G - 1)) (hG' : Ord 1 (G' - 1))
    (hd : Ord d (G - G')) : Ord (d + 1) (G⁻¹ - G'⁻¹ + (G - G')) := by
  have h1 := mul_inv_of_cc hG
  have h2 := mul_inv_of_cc hG'
  have e : G⁻¹ - G'⁻¹ + (G - G') = (G - G') * (1 - G⁻¹ * G'⁻¹) := by
    linear_combination G'⁻¹ * h1 - G⁻¹ * h2
  rw [e]
  have h3 : Ord 1 (1 - G⁻¹ * G'⁻¹) := by
    have a := ord_inv_sub_one le_rfl hG
    have b := ord_inv_sub_one le_rfl hG'
    have e2 : 1 - G⁻¹ * G'⁻¹ = -((G⁻¹ - 1) * G'⁻¹ + (G'⁻¹ - 1)) := by ring
    rw [e2]; exact ((a.mul_right _).add b).neg
  exact hd.mul h3

/-! ### The wall vector -/

/-- The substitution vector of `θ_{r,f}`. -/
def wv (s : Slope) (f : PowerSeries ℚ) : Fin 2 → B :=
  ![X 0 * rayEval s f ^ (ray s).2, X 1 * (rayEval s f ^ (ray s).1)⁻¹]

lemma wall_eq (s : Slope) (f : PowerSeries ℚ) : wall s f = subst (wv s f) := rfl

lemma subVec_wv (s : Slope) (f : PowerSeries ℚ) : SubVec (wv s f) := by
  intro i; fin_cases i
  · exact (ord_X 0).mul_right _
  · exact (ord_X 1).mul_right _

lemma wv_sub_X (s : Slope) {f : PowerSeries ℚ} (hf : PowerSeries.constantCoeff f = 1) (i : Fin 2) :
    Ord (rlen s + 1) (wv s f i - X i) := by
  have hF := ord_rayEval_sub_one s hf
  fin_cases i
  · have e : wv s f 0 - X 0 = X 0 * (rayEval s f ^ (ray s).2 - 1) := by simp [wv]; ring
    simp only [Fin.zero_eta, Fin.isValue]; rw [e, add_comm]
    exact (ord_X 0).mul (ord_pow_sub_one hF _)
  · have e : wv s f 1 - X 1 = X 1 * ((rayEval s f ^ (ray s).1)⁻¹ - 1) := by simp [wv]; ring
    simp only [Fin.mk_one, Fin.isValue]; rw [e, add_comm]
    exact (ord_X 1).mul (ord_inv_sub_one (rlen_pos s) (ord_pow_sub_one hF _))

lemma wv_sub_X_two (s : Slope) {f : PowerSeries ℚ} (hf : PowerSeries.constantCoeff f = 1)
    (i : Fin 2) : Ord 2 (wv s f i - X i) :=
  (wv_sub_X s hf i).mono (by have := rlen_pos s; omega)

lemma wv_diff (s : Slope) {f f' : PowerSeries ℚ} (hf : PowerSeries.constantCoeff f = 1)
    (hf' : PowerSeries.constantCoeff f' = 1) {d : ℕ}
    (hd : Ord d (rayEval s f - rayEval s f')) :
    Ord (d + 2) (wv s f 0 - wv s f' 0 - ((ray s).2 : B) * (X 0 * (rayEval s f - rayEval s f'))) ∧
    Ord (d + 2) (wv s f 1 - wv s f' 1 + ((ray s).1 : B) * (X 1 * (rayEval s f - rayEval s f'))) := by
  set F := rayEval s f
  set F' := rayEval s f'
  have hF := (ord_rayEval_sub_one s hf).mono (rlen_pos s)
  have hF' := (ord_rayEval_sub_one s hf').mono (rlen_pos s)
  constructor
  · have e : wv s f 0 - wv s f' 0 - ((ray s).2 : B) * (X 0 * (F - F'))
        = X 0 * (F ^ (ray s).2 - F' ^ (ray s).2 - ((ray s).2 : B) * (F - F')) := by
      simp [wv, F, F']; ring
    rw [e, show d + 2 = 1 + (d + 1) by ring]
    exact (ord_X 0).mul (ord_pow_sub_pow_lin hF hF' hd _)
  · have hG := ord_pow_sub_one hF (ray s).1
    have hG' := ord_pow_sub_one hF' (ray s).1
    have hGd := ord_pow_sub_pow hd (ray s).1
    have hi := ord_inv_sub_inv_lin hG hG' hGd
    have hl := ord_pow_sub_pow_lin hF hF' hd (ray s).1
    have e : wv s f 1 - wv s f' 1 + ((ray s).1 : B) * (X 1 * (F - F'))
        = X 1 * (((F ^ (ray s).1)⁻¹ - (F' ^ (ray s).1)⁻¹ + (F ^ (ray s).1 - F' ^ (ray s).1))
          - (F ^ (ray s).1 - F' ^ (ray s).1 - ((ray s).1 : B) * (F - F'))) := by
      simp [wv, F, F']; ring
    rw [e, show d + 2 = 1 + (d + 1) by ring]
    exact (ord_X 1).mul (hi.sub hl)


/-! ## Ordered products over lists and the perturbation lemma -/

/-- The ordered product over a list (head leftmost). -/
def prodL (f : Slope → PowerSeries ℚ) (L : List Slope) : B → B :=
  L.foldr (fun s φ => wall s (f s) ∘ φ) id

lemma prodL_nil (f : Slope → PowerSeries ℚ) (h : B) : prodL f [] h = h := rfl
lemma prodL_cons (f : Slope → PowerSeries ℚ) (s : Slope) (L : List Slope) (h : B) :
    prodL f (s :: L) h = wall s (f s) (prodL f L h) := rfl

lemma orderedProd_eq (f : Slope → PowerSeries ℚ) (N : ℕ) :
    orderedProd f N = prodL f ((slopesBelow N).sort (· ≤ ·)) := rfl

lemma ord_two_lin {g : B} (hg : Ord 2 g) (i : Fin 2) : lin i g = 0 := by
  apply ord_iff.mp hg; simp

lemma wall_sub_self {f : PowerSeries ℚ} (hf : PowerSeries.constantCoeff f = 1) (s : Slope)
    {H : B} {k : ℕ} (hk : 1 ≤ k) (hH : Ord k H) : Ord (k + 1) (wall s f H - H) :=
  subst_unipotent hk hH (subVec_wv s f) (wv_sub_X_two s hf)

lemma prodL_sub_self {f : Slope → PowerSeries ℚ} (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1)
    (L : List Slope) {h : B} (hh : Ord 1 h) : Ord 2 (prodL f L h - h) := by
  induction L with
  | nil => simpa [prodL_nil] using Ord.zero 2
  | cons s L ih =>
    rw [prodL_cons]
    have hP : Ord 1 (prodL f L h) := by
      have := (ih.mono (by norm_num : 1 ≤ 2)).add hh; simpa using this
    have e : wall s (f s) (prodL f L h) - h
        = (wall s (f s) (prodL f L h) - prodL f L h) + (prodL f L h - h) := by ring
    rw [e]; exact (wall_sub_self (hf s) s le_rfl hP).add ih

lemma lin_prodL {f : Slope → PowerSeries ℚ} (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1)
    (L : List Slope) {h : B} (hh : Ord 1 h) (i : Fin 2) : lin i (prodL f L h) = lin i h := by
  have := ord_two_lin (prodL_sub_self hf L hh) i
  rw [lin, map_sub, sub_eq_zero] at this; exact this

/-- The first-order term of a perturbation of one wall, at `h`. -/
def pertTerm (f f' : Slope → PowerSeries ℚ) (h : B) (s : Slope) : B :=
  lin 0 h • (((ray s).2 : B) * (X 0 * (rayEval s (f s) - rayEval s (f' s))))
    - lin 1 h • (((ray s).1 : B) * (X 1 * (rayEval s (f s) - rayEval s (f' s))))

lemma pertTerm_ord {f f' : Slope → PowerSeries ℚ} {h : B} {s : Slope} {d : ℕ}
    (hd : Ord d (rayEval s (f s) - rayEval s (f' s))) : Ord (d + 1) (pertTerm f f' h s) := by
  unfold pertTerm
  refine Ord.sub (Ord.smul ?_ _) (Ord.smul ?_ _)
  · rw [add_comm]; exact ((ord_X 0).mul hd).mul_left _
  · rw [add_comm]; exact ((ord_X 1).mul hd).mul_left _

/-- The perturbation lemma: if the ray functions of `f` and `f'` differ only in degree `≥ d`
(on each ray `s` of `L`), the ordered products differ, to order `d + 1`, by the sum of the
one-wall first-order terms. -/
lemma prodL_pert {f f' : Slope → PowerSeries ℚ} (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1)
    (hf' : ∀ s, PowerSeries.constantCoeff (f' s) = 1) {d : ℕ} (hd1 : 1 ≤ d) (L : List Slope)
    (hd : ∀ s ∈ L, Ord d (rayEval s (f s) - rayEval s (f' s))) {h : B} (hh : Ord 1 h) :
    Ord (d + 2) (prodL f L h - prodL f' L h - (L.map (pertTerm f f' h)).sum) := by
  induction L with
  | nil => simpa [prodL_nil] using Ord.zero _
  | cons s L ih =>
    have ih' := ih (fun t ht => hd t (List.mem_cons_of_mem _ ht))
    have hds := hd s List.mem_cons_self
    set D := prodL f L h - prodL f' L h
    have hsum : Ord (d + 1) (L.map (pertTerm f f' h)).sum := by
      have : ∀ t ∈ L, Ord (d + 1) (pertTerm f f' h t) :=
        fun t ht => pertTerm_ord (hd t (List.mem_cons_of_mem _ ht))
      clear ih ih' hds
      induction L with
      | nil => simpa using Ord.zero _
      | cons t L ih2 =>
        rw [List.map_cons, List.sum_cons]
        exact (this t List.mem_cons_self).add (ih2 (fun u hu => hd u (by
          rcases List.mem_cons.mp hu with rfl | hu
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hu))) (fun u hu =>
            this u (List.mem_cons_of_mem _ hu)))
    have hD : Ord (d + 1) D := by
      have := (ih'.mono (by omega : d + 1 ≤ d + 2)).add hsum; simpa using this
    -- term 1: the wall applied to the difference
    have t1 : Ord (d + 2) (wall s (f s) D - D) := wall_sub_self (hf s) s (by omega) hD
    -- term 3: Taylor at `H = prodL f' L h`
    set H := prodL f' L h
    have hwd := wv_diff s (hf s) (hf' s) hds
    have hvd : ∀ i, Ord (d + 1) (wv s (f s) i - wv s (f' s) i) := by
      intro i; fin_cases i
      · have := hwd.1.mono (by omega : d + 1 ≤ d + 2)
        have h2 : Ord (d + 1) (((ray s).2 : B) * (X 0 * (rayEval s (f s) - rayEval s (f' s)))) := by
          rw [add_comm]; exact ((ord_X 0).mul hds).mul_left _
        simpa using this.add h2
      · have := hwd.2.mono (by omega : d + 1 ≤ d + 2)
        have h2 : Ord (d + 1) (((ray s).1 : B) * (X 1 * (rayEval s (f s) - rayEval s (f' s)))) := by
          rw [add_comm]; exact ((ord_X 1).mul hds).mul_left _
        simpa using this.sub h2
    have t3 := subst_taylor H (subVec_wv s (f s)) (subVec_wv s (f' s)) hvd
    rw [lin_prodL hf' L hh, lin_prodL hf' L hh] at t3
    rw [prodL_cons, prodL_cons, List.map_cons, List.sum_cons]
    have hlin0 := (hwd.1.smul (lin 0 h))
    have hlin1 := (hwd.2.smul (lin 1 h))
    have e : wall s (f s) (prodL f L h) - wall s (f' s) H
        - (pertTerm f f' h s + (L.map (pertTerm f f' h)).sum)
        = (wall s (f s) D - D) + (D - (L.map (pertTerm f f' h)).sum)
          + (subst (wv s (f s)) H - subst (wv s (f' s)) H
              - (lin 0 h • (wv s (f s) 0 - wv s (f' s) 0) + lin 1 h • (wv s (f s) 1 - wv s (f' s) 1)))
          + lin 0 h • (wv s (f s) 0 - wv s (f' s) 0
              - ((ray s).2 : B) * (X 0 * (rayEval s (f s) - rayEval s (f' s))))
          + lin 1 h • (wv s (f s) 1 - wv s (f' s) 1
              + ((ray s).1 : B) * (X 1 * (rayEval s (f s) - rayEval s (f' s)))) := by
      have hW : wall s (f s) D = wall s (f s) (prodL f L h) - wall s (f s) H := by
        rw [wall_eq, ← subst_sub (subVec_wv s (f s)).hasSubst]
      rw [hW, wall_eq, wall_eq]
      simp only [pertTerm, smul_sub, smul_add, D, H]
      ring
    rw [e]
    exact (((t1.add ih').add (by rw [show d + 2 = d + 1 + 1 by ring]; exact t3)).add hlin0).add hlin1


/-! ## Slopes, rays and `slopesBelow` -/

lemma ray_coprime (s : Slope) : Nat.Coprime (ray s).1 (ray s).2 := by
  induction s using WithTop.recTopCoe with
  | top => simp [ray]
  | coe q => simp only [ray, WithTop.recTopCoe_coe]; exact (q.coprime_num_den).symm

lemma slopeOf_ray (s : Slope) : slopeOf (ray s).1 (ray s).2 = s := by
  induction s using WithTop.recTopCoe with
  | top => simp [ray, slopeOf]
  | coe q =>
    simp only [ray, WithTop.recTopCoe_coe, slopeOf, if_neg q.den_ne_zero]
    rw [NNRat.num_div_den]

lemma ray_slopeOf {p q : ℕ} (h : Nat.Coprime p q) : ray (slopeOf p q) = (p, q) := by
  by_cases hp : p = 0
  · subst hp
    have : q = 1 := by simpa using h
    subst this; simp [slopeOf, ray]
  · simp only [slopeOf, if_neg hp, ray, WithTop.recTopCoe_coe]
    have hp' : (0 : ℤ) < p := by exact_mod_cast Nat.pos_of_ne_zero hp
    have hc : Nat.Coprime ((q : ℤ).natAbs) ((p : ℤ).natAbs) := by simpa using h.symm
    have hden := Rat.den_div_eq_of_coprime hp' hc
    have hnum := Rat.num_div_eq_of_coprime hp' hc
    have e : (((q : ℚ≥0) / p : ℚ≥0) : ℚ) = ((q : ℤ) : ℚ) / ((p : ℤ) : ℚ) := by push_cast; rfl
    refine Prod.ext ?_ ?_
    · rw [← NNRat.den_coe, e]; exact_mod_cast hden
    · have := NNRat.num_coe ((q : ℚ≥0) / p)
      rw [e, hnum] at this
      exact_mod_cast this.symm

lemma ray_injective : Function.Injective ray := fun s t h => by
  rw [← slopeOf_ray s, ← slopeOf_ray t, h]

lemma mem_slopesBelow (s : Slope) (N : ℕ) : s ∈ slopesBelow N ↔ rlen s < N := by
  simp only [slopesBelow, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range]
  constructor
  · rintro ⟨⟨p, q⟩, ⟨-, hc, hlt⟩, rfl⟩
    simp only at hc hlt ⊢
    rw [rlen, ray_slopeOf hc]; exact hlt
  · intro h
    refine ⟨((ray s).1, (ray s).2), ⟨⟨?_, ?_⟩, ray_coprime s, h⟩, slopeOf_ray s⟩ <;>
      (simp only [rlen] at h; omega)

lemma rvec_apply0 (s : Slope) : rvec s 0 = (ray s).1 := by simp [rvec]
lemma rvec_apply1 (s : Slope) : rvec s 1 = (ray s).2 := by simp [rvec]

/-- Multiples of primitive vectors determine the ray and the multiple. -/
lemma smul_rvec_eq {s t : Slope} {j j' : ℕ} (hj : 1 ≤ j) (h : j • rvec s = j' • rvec t) :
    s = t ∧ j = j' := by
  have h0 := congrArg (fun e => e 0) h
  have h1 := congrArg (fun e => e 1) h
  simp only [Finsupp.smul_apply, rvec_apply0, rvec_apply1, smul_eq_mul] at h0 h1
  have g1 : Nat.gcd (j * (ray s).1) (j * (ray s).2) = j := by
    rw [Nat.gcd_mul_left, ray_coprime s, mul_one]
  have g2 : Nat.gcd (j' * (ray t).1) (j' * (ray t).2) = j' := by
    rw [Nat.gcd_mul_left, ray_coprime t, mul_one]
  have hjj : j = j' := by rw [← g1, ← g2, h0, h1]
  subst hjj
  refine ⟨ray_injective (Prod.ext ?_ ?_), rfl⟩
  · exact Nat.eq_of_mul_eq_mul_left (by omega) h0
  · exact Nat.eq_of_mul_eq_mul_left (by omega) h1


/-! ## Uniqueness of factorizations -/

lemma lin_X (i j : Fin 2) : lin i (X j : B) = if i = j then 1 else 0 := by
  rw [lin, coeff_X]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg, if_neg h]
    rw [Finsupp.single_left_inj one_ne_zero]; exact h

lemma coeff_rayEval_sub_other {s t : Slope} (hst : s ≠ t) {j : ℕ} (hj : 1 ≤ j)
    (F G : PowerSeries ℚ) : coeff (j • rvec s) (rayEval t F - rayEval t G) = 0 := by
  classical
  rw [map_sub, coeff_rayEval, coeff_rayEval, dif_neg, dif_neg, sub_self] <;>
  · rintro ⟨j', hj'⟩
    exact hst (smul_rvec_eq hj hj').1

lemma coeff_X_mul_add (i : Fin 2) (k : Fin 2 →₀ ℕ) (G : B) :
    coeff (Finsupp.single i 1 + k) ((X i : B) * G) = coeff k G := by
  rw [X_def, coeff_add_monomial_mul, one_mul]

lemma coeff_natCast_mul' (n : ℕ) (e : Fin 2 →₀ ℕ) (G : B) :
    coeff e ((n : B) * G) = n * coeff e G := by
  rw [← map_natCast (C (σ := Fin 2) (R := ℚ)), coeff_C_mul]

/-- Extraction of the perturbation sum's coefficient on the ray `s`. -/
lemma coeff_pertSum (f f' : Slope → PowerSeries ℚ) (i : Fin 2) (L : List Slope) (hL : L.Nodup)
    {s : Slope} (hs : s ∈ L) {j : ℕ} (hj : 1 ≤ j) :
    coeff (Finsupp.single i 1 + j • rvec s) ((L.map (pertTerm f f' (X i))).sum) =
      (if i = 0 then ((ray s).2 : ℚ) else -((ray s).1 : ℚ)) *
        (PowerSeries.coeff j (f s) - PowerSeries.coeff j (f' s)) := by
  have hterm : ∀ t, coeff (Finsupp.single i 1 + j • rvec s) (pertTerm f f' (X i) t) =
      (if i = 0 then ((ray t).2 : ℚ) else -((ray t).1 : ℚ)) *
        coeff (j • rvec s) (rayEval t (f t) - rayEval t (f' t)) := by
    intro t
    by_cases hi : i = 0
    · subst hi
      have e : pertTerm f f' (X 0) t = ((ray t).2 : B) * (X 0 * (rayEval t (f t) - rayEval t (f' t))) := by
        simp [pertTerm, lin_X]
      rw [e, coeff_natCast_mul', coeff_X_mul_add, if_pos rfl]
    · have hi1 : i = 1 := by fin_cases i <;> simp_all
      subst hi1
      have e : pertTerm f f' (X 1) t = -(((ray t).1 : B) * (X 1 * (rayEval t (f t) - rayEval t (f' t)))) := by
        simp [pertTerm, lin_X]
      rw [e, map_neg, coeff_natCast_mul', coeff_X_mul_add, if_neg hi, neg_mul]
  induction L with
  | nil => simp at hs
  | cons t L ih =>
    rw [List.map_cons, List.sum_cons, map_add, hterm]
    rcases List.mem_cons.mp hs with rfl | hs'
    · have hnot : s ∉ L := (List.nodup_cons.mp hL).1
      have hz : coeff (Finsupp.single i 1 + j • rvec s) ((L.map (pertTerm f f' (X i))).sum) = 0 := by
        clear ih hs hL
        induction L with
        | nil => simp
        | cons u L ih2 =>
          rw [List.map_cons, List.sum_cons, map_add, hterm,
            coeff_rayEval_sub_other (fun h => hnot (by rw [h]; exact List.mem_cons_self)) hj,
            mul_zero, zero_add]
          exact ih2 (fun h => hnot (List.mem_cons_of_mem _ h))
      rw [hz, add_zero, map_sub, coeff_rayEval_smul, coeff_rayEval_smul]
    · have hts : t ≠ s := fun h => (List.nodup_cons.mp hL).1 (h ▸ hs')
      rw [coeff_rayEval_sub_other (Ne.symm hts) hj, mul_zero, zero_add]
      exact ih (List.nodup_cons.mp hL).2 hs'

/-- Uniqueness of the levelwise ordered factorization of a given map. -/
theorem factor_unique_aux (g : B → B) (f f' : Slope → PowerSeries ℚ)
    (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1)
    (hf' : ∀ s, PowerSeries.constantCoeff (f' s) = 1)
    (hgf : ∀ N i, EqMod N (orderedProd f N (X i)) (g (X i)))
    (hgf' : ∀ N i, EqMod N (orderedProd f' N (X i)) (g (X i))) : f = f' := by
  have key : ∀ d, ∀ s j, j * rlen s = d → PowerSeries.coeff j (f s) = PowerSeries.coeff j (f' s) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d IH =>
      intro s j hsj
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp [hf, hf']
      have hd1 : 1 ≤ d := by have := rlen_pos s; rw [← hsj]; nlinarith
      have hd : ∀ t, Ord d (rayEval t (f t) - rayEval t (f' t)) := fun t =>
        ord_rayEval_sub t fun j' hj' => IH _ hj' t j' rfl
      set N := d + 2
      set L := (slopesBelow N).sort (· ≤ ·)
      have hL : L.Nodup := Finset.sort_nodup _ _
      have hsL : s ∈ L := by
        rw [Finset.mem_sort, mem_slopesBelow]
        have : rlen s ≤ d := by rw [← hsj]; exact Nat.le_mul_of_pos_left _ hj
        simp only [N]; omega
      have hcoef : ∀ i : Fin 2, (if i = 0 then ((ray s).2 : ℚ) else -((ray s).1 : ℚ)) *
          (PowerSeries.coeff j (f s) - PowerSeries.coeff j (f' s)) = 0 := by
        intro i
        have hp := prodL_pert hf hf' hd1 L (fun t _ => hd t) (ord_X i)
        have hdiff : Ord N (prodL f L (X i) - prodL f' L (X i)) := by
          have a := eqMod_iff.mp ((hgf N i).trans' (hgf' N i).symm')
          simpa [orderedProd_eq] using a
        have hsum := (hdiff.sub hp)
        simp only [sub_sub_cancel] at hsum
        have hdeg : (Finsupp.single i 1 + j • rvec s).degree < N := by
          rw [map_add, map_nsmul, rvec_degree, smul_eq_mul, hsj]; simp [N]; omega
        rw [← coeff_pertSum f f' i L hL hsL hj]
        exact ord_iff.mp hsum _ hdeg
      have h0 := hcoef 0
      have h1 := hcoef 1
      simp only [if_true, if_neg (show (1 : Fin 2) ≠ 0 by decide)] at h0 h1
      have hr := rlen_pos s
      simp only [rlen] at hr
      rcases Nat.eq_zero_or_pos (ray s).2 with h2 | h2
      · have : ((ray s).1 : ℚ) ≠ 0 := by exact_mod_cast (show (ray s).1 ≠ 0 by omega)
        have := (mul_eq_zero.mp h1).resolve_left (neg_ne_zero.mpr this)
        linarith
      · have : ((ray s).2 : ℚ) ≠ 0 := by exact_mod_cast (show (ray s).2 ≠ 0 by omega)
        have := (mul_eq_zero.mp h0).resolve_left this
        linarith
  funext s
  ext j
  exact key _ s j rfl

end ErsConj13.Scat
