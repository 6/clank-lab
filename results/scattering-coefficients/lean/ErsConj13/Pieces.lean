import ErsConj13.Calculus

/-!
# The proof of the Main Lemma, in six pieces

Log-free version. The paper puts logarithms in `A_L = A[L_u, L_w]`. Here they are
replaced by two exact multiplicative facts:
* the cocycle `μ_φ = (φ u / u) / (φ w / w)`, used in its cross-multiplied form (piece 2c,
  `cocycle`), which replaces `(4.1)`; and
* conjugation of the Euler derivation `E = u∂_u + w∂_w` (piece 1, `euler_conj`):
  `φ ∘ E = (E + {log μ_φ, ·}) ∘ φ`, multiplied through by `φ(u)/u · φ(w)/w`.
`{L_u − L_w, ·} = E`, so this is the content of the paper's statement that the extension `g̃` is Poisson, for `L_u − L_w`.
The h-splitting of `log(1+P)` (Lemma E) becomes a unique factorization in
`(1 + 𝒪_{≤−1}) · ℚ⟦uw⟧ˣ · (1 + 𝒪_{≥1})` (piece 2, `unique_factor`).
-/

noncomputable section

namespace ErsConj13

/-- The Euler derivation `E = u∂_u + w∂_w` (`= {L_u − L_w, ·}` in the paper). -/
def euler (f : A) : A := zd 0 f + zd 1 f

/-- `t d/dt` on `ℚ⟦t⟧` (written `′` in the paper). -/
def tD (f : PowerSeries ℚ) : PowerSeries ℚ := PowerSeries.X * PowerSeries.derivative ℚ f

section tDcalc
open PowerSeries

lemma tD_mul (f g : PowerSeries ℚ) : tD (f * g) = tD f * g + f * tD g := by
  simp only [tD, Derivation.leibniz, smul_eq_mul]; ring
lemma tD_add (f g : PowerSeries ℚ) : tD (f + g) = tD f + tD g := by
  simp only [tD, map_add]; ring
lemma tD_sub (f g : PowerSeries ℚ) : tD (f - g) = tD f - tD g := by
  simp only [tD, map_sub]; ring
lemma tD_one : tD 1 = 0 := by simp [tD]
lemma tD_X : tD X = X := by simp [tD]
lemma tD_two : tD 2 = 0 := by
  rw [show (2 : ℚ⟦X⟧) = 1 + 1 by norm_num, tD_add, tD_one, add_zero]
lemma tD_pow (f : PowerSeries ℚ) (n : ℕ) : tD (f ^ (n + 1)) = (n + 1 : ℚ⟦X⟧) * f ^ n * tD f := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, tD_mul, ih]; push_cast; ring
lemma coeff_tD (f : PowerSeries ℚ) (n : ℕ) : coeff n (tD f) = n * coeff n f := by
  rcases n with _ | k
  · simp [tD]
  · simp [tD, coeff_succ_X_mul, coeff_derivative]; ring

end tDcalc

/-- `g` commutes with the bracket. -/
def IsPoisson (g : A ≃+* A) : Prop := ∀ f h, g (bracket f h) = bracket (g f) (g h)

/-! ## Basic calculus (used by several pieces) -/

lemma coeff_zd (i : Fin 2) (f : A) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (zd i f) = (e i : ℚ) * MvPowerSeries.coeff e f := rfl

lemma zd_add (i : Fin 2) (f g : A) : zd i (f + g) = zd i f + zd i g := by
  ext e; simp only [coeff_zd, map_add]; ring

lemma zd_one (i : Fin 2) : zd i 1 = 0 := by
  ext e; rw [coeff_zd, MvPowerSeries.coeff_one, map_zero]
  split_ifs with h <;> simp [h]

lemma zd_X (i j : Fin 2) : zd i (MvPowerSeries.X j) = if i = j then MvPowerSeries.X j else 0 := by
  ext e; rw [coeff_zd, MvPowerSeries.coeff_X]
  by_cases hij : i = j
  · subst hij; split_ifs with h h' <;> simp_all [MvPowerSeries.coeff_X]
  · rw [if_neg hij]
    split_ifs with h
    · simp [h, Ne.symm hij]
    · simp

lemma zd_mul (i : Fin 2) (f g : A) : zd i (f * g) = zd i f * g + f * zd i g := by
  classical
  ext e
  simp only [coeff_zd, map_add, MvPowerSeries.coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [← this, Finsupp.add_apply]; push_cast; ring

lemma bracket_mul_left (f g h : A) : bracket (f * g) h = f * bracket g h + g * bracket f h := by
  simp only [bracket, zd_mul]; ring

lemma bracket_add_left (f g h : A) : bracket (f + g) h = bracket f h + bracket g h := by
  simp only [bracket, zd_add]; ring

lemma bracket_one_left (h : A) : bracket 1 h = 0 := by
  simp only [bracket, zd_one]; ring

lemma bracket_pow_left (f h : A) (n : ℕ) :
    bracket (f ^ (n + 1)) h = ((n + 1 : ℕ) : A) * f ^ n * bracket f h := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, bracket_mul_left, ih]; push_cast; ring

/-- `diag` as a ring hom `ℚ⟦t⟧ → A`, `t ↦ uw`. -/
def diagHom : PowerSeries ℚ →+* A where
  toFun := diag
  map_one' := diag_one
  map_mul' := diag_mul
  map_zero' := diag_zero
  map_add' := diag_add

lemma diag_pow (f : PowerSeries ℚ) (n : ℕ) : diag (f ^ n) = diag f ^ n :=
  map_pow diagHom f n

lemma one_add_u_ne_zero : (1 + u : A) ≠ 0 := by
  intro h
  have := congrArg MvPowerSeries.constantCoeff h
  simp at this

lemma X_ne_zero' (i : Fin 2) : (MvPowerSeries.X i : A) ≠ 0 := by
  intro h
  have := congrArg (MvPowerSeries.coeff (Finsupp.single i 1)) h
  simp [MvPowerSeries.coeff_X] at this

lemma u_mul_w_ne_zero : u * w ≠ 0 := mul_ne_zero (X_ne_zero' _) (X_ne_zero' _)

/-! ## Piece 2: h-filtration calculus (basic closure lemmas are in `ErsConj13.Calculus`) -/

lemma u_mem_OGe_θ : u ∈ OGe (-1) := by
  intro e he
  rw [u, MvPowerSeries.X_def, MvPowerSeries.coeff_monomial] at he
  split_ifs at he with h
  · subst h; simp [hdeg]
  · exact absurd rfl he

lemma zero_mem_OGe_θ (k : ℤ) : (0 : A) ∈ OGe k := by
  intro e he; simp at he

lemma C_mem_OGe_θ (c : ℚ) : (MvPowerSeries.C c : A) ∈ OGe 0 := by
  intro e he
  rw [MvPowerSeries.coeff_C] at he
  split_ifs at he with h
  · subst h; simp [hdeg]
  · exact absurd rfl he

lemma pow_mem_OGe_θ {a : ℤ} {x : A} (hx : x ∈ OGe a) (n : ℕ) : x ^ n ∈ OGe (n * a) := by
  induction n with
  | zero =>
    intro e he
    rw [pow_zero, MvPowerSeries.coeff_one] at he
    split_ifs at he with h
    · subst h; simp [hdeg]
    · exact absurd rfl he
  | succ n ih =>
    rw [pow_succ]
    have := OGe_mul ih hx
    convert this using 2; push_cast; ring

lemma sum_mem_OGe_θ {ι : Type*} (s : Finset ι) (k : ℤ) (f : ι → A)
    (h : ∀ i ∈ s, f i ∈ OGe k) : (∑ i ∈ s, f i) ∈ OGe k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_mem_OGe_θ k
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact OGe_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma monomial_eq_θ (p : Fin 2 →₀ ℕ) (c : ℚ) :
    (MvPowerSeries.monomial p c : A) =
      MvPowerSeries.C c * MvPowerSeries.X 0 ^ (p 0) * MvPowerSeries.X 1 ^ (p 1) := by
  have hp : p = Finsupp.single 0 (p 0) + Finsupp.single 1 (p 1) := fin2_ext (by simp) (by simp)
  conv_lhs => rw [hp]
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, ← MvPowerSeries.monomial_zero_eq_C,
    MvPowerSeries.monomial_mul_monomial, MvPowerSeries.monomial_mul_monomial, mul_one, mul_one,
    zero_add]

lemma coeff_Xpow_mul_θ (s : Fin 2) (n : ℕ) (φ : A) (e : Fin 2 →₀ ℕ) (h : e s < n) :
    MvPowerSeries.coeff e (MvPowerSeries.X s ^ n * φ) = 0 := by
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial_mul, if_neg]
  rw [Finsupp.single_le_iff]; omega

lemma decomp_θ (r : A) (N : ℕ)
    (hr : ∀ q : Fin 2 →₀ ℕ, q 0 < N → q 1 < N → MvPowerSeries.coeff q r = 0) :
    ∃ g₁ g₂ : A, r = MvPowerSeries.X 0 ^ N * g₁ + MvPowerSeries.X 1 ^ N * g₂ := by
  classical
  let g₁ : A := fun q => MvPowerSeries.coeff (q + Finsupp.single 0 N) r
  let g₂ : A := fun q => if q 0 < N then MvPowerSeries.coeff (q + Finsupp.single 1 N) r else 0
  have c1 : ∀ q, MvPowerSeries.coeff q g₁ = MvPowerSeries.coeff (q + Finsupp.single 0 N) r :=
    fun q => rfl
  have c2 : ∀ q, MvPowerSeries.coeff q g₂ =
      if q 0 < N then MvPowerSeries.coeff (q + Finsupp.single 1 N) r else 0 := fun q => rfl
  refine ⟨g₁, g₂, ?_⟩
  ext q
  rw [map_add, MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq,
    MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul, c1, c2]
  simp only [Finsupp.single_le_iff, one_mul]
  by_cases h0 : N ≤ q 0
  · rw [if_pos h0, tsub_add_cancel_of_le (by rwa [Finsupp.single_le_iff])]
    simp
    intros; omega
  · rw [if_neg h0, zero_add]
    by_cases h1 : N ≤ q 1
    · have : (q - Finsupp.single 1 N : Fin 2 →₀ ℕ) 0 < N := by simp; omega
      rw [if_pos h1, if_pos this, tsub_add_cancel_of_le (by rwa [Finsupp.single_le_iff])]
    · rw [if_neg h1]; exact hr q (by omega) (by omega)

/-- The continuity piece: the diagonal wall preserves each `𝒪_{≥k}`. It needs automatic
continuity (a ring automorphism of the local ring `A` preserves `𝔪^N`, so it is determined
modulo `𝔪^N` by its values on `u`, `w`), together with `θ(z^m) = z^m F(uw)^{−h(m)}` (`h` the `h`-degree). -/
lemma theta_OGe (θ : A ≃+* A) (F : PowerSeries ℚ) (hF : PowerSeries.constantCoeff F = 1)
    (hθu : θ u = u * diag F) (hθw : θ w * diag F = w) {k : ℤ} {f : A} (hf : f ∈ OGe k) :
    θ f ∈ OGe k := by
  classical
  have hθw' : θ w = w * diag F⁻¹ := by
    have h1 : diag F * diag F⁻¹ = 1 := by
      rw [← diag_mul, PowerSeries.mul_inv_cancel F (by rw [hF]; norm_num), diag_one]
    calc θ w = θ w * (diag F * diag F⁻¹) := by rw [h1, mul_one]
      _ = w * diag F⁻¹ := by rw [← mul_assoc, hθw]
  have hC : ∀ c : ℚ, θ (MvPowerSeries.C c) = MvPowerSeries.C c := by
    intro c
    rw [MvPowerSeries.c_eq_algebraMap]
    exact RingHom.map_rat_algebraMap θ.toRingHom c
  have hmon : ∀ p c, θ (MvPowerSeries.monomial p c) ∈ OGe (hdeg p) := by
    intro p c
    rw [monomial_eq_θ, map_mul, map_mul, map_pow, map_pow, hC]
    change MvPowerSeries.C c * θ u ^ (p 0) * θ w ^ (p 1) ∈ _
    rw [hθu, hθw']
    have h := OGe_mul (OGe_mul (C_mem_OGe_θ c)
      (pow_mem_OGe_θ (OGe_mul u_mem_OGe_θ (diag_mem_OGe F)) (p 0)))
      (pow_mem_OGe_θ (w_mul_diag_mem F⁻¹) (p 1))
    convert h using 2; simp only [hdeg]; ring
  intro e he
  set N := e 0 + e 1 + 1 with hN
  set box := (Finset.Iic (dm N)).filter (fun p : Fin 2 →₀ ℕ => p 0 < N ∧ p 1 < N) with hbox
  set g : A := ∑ p ∈ box, MvPowerSeries.monomial p (MvPowerSeries.coeff p f) with hg
  have hθg : θ g ∈ OGe k := by
    rw [hg, map_sum]
    apply sum_mem_OGe_θ
    intro p _
    by_cases hp : MvPowerSeries.coeff p f = 0
    · rw [hp, map_zero, map_zero]; exact zero_mem_OGe_θ k
    · exact OGe_mono (hf p hp) (hmon p _)
  have hcg : ∀ q : Fin 2 →₀ ℕ, q 0 < N → q 1 < N →
      MvPowerSeries.coeff q (f - g) = 0 := by
    intro q h0 h1
    have hq : q ∈ box := by
      rw [hbox, Finset.mem_filter, Finset.mem_Iic]
      refine ⟨?_, h0, h1⟩
      intro i; fin_cases i <;> simp <;> omega
    rw [map_sub, hg, map_sum]
    simp only [MvPowerSeries.coeff_monomial]
    rw [Finset.sum_ite_eq box q, if_pos hq, sub_self]
  obtain ⟨g₁, g₂, hr⟩ := decomp_θ (f - g) N hcg
  have hθr : MvPowerSeries.coeff e (θ (f - g)) = 0 := by
    rw [hr, map_add, map_mul, map_mul, map_pow, map_pow]
    change MvPowerSeries.coeff e (θ u ^ N * θ g₁ + θ w ^ N * θ g₂) = 0
    rw [hθu, hθw', mul_pow, mul_pow, mul_assoc, mul_assoc, map_add,
      coeff_Xpow_mul_θ 0 N _ e (by omega), coeff_Xpow_mul_θ 1 N _ e (by omega), add_zero]
  have hfe : MvPowerSeries.coeff e (θ f) = MvPowerSeries.coeff e (θ g) := by
    have := hθr
    rw [map_sub, map_sub, sub_eq_zero] at this
    exact this
  rw [hfe] at he
  exact hθg e he

lemma fin2_ne_zero_sum {b : Fin 2 →₀ ℕ} (hb : b ≠ 0) : b 0 ≠ 0 ∨ b 1 ≠ 0 := by
  by_contra hc; simp only [not_or, not_not] at hc
  exact hb (fin2_ext (by simp [hc.1]) (by simp [hc.2]))

lemma inv_mem_OLe {x v : A} (hx : x - 1 ∈ OLe (-1)) (hv : v * x = 1) : v - 1 ∈ OLe (-1) := by
  have key : ∀ n : ℕ, ∀ e : Fin 2 →₀ ℕ, e 0 + e 1 = n → 0 ≤ hdeg e →
      MvPowerSeries.coeff e (v - 1) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro e hn he
      by_contra hne
      have h1 : v - 1 = -(v * (x - 1)) := by linear_combination hv
      rw [h1, map_neg, neg_eq_zero] at hne
      obtain ⟨a, b, hab, ha, hb⟩ := exists_mul_ne_zero hne
      have hbd := hx b hb
      have hb0 : b ≠ 0 := by rintro rfl; simp [hdeg] at hbd
      have hda : 1 ≤ hdeg a := by have := hdeg_add a b; rw [hab] at this; linarith
      have ha0 : a ≠ 0 := by rintro rfl; simp [hdeg] at hda
      have hlt : a 0 + a 1 < n := by
        have h0 : e 0 = a 0 + b 0 := by rw [← hab]; rfl
        have h1 : e 1 = a 1 + b 1 := by rw [← hab]; rfl
        have := fin2_ne_zero_sum hb0
        omega
      have hz := ih _ hlt a rfl (by linarith)
      apply ha
      have : MvPowerSeries.coeff a (v - 1) = MvPowerSeries.coeff a v := by
        simp [MvPowerSeries.coeff_one, ha0]
      rw [← this, hz]
  intro e he
  by_contra hlt; rw [not_le] at hlt
  exact he (key _ e rfl (by omega))

lemma inv_mem_OGe {x v : A} (hx : x - 1 ∈ OGe 1) (hv : v * x = 1) : v - 1 ∈ OGe 1 := by
  have key : ∀ n : ℕ, ∀ e : Fin 2 →₀ ℕ, e 0 + e 1 = n → hdeg e ≤ 0 →
      MvPowerSeries.coeff e (v - 1) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro e hn he
      by_contra hne
      have h1 : v - 1 = -(v * (x - 1)) := by linear_combination hv
      rw [h1, map_neg, neg_eq_zero] at hne
      obtain ⟨a, b, hab, ha, hb⟩ := exists_mul_ne_zero hne
      have hbd := hx b hb
      have hb0 : b ≠ 0 := by rintro rfl; simp [hdeg] at hbd
      have hda : hdeg a ≤ -1 := by have := hdeg_add a b; rw [hab] at this; linarith
      have ha0 : a ≠ 0 := by rintro rfl; simp [hdeg] at hda
      have hlt : a 0 + a 1 < n := by
        have h0 : e 0 = a 0 + b 0 := by rw [← hab]; rfl
        have h1 : e 1 = a 1 + b 1 := by rw [← hab]; rfl
        have := fin2_ne_zero_sum hb0
        omega
      have hz := ih _ hlt a rfl (by linarith)
      apply ha
      have : MvPowerSeries.coeff a (v - 1) = MvPowerSeries.coeff a v := by
        simp [MvPowerSeries.coeff_one, ha0]
      rw [← this, hz]
  intro e he
  by_contra hlt; rw [not_le] at hlt
  exact he (key _ e rfl (by omega))

lemma constantCoeff_ne_zero_of_OLe {x : A} (hx : x - 1 ∈ OLe (-1)) :
    MvPowerSeries.constantCoeff x ≠ 0 := by
  have h0 : MvPowerSeries.coeff 0 (x - 1) = 0 := by
    by_contra hc; have := hx 0 hc; simp [hdeg] at this
  rw [map_sub, MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at h0
  simp at h0
  rw [sub_eq_zero] at h0
  rw [h0]; exact one_ne_zero

lemma constantCoeff_ne_zero_of_OGe {x : A} (hx : x - 1 ∈ OGe 1) :
    MvPowerSeries.constantCoeff x ≠ 0 := by
  have h0 : MvPowerSeries.coeff 0 (x - 1) = 0 := by
    by_contra hc; have := hx 0 hc; simp [hdeg] at this
  rw [map_sub, MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at h0
  simp at h0
  rw [sub_eq_zero] at h0
  rw [h0]; exact one_ne_zero

lemma OLe_inter_OGe {m : A} (h1 : m ∈ OLe (-1)) (h2 : m ∈ OGe 1) : m = 0 := by
  ext e
  by_contra hc
  have a := h1 e hc
  have b := h2 e hc
  simp only [map_zero] at hc
  linarith

lemma diag_ne_zero {y : PowerSeries ℚ} (hy : IsUnit y) : diag y ≠ 0 := by
  intro h
  have := congrArg (MvPowerSeries.coeff 0) h
  rw [coeff_diag] at this
  simp only [Finsupp.coe_zero, Pi.zero_apply, if_true, map_zero] at this
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
  exact (hy.map PowerSeries.constantCoeff).ne_zero this

/-- Unique factorization in `(1 + 𝒪_{≤−1}) · ℚ⟦uw⟧ˣ · (1 + 𝒪_{≥1})`: the log-free form of
the h-splitting of `log(1+P)` in Lemma E. -/
lemma unique_factor {x x' z z' : A} {y y' : PowerSeries ℚ}
    (hx : x - 1 ∈ OLe (-1)) (hx' : x' - 1 ∈ OLe (-1))
    (hz : z - 1 ∈ OGe 1) (hz' : z' - 1 ∈ OGe 1)
    (hy : IsUnit y) (hy' : IsUnit y')
    (h : x * diag y * z = x' * diag y' * z') : y = y' ∧ x = x' ∧ z = z' := by
  set v' := x'⁻¹ with hv'def
  set t := z⁻¹ with htdef
  have hv'x' : v' * x' = 1 := MvPowerSeries.inv_mul_cancel _ (constantCoeff_ne_zero_of_OLe hx')
  have hzt : z * t = 1 := MvPowerSeries.mul_inv_cancel _ (constantCoeff_ne_zero_of_OGe hz)
  have hv' : v' - 1 ∈ OLe (-1) := inv_mem_OLe hx' hv'x'
  have ht : t - 1 ∈ OGe 1 := inv_mem_OGe hz (by rw [mul_comm]; exact hzt)
  set a := v' * x with hadef
  set b := z' * t with hbdef
  have ha : a - 1 ∈ OLe (-1) := oneLe_mul hv' hx
  have hb : b - 1 ∈ OGe 1 := oneGe_mul hz' ht
  have hLR : a * diag y = diag y' * b := by
    rw [hadef, hbdef]
    linear_combination (v' * t) * h - (v' * x * diag y) * hzt + (diag y' * z' * t) * hv'x'
  have hL : (a - 1) * diag y ∈ OLe (-1) := by
    simpa using OLe_mul ha (diag_mem_OLe y)
  have hR : diag y' * (b - 1) ∈ OGe 1 := by
    simpa using OGe_mul (diag_mem_OGe y') hb
  have hD : diag y = diag y' := by
    ext e
    rw [coeff_diag, coeff_diag]
    by_cases he : e 0 = e 1
    · have hd : hdeg e = 0 := by simp [hdeg, he]
      have c1 : MvPowerSeries.coeff e ((a - 1) * diag y) = 0 := by
        by_contra hc; have := hL e hc; omega
      have c2 : MvPowerSeries.coeff e (diag y' * (b - 1)) = 0 := by
        by_contra hc; have := hR e hc; omega
      have c3 := congrArg (MvPowerSeries.coeff e) hLR
      rw [sub_mul, one_mul, map_sub] at c1
      rw [mul_sub, mul_one, map_sub] at c2
      have : MvPowerSeries.coeff e (diag y) = MvPowerSeries.coeff e (diag y') := by
        rw [sub_eq_zero] at c1 c2
        rw [← c1, ← c2, c3]
      rwa [coeff_diag, coeff_diag] at this
    · rw [if_neg he, if_neg he]
  have hyy : y = y' := diag_injective hD
  subst hyy
  have hm : (a - 1) * diag y = diag y * (b - 1) := by
    linear_combination hLR
  have hm0 : (a - 1) * diag y = 0 := OLe_inter_OGe hL (hm ▸ hR)
  have hm1 : diag y * (b - 1) = 0 := hm ▸ hm0
  have hDne := diag_ne_zero hy
  have ha1 : a = 1 := by
    rcases mul_eq_zero.mp hm0 with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 hDne
  have hb1 : b = 1 := by
    rcases mul_eq_zero.mp hm1 with h1 | h1
    · exact absurd h1 hDne
    · exact sub_eq_zero.mp h1
  have hxx : x = x' := by
    have hx'v' : x' * v' = 1 := by rw [mul_comm]; exact hv'x'
    linear_combination x' * ha1 - x * hx'v'
  have hzz : z = z' := by
    linear_combination (-z) * hb1 + z' * hzt
  exact ⟨rfl, hxx, hzz⟩

open Polynomial in
/-- Lemma E's quadratic: `ρ² − (1+β)ρ + tF = 0` has a root `ρ ∈ 1 + tℚ⟦t⟧`; `δ := F/ρ`.
(In the paper's notation, `ρ = −w₂` and `d = tδ = −w₁`.) -/
lemma quad_root (F β : PowerSeries ℚ) (_hF : PowerSeries.constantCoeff F = 1)
    (hβ : PowerSeries.constantCoeff β = 0) :
    ∃ ρ δ : PowerSeries ℚ, PowerSeries.constantCoeff ρ = 1 ∧ ρ * δ = F ∧
      ρ + PowerSeries.X * δ = 1 + β := by
  set I : Ideal (PowerSeries ℚ) := Ideal.span {PowerSeries.X}
  set f : (PowerSeries ℚ)[X] := X * (X - C (1 + β)) + C (PowerSeries.X * F) with hf
  have hmon : f.Monic := by
    rw [hf]; monicity!
  have hmem : ∀ g : PowerSeries ℚ, PowerSeries.constantCoeff g = 0 → g ∈ I := by
    intro g hg
    exact Ideal.mem_span_singleton.mpr ((PowerSeries.X_dvd_iff).mpr hg)
  have h1 : f.eval 1 ∈ I := by
    apply hmem; simp [f, hβ]
  have h2 : IsUnit (Ideal.Quotient.mk I (f.derivative.eval 1)) := by
    apply IsUnit.map
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp [f, hβ]
  obtain ⟨ρ, hroot, hsub⟩ := HenselianRing.is_henselian f hmon 1 h1 h2
  have hρ : PowerSeries.constantCoeff ρ = 1 := by
    have := Ideal.mem_span_singleton.mp hsub
    rw [PowerSeries.X_dvd_iff] at this
    simpa [sub_eq_zero] using this
  have hρ0 : PowerSeries.constantCoeff ρ ≠ 0 := by rw [hρ]; norm_num
  have heq : ρ * (ρ - (1 + β)) + PowerSeries.X * F = 0 := by
    simpa [f] using hroot
  have hinv : ρ * ρ⁻¹ = 1 := PowerSeries.mul_inv_cancel ρ hρ0
  refine ⟨ρ, ρ⁻¹ * F, hρ, ?_, ?_⟩
  · rw [← mul_assoc, hinv, one_mul]
  · have hne : ρ ≠ 0 := by
      intro h; apply hρ0; rw [h]; simp
    apply mul_left_cancel₀ hne
    calc ρ * (ρ + PowerSeries.X * (ρ⁻¹ * F))
        = ρ * ρ + PowerSeries.X * F * (ρ * ρ⁻¹) := by ring
      _ = ρ * (1 + β) := by rw [hinv]; linear_combination heq

/-- Lemma E's factorization `1 + P = ρ (1 − w₁/w)(1 − w/w₂)`, written as
`ρ̂ (1 + u δ̂)(1 + w ρ̂⁻¹)`, with `ρ̂ (1 + w ρ̂⁻¹) = ρ̂ + w`. -/
lemma one_add_P_factor (F β ρ δ : PowerSeries ℚ) (h1 : ρ * δ = F)
    (h2 : ρ + PowerSeries.X * δ = 1 + β) :
    1 + (u * diag F + diag β + w) = (diag ρ + w) * (1 + u * diag δ) := by
  have hF : diag F = diag ρ * diag δ := by rw [← h1, diag_mul]
  have hβ : diag ρ + u * w * diag δ = 1 + diag β := by
    rw [← diag_X, ← diag_mul, ← diag_add, h2, diag_add, diag_one]
  rw [hF]; linear_combination (-1 : A) * hβ

/-! ## Piece 3: `T` explicit, and the filtration lemma -/

lemma T_fix_s (T : A ≃+* A) (hTu : T u * (1 + u) = u * (1 + u + w))
    (hTw : T w * (1 + u) = w) : T (u + w) = u + w := by
  refine mul_right_cancel₀ one_add_u_ne_zero ?_
  rw [map_add, add_mul, hTu, hTw]; ring

lemma T_iter_fix_s (T : A ≃+* A) (hTu : T u * (1 + u) = u * (1 + u + w))
    (hTw : T w * (1 + u) = w) (n : ℕ) : (⇑T)^[n] (u + w) = u + w := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, T_fix_s T hTu hTw]

/-- `T^n(u)/T^n(w) = (1+s)^n u/w`, cross-multiplied. -/
lemma T_iter_ratio (T : A ≃+* A) (hTu : T u * (1 + u) = u * (1 + u + w))
    (hTw : T w * (1 + u) = w) (n : ℕ) :
    (⇑T)^[n] u * w = (1 + (u + w)) ^ n * u * (⇑T)^[n] w := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hTw0 : T w ≠ 0 := by
      intro h; rw [h, zero_mul] at hTw; exact X_ne_zero' _ hTw.symm
    have h1 := congrArg T ih
    simp only [map_mul, map_pow, map_add, map_one, T_fix_s T hTu hTw] at h1
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    -- h1 : T(T^n u) * T w = (1+(u+w))^n * T u * T(T^n w)
    refine mul_right_cancel₀ (mul_ne_zero hTw0 one_add_u_ne_zero) ?_
    linear_combination (w * (1 + u)) * h1 + ((1 + (u + w)) ^ n * T ((⇑T)^[n] w) * w) * hTu
      - ((1 + (u + w)) ^ n * T ((⇑T)^[n] w) * u * (1 + u + w)) * hTw

lemma u_mem_OGe : u ∈ OGe (-1) := by
  intro e he
  rw [u, MvPowerSeries.X_def, MvPowerSeries.coeff_monomial] at he
  split_ifs at he with h
  · subst h; simp [hdeg]
  · exact absurd rfl he

lemma w_mem_OLe : w ∈ OLe 1 := by
  intro e he
  rw [w, MvPowerSeries.X_def, MvPowerSeries.coeff_monomial] at he
  split_ifs at he with h
  · subst h; simp [hdeg]
  · exact absurd rfl he

lemma coeff_eq_zero_of_OLe {k : ℤ} {f : A} (hf : f ∈ OLe k) {e : Fin 2 →₀ ℕ} (he : k < hdeg e) :
    MvPowerSeries.coeff e f = 0 := by
  by_contra h; have := hf e h; omega

lemma coeff_eq_zero_of_OGe {k : ℤ} {f : A} (hf : f ∈ OGe k) {e : Fin 2 →₀ ℕ} (he : hdeg e < k) :
    MvPowerSeries.coeff e f = 0 := by
  by_contra h; have := hf e h; omega

/-- Lemma V1: `P := g_<⁻¹(u+w)` has h-parts only in `{−1, 0, 1}`, with `π₋₁ P = u F(uw)` and
`π₁ P = w`. -/
lemma V1 (T θ gl gr : A ≃+* A) (F : PowerSeries ℚ)
    (hTu : T u * (1 + u) = u * (1 + u + w)) (hTw : T w * (1 + u) = w)
    (hF : PowerSeries.constantCoeff F = 1)
    (hθu : θ u = u * diag F) (hθw : θ w * diag F = w)
    (a₁ a₂ b₁ b₂ : A) (ha₁ : a₁ ∈ OLe (-1)) (ha₂ : a₂ ∈ OLe (-1))
    (hb₁ : b₁ ∈ OGe 1) (hb₂ : b₂ ∈ OGe 1)
    (hgl_u : gl.symm u = u * (1 + a₁)) (hgl_w : gl.symm w = w * (1 + a₂))
    (hgr_u : gr u = u * (1 + b₁)) (hgr_w : gr w = w * (1 + b₂))
    (hfac : ∀ f, (⇑T)^[5] f = gl (θ (gr f))) :
    ∃ β : PowerSeries ℚ, PowerSeries.constantCoeff β = 0 ∧
      gl.symm (u + w) = u * diag F + diag β + w := by
  set P := gl.symm (u + w) with hPdef
  have hPθ : P = θ (gr (u + w)) := by
    have h := hfac (u + w)
    rw [T_iter_fix_s T hTu hTw] at h
    rw [hPdef]; nth_rewrite 1 [h]; exact RingEquiv.symm_apply_apply _ _
  have hθw' : θ w = w * diag F⁻¹ := by
    have hinv : F * F⁻¹ = 1 := PowerSeries.mul_inv_cancel F (by rw [hF]; norm_num)
    have : diag F * diag F⁻¹ = 1 := by rw [← diag_mul, hinv, diag_one]
    linear_combination (diag F⁻¹) * hθw - (θ w) * this
  -- P − w has h ≤ 0
  have hP1 : P - w ∈ OLe 0 := by
    have : P - w = u + u * a₁ + w * a₂ := by rw [hPdef, map_add, hgl_u, hgl_w]; ring
    rw [this]
    refine OLe_add (OLe_add (OLe_mono (by norm_num) u_mem) ?_) ?_
    · exact OLe_mono (by norm_num) (OLe_mul u_mem ha₁)
    · exact OLe_mono (by norm_num) (OLe_mul w_mem_OLe ha₂)
  -- P − uF has h ≥ 0
  have hP2 : P - u * diag F ∈ OGe 0 := by
    have : P - u * diag F = u * diag F * θ b₁ + w * diag F⁻¹ * (1 + θ b₂) := by
      rw [hPθ, map_add, hgr_u, hgr_w, map_add, map_mul, map_mul, hθu, hθw', map_add, map_add,
        map_one]
      ring
    rw [this]
    have hθb₁ := theta_OGe θ F hF hθu hθw hb₁
    have hθb₂ := theta_OGe θ F hF hθu hθw hb₂
    refine OGe_add ?_ ?_
    · have := OGe_mul (OGe_mul u_mem_OGe (diag_mem_OGe F)) hθb₁
      simpa using this
    · have h1 : (1 + θ b₂) ∈ OGe 0 := by
        refine OGe_add ?_ (OGe_mono (by norm_num) hθb₂)
        intro e he
        rw [MvPowerSeries.coeff_one] at he
        split_ifs at he with h
        · subst h; simp [hdeg]
        · exact absurd rfl he
      have := OGe_mul (w_mul_diag_mem F⁻¹) h1
      exact OGe_mono (by norm_num) this
  refine ⟨PowerSeries.mk fun n => MvPowerSeries.coeff (dm n) P, ?_, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    have : dm 0 = 0 := by simp [dm]
    rw [this, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hPdef, map_add, hgl_u, hgl_w]
    simp
  · ext e
    rw [map_add, map_add, coeff_diag]
    rcases lt_trichotomy (hdeg e) 0 with hneg | hzero | hpos
    · -- h ≤ −1: P agrees with u F
      have h1 := coeff_eq_zero_of_OGe hP2 hneg
      have h2 : MvPowerSeries.coeff e w = 0 := coeff_eq_zero_of_OGe w_mem (by omega)
      have h3 : e 0 ≠ e 1 := by intro h; simp [hdeg, h] at hneg
      rw [map_sub] at h1
      rw [if_neg h3, h2]; linear_combination h1
    · have h0 : e 0 = e 1 := by simp only [hdeg] at hzero; omega
      have h1 : MvPowerSeries.coeff e (u * diag F) = 0 :=
        coeff_eq_zero_of_OLe (u_mul_diag_mem F) (by omega)
      have h2 : MvPowerSeries.coeff e w = 0 := coeff_eq_zero_of_OGe w_mem (by omega)
      rw [if_pos h0, PowerSeries.coeff_mk, h1, h2, ← eq_dm h0]; ring
    · have h1 := coeff_eq_zero_of_OLe hP1 hpos
      have h2 : MvPowerSeries.coeff e (u * diag F) = 0 :=
        coeff_eq_zero_of_OLe (u_mul_diag_mem F) (by omega)
      have h3 : e 0 ≠ e 1 := by intro h; simp [hdeg, h] at hpos
      rw [map_sub] at h1
      rw [if_neg h3, h2]; linear_combination h1

/-! ## Piece 2c: the multiplicative cocycle (replaces the logarithmic identity of the paper) -/

/-- `μ_{g_<⁻¹} · (1+P)⁵ = F² · θ(μ_{g_>})`, cross-multiplied, with
`μ_φ = (φ u/u)/(φ w/w)`. -/
lemma cocycle (T θ gl gr : A ≃+* A) (F : PowerSeries ℚ)
    (hTu : T u * (1 + u) = u * (1 + u + w)) (hTw : T w * (1 + u) = w)
    (hθu : θ u = u * diag F) (hθw : θ w * diag F = w)
    (a₁ a₂ b₁ b₂ : A)
    (hgl_u : gl.symm u = u * (1 + a₁)) (hgl_w : gl.symm w = w * (1 + a₂))
    (hgr_u : gr u = u * (1 + b₁)) (hgr_w : gr w = w * (1 + b₂))
    (hfac : ∀ f, (⇑T)^[5] f = gl (θ (gr f))) :
    (1 + a₂) * diag (F ^ 2) * θ (1 + b₁) =
      (1 + gl.symm (u + w)) ^ 5 * (1 + a₁) * θ (1 + b₂) := by
  have hX : ∀ f, gl.symm ((⇑T)^[5] f) = θ (gr f) := by
    intro f; rw [hfac, RingEquiv.symm_apply_apply]
  have h1 := congrArg gl.symm (T_iter_ratio T hTu hTw 5)
  rw [map_mul, map_mul, map_mul, map_pow, hX, hX, map_add, map_one] at h1
  rw [hgr_u, hgr_w, map_mul, map_mul, hθu, hgl_u, hgl_w] at h1
  rw [diag_pow]
  refine mul_left_cancel₀ u_mul_w_ne_zero ?_
  linear_combination (diag F) * h1 + ((1 + gl.symm (u + w)) ^ 5 * u * (1 + a₁) * θ (1 + b₂)) * hθw

lemma zero_mem_OLe (k : ℤ) : (0 : A) ∈ OLe k := fun e he => by simp at he

lemma zero_mem_OGe (k : ℤ) : (0 : A) ∈ OGe k := fun e he => by simp at he

lemma oneLe_pow {x : A} (hx : x - 1 ∈ OLe (-1)) (n : ℕ) : x ^ n - 1 ∈ OLe (-1) := by
  induction n with
  | zero => simpa using zero_mem_OLe (-1)
  | succ n ih => rw [pow_succ]; exact oneLe_mul ih hx

lemma oneGe_pow {x : A} (hx : x - 1 ∈ OGe 1) (n : ℕ) : x ^ n - 1 ∈ OGe 1 := by
  induction n with
  | zero => simpa using zero_mem_OGe 1
  | succ n ih => rw [pow_succ]; exact oneGe_mul ih hx

/-- Lemma E, conclusions (E1) and (E2), log-free: `F² = ρ⁵` and
`μ_{g_<⁻¹} = (1 + u δ̂)⁻⁵`, i.e. `1 + a₂ = (1 + u δ̂)⁵ (1 + a₁)`. -/
lemma lemma_E (θ : A ≃+* A) (F ρ δ : PowerSeries ℚ) (hF : PowerSeries.constantCoeff F = 1)
    (hρ : PowerSeries.constantCoeff ρ = 1)
    (hθu : θ u = u * diag F) (hθw : θ w * diag F = w)
    (a₁ a₂ b₁ b₂ : A) (ha₁ : a₁ ∈ OLe (-1)) (ha₂ : a₂ ∈ OLe (-1))
    (hb₁ : b₁ ∈ OGe 1) (hb₂ : b₂ ∈ OGe 1)
    (hcoc : (1 + a₂) * diag (F ^ 2) * θ (1 + b₁) =
      ((diag ρ + w) * (1 + u * diag δ)) ^ 5 * (1 + a₁) * θ (1 + b₂)) :
    F ^ 2 = ρ ^ 5 ∧ 1 + a₂ = (1 + u * diag δ) ^ 5 * (1 + a₁) := by
  have hinv : ρ * ρ⁻¹ = 1 := PowerSeries.mul_inv_cancel ρ (by rw [hρ]; norm_num)
  have hsplit : diag ρ + w = diag ρ * (1 + w * diag ρ⁻¹) := by
    have : diag ρ * diag ρ⁻¹ = 1 := by rw [← diag_mul, hinv, diag_one]
    linear_combination (-w) * this
  rw [hsplit, diag_pow] at hcoc
  have hθ1 : ∀ b, b ∈ OGe 1 → θ (1 + b) - 1 ∈ OGe 1 := by
    intro b hb; rw [map_add, map_one, add_sub_cancel_left]
    exact theta_OGe θ F hF hθu hθw hb
  have key := unique_factor (x := 1 + a₂) (y := F ^ 2) (z := θ (1 + b₁))
    (x' := (1 + u * diag δ) ^ 5 * (1 + a₁)) (y' := ρ ^ 5)
    (z' := (1 + w * diag ρ⁻¹) ^ 5 * θ (1 + b₂))
    (by rwa [add_sub_cancel_left])
    (oneLe_mul (oneLe_pow (by rw [add_sub_cancel_left]; exact u_mul_diag_mem δ) 5)
      (by rwa [add_sub_cancel_left]))
    (hθ1 b₁ hb₁)
    (oneGe_mul (oneGe_pow (by rw [add_sub_cancel_left]; exact w_mul_diag_mem _) 5) (hθ1 b₂ hb₂))
    (by rw [PowerSeries.isUnit_iff_constantCoeff]; simp [hF])
    (by rw [PowerSeries.isUnit_iff_constantCoeff]; simp [hρ])
    (by rw [diag_pow, diag_pow, hcoc]; ring)
  exact ⟨key.1, key.2.1⟩

/-! ## Piece 1: the Poisson layer (log-free) -/

lemma isPoisson_symm (g : A ≃+* A) (hg : IsPoisson g) : IsPoisson g.symm := by
  intro f h
  apply g.injective
  rw [hg, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

/-- `u w E(y) = w{u, y} − u{w, y}`. -/
lemma euler_eq_bracket (y : A) : u * w * euler y = w * bracket u y - u * bracket w y := by
  simp only [euler, bracket, zd_X]; simp; ring

lemma euler_s : euler (u + w) = u + w := by
  simp only [euler, zd_add, zd_X]; simp

/-- Conjugating the Euler derivation by a Poisson automorphism `φ` with `φ u = u α`,
`φ w = w β`: `φ ∘ E = (E + {log(α/β), ·}) ∘ φ`, multiplied through by `αβ`. This is the paper's
statement that `g̃` is Poisson, applied to `L_u − L_w`, and needs no logarithm. -/
lemma euler_conj (φ : A ≃+* A) (hφ : IsPoisson φ) (α β : A) (hα : φ u = u * α)
    (hβ : φ w = w * β) (y : A) :
    α * β * φ (euler y) = α * β * euler (φ y) + β * bracket α (φ y) - α * bracket β (φ y) := by
  have h1 := congrArg φ (euler_eq_bracket y)
  rw [map_mul, map_mul, map_sub, map_mul, map_mul, hφ, hφ, hα, hβ, bracket_mul_left,
    bracket_mul_left] at h1
  have h2 := euler_eq_bracket (φ y)
  refine mul_left_cancel₀ u_mul_w_ne_zero ?_
  linear_combination h1 - (α * β) * h2

lemma constantCoeff_eq_zero_of_OLe {a : A} (ha : a ∈ OLe (-1)) :
    MvPowerSeries.constantCoeff a = 0 := by
  by_contra h
  have := ha 0 (by rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply])
  simp [hdeg] at this

/-- Lemma SE (`{Q′, P} = P`), multiplied by the unit `1 + u δ̂ = 1 − w₁/w`. -/
lemma lemma_SE (Xg : A ≃+* A) (hX : IsPoisson Xg) (a₁ a₂ : A) (δ : PowerSeries ℚ)
    (ha₁ : a₁ ∈ OLe (-1))
    (hu : Xg u = u * (1 + a₁)) (hw : Xg w = w * (1 + a₂))
    (hE : 1 + a₂ = (1 + u * diag δ) ^ 5 * (1 + a₁)) :
    (1 + u * diag δ) * (euler (Xg (u + w)) - Xg (u + w)) =
      5 * bracket (u * diag δ) (Xg (u + w)) := by
  set P := Xg (u + w)
  set γ := 1 + u * diag δ
  have h1 := euler_conj Xg hX (1 + a₁) (1 + a₂) hu hw (u + w)
  rw [euler_s, hE, bracket_mul_left, bracket_pow_left _ _ 4, bracket_add_left,
    bracket_one_left] at h1
  have hα : (1 + a₁) ≠ 0 := by
    intro h; have := congrArg MvPowerSeries.constantCoeff h
    simp [constantCoeff_eq_zero_of_OLe ha₁] at this
  have hγ : γ ≠ 0 := by
    intro h; have := congrArg MvPowerSeries.constantCoeff h
    simp [γ] at this
  refine mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 hα) (pow_ne_zero 4 hγ)) ?_
  have hγb : bracket γ (Xg (u + w)) = bracket (u * diag δ) (Xg (u + w)) := by
    simp only [γ, bracket_add_left, bracket_one_left, zero_add]
  push_cast at h1
  linear_combination (-1 : A) * h1 + (5 * (1 + a₁) ^ 2 * γ ^ 4) * hγb

/-! ## Piece 4: the exact scalar identity and ODE uniqueness -/

/-- The scalar residual `2ρ′ − ρ + 1 − 3d′ − d` of ODE₅, with `d = tδ`. -/
def Φ (ρ δ : PowerSeries ℚ) : PowerSeries ℚ :=
  1 - ρ + 2 * tD ρ - 4 * PowerSeries.X * δ - 3 * PowerSeries.X * tD δ

/-- The `1/w` residual `[(2−c)dρ′ + 2ρ(d′ − d)]/t` (c = 5). -/
def Ψ (ρ δ : PowerSeries ℚ) : PowerSeries ℚ := 2 * ρ * tD δ - 3 * δ * tD ρ

lemma zd_sub (i : Fin 2) (f g : A) : zd i (f - g) = zd i f - zd i g := by
  ext e; simp only [coeff_zd, map_sub]; ring

lemma zd_diag (i : Fin 2) (f : PowerSeries ℚ) : zd i (diag f) = diag (tD f) := by
  ext e
  rw [coeff_zd, coeff_diag, coeff_diag, coeff_tD]
  split_ifs with h
  · fin_cases i <;> simp [h]
  · simp

lemma diag_eq_hom (f : PowerSeries ℚ) : diag f = diagHom f := rfl

/-- The exact identity, for any `ρ, δ`, with `P = (ρ̂ + w)(1 + uδ̂) − 1`. -/
lemma exact_identity (ρ δ : PowerSeries ℚ) :
    let γ := 1 + u * diag δ
    let P := (diag ρ + w) * γ - 1
    γ * (euler P - P) - 5 * bracket (u * diag δ) P = γ * (diag (Φ ρ δ) + u * diag (Ψ ρ δ)) := by
  intro γ P
  simp only [γ, P, euler, bracket, zd_mul, zd_add, zd_sub, zd_one, zd_X, zd_diag]
  simp only [diag_eq_hom, Φ, Ψ, map_sub, map_add, map_mul, map_one, map_ofNat]
  rw [← diag_eq_hom PowerSeries.X, diag_X]
  simp
  ring

/-- SE implies ODE₅ (the `h = 0` part of the exact identity). -/
lemma ode_of_SE (ρ δ : PowerSeries ℚ)
    (h : (1 + u * diag δ) * (euler ((diag ρ + w) * (1 + u * diag δ) - 1)
        - ((diag ρ + w) * (1 + u * diag δ) - 1)) =
      5 * bracket (u * diag δ) ((diag ρ + w) * (1 + u * diag δ) - 1)) :
    Φ ρ δ = 0 := by
  have hx := exact_identity ρ δ
  simp only at hx
  rw [h, sub_self] at hx
  have hγ : (1 + u * diag δ) ≠ 0 := by
    intro h0; have := congrArg MvPowerSeries.constantCoeff h0; simp at this
  have h2 := (mul_eq_zero.mp hx.symm).resolve_left hγ
  ext n
  have h3 := congrArg (MvPowerSeries.coeff (dm n)) h2
  rw [map_add, map_zero, coeff_diag] at h3
  have h4 : MvPowerSeries.coeff (dm n) (u * diag (Ψ ρ δ)) = 0 := by
    by_contra hne
    have := u_mul_diag_mem (Ψ ρ δ) (dm n) hne
    simp [hdeg] at this
  rw [h4, add_zero] at h3
  simpa using h3

section odeU
open PowerSeries

lemma coeff_X_mul' (f : PowerSeries ℚ) (n : ℕ) :
    coeff n (X * f) = if n = 0 then 0 else coeff (n - 1) f := by
  rcases n with _ | k
  · simp
  · simp [coeff_succ_X_mul]

lemma coeff_lin (f g : PowerSeries ℚ) (k : ℕ) :
    coeff k (-f + 2 * tD f - 4 * X * g - 3 * X * tD g) =
      (2 * (k : ℚ) - 1) * coeff k f
        - (if k = 0 then 0 else 4 * coeff (k - 1) g + 3 * coeff (k - 1) (tD g)) := by
  rw [show (4 : ℚ⟦X⟧) * X * g = X * (C (4 : ℚ) * g) by simp [map_ofNat]; ring,
    show (3 : ℚ⟦X⟧) * X * tD g = X * (C (3 : ℚ) * tD g) by simp [map_ofNat]; ring,
    show (2 : ℚ⟦X⟧) * tD f = C (2 : ℚ) * tD f by simp [map_ofNat]]
  simp only [map_sub, map_add, map_neg, coeff_X_mul', coeff_C_mul, coeff_tD]
  split_ifs <;> ring

/-- ODE uniqueness: `Φ(ρ, δ) = 0` and `δ² = ρ³` with `ρ(0) = δ(0) = 1` determine `ρ, δ`.
The `t^k` coefficient of `Φ` is `(2k−1)ρ_k − (3k+1)δ_{k−1}`. -/
lemma ode_unique (ρ δ ρ' δ' : PowerSeries ℚ)
    (_hρ : PowerSeries.constantCoeff ρ = 1) (hδ : PowerSeries.constantCoeff δ = 1)
    (_hρ' : PowerSeries.constantCoeff ρ' = 1) (hδ' : PowerSeries.constantCoeff δ' = 1)
    (h : Φ ρ δ = 0) (h' : Φ ρ' δ' = 0) (hsq : δ ^ 2 = ρ ^ 3) (hsq' : δ' ^ 2 = ρ' ^ 3) :
    ρ = ρ' ∧ δ = δ' := by
  set Dρ := ρ - ρ' with hDρ
  set Dδ := δ - δ' with hDδ
  have hlin : -Dρ + 2 * tD Dρ - 4 * X * Dδ - 3 * X * tD Dδ = 0 := by
    have : Φ ρ δ - Φ ρ' δ' = 0 := by rw [h, h', sub_zero]
    rw [← this]; simp only [Φ, hDρ, hDδ, tD_sub]; ring
  have hv : IsUnit (δ + δ') := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp [hδ, hδ']
  obtain ⟨v, hv⟩ := hv
  set m := (↑v⁻¹ : ℚ⟦X⟧) * (ρ ^ 2 + ρ * ρ' + ρ' ^ 2) with hm
  have hDδm : Dδ = m * Dρ := by
    have h1 : (δ + δ') * Dδ = (ρ ^ 2 + ρ * ρ' + ρ' ^ 2) * Dρ := by
      simp only [hDρ, hDδ]; linear_combination hsq - hsq'
    rw [hm, mul_assoc, ← h1, ← hv, ← mul_assoc, Units.inv_mul, one_mul]
  have key : ∀ n, ∀ k < n, coeff k Dρ = 0 := by
    intro n
    induction n with
    | zero => intro k hk; omega
    | succ n ih =>
      intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact ih k hk
      · have hc := congrArg (coeff k) hlin
        have hδk : k ≠ 0 → coeff (k - 1) Dδ = 0 := by
          intro _
          rw [hDδm, coeff_mul]
          refine Finset.sum_eq_zero fun p hp => ?_
          have : p.2 < k := by
            have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp; omega
          rw [ih p.2 this, mul_zero]
        have hδk' : k ≠ 0 → coeff (k - 1) (tD Dδ) = 0 := by
          intro hk0; rw [coeff_tD, hδk hk0, mul_zero]
        rw [coeff_lin] at hc
        have hk2 : (2 * (k : ℚ) - 1) ≠ 0 := by
          intro h2; have : (2 * k : ℚ) = 1 := by linarith
          have h3 : (2 * k : ℕ) = 1 := by exact_mod_cast this
          omega
        split_ifs at hc with hk0
        · simpa [hk2] using hc
        · rw [hδk hk0, hδk' hk0] at hc
          simpa [hk2] using hc
  have hD : Dρ = 0 := by
    ext k; rw [key (k + 1) k (Nat.lt_succ_self k), map_zero]
  refine ⟨sub_eq_zero.mp hD, sub_eq_zero.mp ?_⟩
  rw [← hDδ, hDδm, hD, mul_zero]

end odeU

/-! ## Piece 5: the c = 5 identity -/

/-- The cubic `K(S) = t²S³ − 2tS² + (1+t)S − (1+t)`, equivalent to the paper's
`S = Y/(1−v)`, `v = tS`, `Y² = Y + v`. -/
def K (S : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.X ^ 2 * S ^ 3 - 2 * PowerSeries.X * S ^ 2 + (1 + PowerSeries.X) * S
    - (1 + PowerSeries.X)

section c5
open PowerSeries

/-- `ρ = S²`, `δ = S³` solves ODE₅ when `K(S) = 0` (closed). -/
lemma c5_identity (S : PowerSeries ℚ) (hK : K S = 0) : Φ (S ^ 2) (S ^ 3) = 0 := by
  have hd : tD (K S) = 0 := by rw [hK]; simp [tD]
  have hd' : tD (K S) = (3 * X ^ 2 * S ^ 2 - 4 * X * S + 1 + X) * tD S
      + X * (2 * X * S ^ 3 - 2 * S ^ 2 + S - 1) := by
    simp only [K, tD_sub, tD_add, tD_mul, tD_one]
    rw [show X ^ 2 = X ^ (1 + 1) from rfl, show S ^ 3 = S ^ (2 + 1) from rfl,
      show S ^ 2 = S ^ (1 + 1) from rfl, tD_pow, tD_pow, tD_pow]
    simp only [tD_X, tD_two]
    push_cast; ring
  have hΦ : Φ (S ^ 2) (S ^ 3) = 1 - S ^ 2 - 4 * X * S ^ 3 + tD S * (4 * S - 9 * X * S ^ 2) := by
    simp only [Φ]
    rw [show S ^ 3 = S ^ (2 + 1) from rfl, show S ^ 2 = S ^ (1 + 1) from rfl, tD_pow, tD_pow]
    push_cast; ring
  have hKS : (3 * X ^ 2 * S ^ 2 - 4 * X * S + 1 + X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    simp at this
  refine (mul_eq_zero.mp ?_).resolve_left hKS
  rw [hΦ]
  unfold K at hK
  linear_combination (6 * X * S ^ 2 - S - 1) * hK + (4 * S - 9 * X * S ^ 2) * (hd'.symm.trans hd)

end c5

/-! ## Piece 6: the binomial sum -/

lemma S_const : PowerSeries.constantCoeff S = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, S, PowerSeries.coeff_mk]; simp



end ErsConj13
