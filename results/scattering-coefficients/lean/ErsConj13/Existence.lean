import ErsConj13.Calculus

noncomputable section

namespace ErsConj13

open MvPowerSeries

/-! ## Generic substitution automorphisms of `A` -/

lemma hasSubst_fin2 {a : Fin 2 → A} (h : ∀ i, constantCoeff (a i) = 0) : HasSubst a :=
  hasSubst_of_constantCoeff_zero h

lemma subst_one' {a : Fin 2 → A} (ha : HasSubst a) : subst a (1 : A) = 1 := by
  rw [← substAlgHom_apply (R := ℚ) ha, map_one]

lemma inv_eq_of_mul {x y : A} (h : x * y = 1) : x⁻¹ = y := by
  have hc : constantCoeff x ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  exact (MvPowerSeries.inv_eq_iff_mul_eq_one hc).mpr (by rw [mul_comm, h])

lemma subst_inv' {a : Fin 2 → A} (ha : HasSubst a) {x : A} (hx : constantCoeff x ≠ 0) :
    subst a x⁻¹ = (subst a x)⁻¹ := by
  symm
  apply inv_eq_of_mul
  rw [← subst_mul ha, MvPowerSeries.mul_inv_cancel _ hx, subst_one' ha]

lemma subst_comp_eq_id {a b : Fin 2 → A} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (hab : ∀ i, subst b (a i) = X i) (f : A) :
    subst b (subst a f) = f := by
  rw [subst_comp_subst_apply (hasSubst_fin2 ha) (hasSubst_fin2 hb)]
  have : (fun s => subst b (a s)) = (X : Fin 2 → A) := funext hab
  rw [this, subst_self]; rfl

/-- The substitution automorphism `f ↦ f(a 0, a 1)` of `A`, with inverse `f ↦ f(b 0, b 1)`. -/
def substEquiv (a b : Fin 2 → A) (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0)
    (hab : ∀ i, subst a (b i) = X i) (hba : ∀ i, subst b (a i) = X i) : A ≃+* A where
  toFun := subst a
  invFun := subst b
  left_inv f := subst_comp_eq_id ha hb hba f
  right_inv f := subst_comp_eq_id hb ha hab f
  map_mul' f g := subst_mul (hasSubst_fin2 ha) f g
  map_add' f g := subst_add (hasSubst_fin2 ha) f g

lemma substEquiv_apply (a b : Fin 2 → A) (ha hb hab hba) (f : A) :
    substEquiv a b ha hb hab hba f = subst a f := rfl

/-! ## T -/

def Ta : Fin 2 → A := ![u * (1 + u + w) * (1 + u)⁻¹, w * (1 + u)⁻¹]
def Tb : Fin 2 → A := ![u * (1 + w)⁻¹, w * (1 + u + w) * (1 + w)⁻¹]

lemma Ta_cc : ∀ i, constantCoeff (Ta i) = 0 := by
  simp [Fin.forall_fin_two, Ta]
lemma Tb_cc : ∀ i, constantCoeff (Tb i) = 0 := by
  simp [Fin.forall_fin_two, Tb]

lemma cc1u : constantCoeff (1 + u) ≠ 0 := by simp
lemma cc1w : constantCoeff (1 + w) ≠ 0 := by simp
lemma cc1uw : constantCoeff (1 + u + w) ≠ 0 := by simp

lemma hI : (1 + u) * (1 + u)⁻¹ = 1 := MvPowerSeries.mul_inv_cancel _ cc1u
lemma hJ : (1 + u + w) * (1 + u + w)⁻¹ = 1 := MvPowerSeries.mul_inv_cancel _ cc1uw
lemma hK : (1 + w) * (1 + w)⁻¹ = 1 := MvPowerSeries.mul_inv_cancel _ cc1w

lemma Tab : ∀ i, subst Ta (Tb i) = X i := by
  have ha := hasSubst_fin2 Ta_cc
  have s0 : subst Ta u = u * (1 + u + w) * (1 + u)⁻¹ := subst_X ha 0
  have s1 : subst Ta w = w * (1 + u)⁻¹ := subst_X ha 1
  have i1 : (1 + w * (1 + u)⁻¹)⁻¹ = (1 + u) * (1 + u + w)⁻¹ := inv_eq_of_mul (by
    linear_combination ((1 + u + w)⁻¹ * w) * hI + hJ)
  rw [Fin.forall_fin_two]
  constructor
  · show subst Ta (u * (1 + w)⁻¹) = u
    rw [subst_mul ha, subst_inv' ha cc1w, subst_add ha, subst_one' ha, s0, s1, i1]
    linear_combination ((1 + u + w)⁻¹ * u ^ 2 + (1 + u + w)⁻¹ * u * w + (1 + u + w)⁻¹ * u) * hI
      + u * hJ
  · show subst Ta (w * (1 + u + w) * (1 + w)⁻¹) = w
    rw [subst_mul ha, subst_mul ha, subst_inv' ha cc1w]
    simp only [subst_add ha, subst_one' ha, s0, s1]
    rw [i1]
    linear_combination ((1 + u)⁻¹*(1 + u + w)⁻¹*u^2*w + (1 + u)⁻¹*(1 + u + w)⁻¹*u*w^2
      + (1 + u)⁻¹*(1 + u + w)⁻¹*u*w + (1 + u)⁻¹*(1 + u + w)⁻¹*w^2 + (1 + u + w)⁻¹*u*w
      + (1 + u + w)⁻¹*w^2 + (1 + u + w)⁻¹*w)*hI + (w)*hJ

lemma Tba : ∀ i, subst Tb (Ta i) = X i := by
  have hb := hasSubst_fin2 Tb_cc
  have s0 : subst Tb u = u * (1 + w)⁻¹ := subst_X hb 0
  have s1 : subst Tb w = w * (1 + u + w) * (1 + w)⁻¹ := subst_X hb 1
  have i2 : (1 + u * (1 + w)⁻¹)⁻¹ = (1 + w) * (1 + u + w)⁻¹ := inv_eq_of_mul (by
    linear_combination ((1 + w)⁻¹ * w + (1 + w)⁻¹) * hJ + (-(1 + u + w)⁻¹ * w - (1 + u + w)⁻¹ + 1) * hK)
  rw [Fin.forall_fin_two]
  constructor
  · show subst Tb (u * (1 + u + w) * (1 + u)⁻¹) = u
    rw [subst_mul hb, subst_mul hb, subst_inv' hb cc1u]
    simp only [subst_add hb, subst_one' hb, s0, s1]
    rw [i2]
    linear_combination ((1 + w)⁻¹^2*u*w^2 + 2*(1 + w)⁻¹^2*u*w + (1 + w)⁻¹^2*u - (1 + w)⁻¹^2*w^2
      - 2*(1 + w)⁻¹^2*w - (1 + w)⁻¹^2 + (1 + w)⁻¹*w + (1 + w)⁻¹)*hJ
      + ((1 + u + w)⁻¹*(1 + w)⁻¹*w^2 + 2*(1 + u + w)⁻¹*(1 + w)⁻¹*w + (1 + u + w)⁻¹*(1 + w)⁻¹
      + (1 + w)⁻¹*u*w + (1 + w)⁻¹*u - (1 + w)⁻¹*w - (1 + w)⁻¹ + u)*hK
  · show subst Tb (w * (1 + u)⁻¹) = w
    rw [subst_mul hb, subst_inv' hb cc1u]
    simp only [subst_add hb, subst_one' hb, s0, s1]
    rw [i2]
    linear_combination ((1 + w)⁻¹*w^2 + (1 + w)⁻¹*w)*hJ + (w)*hK

/-- `T(u) = u(1+u+w)/(1+u)`, `T(w) = w/(1+u)`; inverse `u ↦ u/(1+w)`, `w ↦ w(1+u+w)/(1+w)`. -/
def Tmap : A ≃+* A := substEquiv Ta Tb Ta_cc Tb_cc Tab Tba

lemma Tmap_u : Tmap u * (1 + u) = u * (1 + u + w) := by
  show subst Ta (X 0) * (1 + u) = _
  rw [subst_X (hasSubst_fin2 Ta_cc)]
  show u * (1 + u + w) * (1 + u)⁻¹ * (1 + u) = _
  linear_combination (u * (1 + u + w)) * hI

lemma Tmap_w : Tmap w * (1 + u) = w := by
  show subst Ta (X 1) * (1 + u) = _
  rw [subst_X (hasSubst_fin2 Ta_cc)]
  show w * (1 + u)⁻¹ * (1 + u) = _
  linear_combination w * hI

theorem exists_T : ∃ T : A ≃+* A, T u * (1 + u) = u * (1 + u + w) ∧ T w * (1 + u) = w :=
  ⟨Tmap, Tmap_u, Tmap_w⟩

/-! ## θ -/

lemma pow_uw (d : ℕ) : (u * w) ^ d = diag (PowerSeries.X ^ d) := by
  induction d with
  | zero => simp [diag_one]
  | succ n ih => rw [pow_succ, ih, pow_succ, diag_mul, diag_X]

lemma hasSubst_uw : PowerSeries.HasSubst (u * w : A) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (by simp)

lemma diag_eq_subst (G : PowerSeries ℚ) : diag G = PowerSeries.subst (u * w : A) G := by
  ext e
  rw [PowerSeries.coeff_subst hasSubst_uw, coeff_diag]
  simp_rw [pow_uw, coeff_diag, PowerSeries.coeff_X_pow]
  rw [finsum_eq_single _ (e 0)]
  · split_ifs <;> simp_all
  · intro d hd
    split_ifs with h1 h2 <;> simp_all [eq_comm]

lemma subst_diag {b : Fin 2 → A} (hb : HasSubst b) (h : subst b (u * w) = u * w)
    (G : PowerSeries ℚ) : subst b (diag G) = diag G := by
  rw [diag_eq_subst, PowerSeries.subst_def, subst_comp_subst_apply hasSubst_uw.const hb]
  simp only [h]

/-- Substitution vector `u ↦ u·diag G`, `w ↦ w·diag H`. -/
def thVec (G H : PowerSeries ℚ) : Fin 2 → A := ![u * diag G, w * diag H]

lemma thVec_cc (G H : PowerSeries ℚ) : ∀ i, constantCoeff (thVec G H i) = 0 := by
  simp [Fin.forall_fin_two, thVec]

lemma thVec_inv {G H : PowerSeries ℚ} (hGH : diag G * diag H = 1) :
    ∀ i, subst (thVec G H) (thVec H G i) = X i := by
  have ha := hasSubst_fin2 (thVec_cc G H)
  have s0 : subst (thVec G H) u = u * diag G := subst_X ha 0
  have s1 : subst (thVec G H) w = w * diag H := subst_X ha 1
  have huw : subst (thVec G H) (u * w) = u * w := by
    rw [subst_mul ha, s0, s1]; linear_combination (u * w) * hGH
  rw [Fin.forall_fin_two]
  constructor
  · show subst (thVec G H) (u * diag H) = u
    rw [subst_mul ha, s0, subst_diag ha huw]; linear_combination u * hGH
  · show subst (thVec G H) (w * diag G) = w
    rw [subst_mul ha, s1, subst_diag ha huw]; linear_combination w * hGH

lemma diag_mul_diag_inv (F : PowerSeries ℚ) (hF : PowerSeries.constantCoeff F = 1) :
    diag F * diag F⁻¹ = 1 := by
  rw [← diag_mul, PowerSeries.mul_inv_cancel _ (by rw [hF]; exact one_ne_zero), diag_one]

/-- The diagonal wall `θ_F`: `u ↦ u F(uw)`, `w ↦ w F(uw)⁻¹`; inverse `θ_{F⁻¹}`. -/
def thetaMap (F : PowerSeries ℚ) (hF : PowerSeries.constantCoeff F = 1) : A ≃+* A :=
  substEquiv (thVec F F⁻¹) (thVec F⁻¹ F) (thVec_cc _ _) (thVec_cc _ _)
    (thVec_inv (diag_mul_diag_inv F hF))
    (thVec_inv (by rw [mul_comm]; exact diag_mul_diag_inv F hF))

lemma thetaMap_u (F : PowerSeries ℚ) (hF : PowerSeries.constantCoeff F = 1) :
    thetaMap F hF u = u * diag F :=
  subst_X (hasSubst_fin2 (thVec_cc F F⁻¹)) 0

lemma thetaMap_w (F : PowerSeries ℚ) (hF : PowerSeries.constantCoeff F = 1) :
    thetaMap F hF w * diag F = w := by
  show subst (thVec F F⁻¹) (X 1) * diag F = w
  rw [subst_X (hasSubst_fin2 (thVec_cc F F⁻¹)) 1]
  show w * diag F⁻¹ * diag F = w
  linear_combination w * diag_mul_diag_inv F hF

theorem exists_theta (F : PowerSeries ℚ) (hF : PowerSeries.constantCoeff F = 1) :
    ∃ θ : A ≃+* A, θ u = u * diag F ∧ θ w * diag F = w :=
  ⟨thetaMap F hF, thetaMap_u F hF, thetaMap_w F hF⟩

end ErsConj13
