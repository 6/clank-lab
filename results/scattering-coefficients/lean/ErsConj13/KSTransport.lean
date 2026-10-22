import ErsConj13.KSExist

/-!
# Transport along `ι : u ↦ x, w ↦ xy` (exponents `(p,q) ↦ (p+q, q)`)
-/

noncomputable section

namespace ErsConj13.Scat

open MvPowerSeries

/-! ## Slope order via rays -/

lemma ray_fst_eq_zero_iff (s : Slope) : (ray s).1 = 0 ↔ s = ⊤ := by
  induction s using WithTop.recTopCoe with
  | top => simp [ray]
  | coe q => simp only [ray, WithTop.recTopCoe_coe, WithTop.coe_ne_top, iff_false]; exact q.den_ne_zero

lemma slope_le_iff (s t : Slope) : s ≤ t ↔ (ray s).2 * (ray t).1 ≤ (ray t).2 * (ray s).1 := by
  induction s using WithTop.recTopCoe with
  | top =>
    rw [ray_top']
    simp only [top_le_iff, one_mul, mul_zero, Nat.le_zero, ray_fst_eq_zero_iff]
  | coe q =>
    induction t using WithTop.recTopCoe with
    | top => simp [ray]
    | coe q' =>
      simp only [ray, WithTop.recTopCoe_coe, WithTop.coe_le_coe]
      rw [← NNRat.coe_le_coe, ← q.num_div_den, ← q'.num_div_den]
      simp only [NNRat.num_div_den]
      rw [← Rat.num_div_den (q : ℚ), ← Rat.num_div_den (q' : ℚ)]
      rw [div_le_div_iff₀ (by exact_mod_cast (q : ℚ).den_pos) (by exact_mod_cast (q' : ℚ).den_pos)]
      rw [NNRat.num_coe, NNRat.num_coe, NNRat.den_coe, NNRat.den_coe]
      exact_mod_cast Iff.rfl

/-- The B-slope of the image ray `(p+q, q)` of the A-ray of slope `σ`. -/
def Lup (σ : Slope) : Slope := slopeOf ((ray σ).1 + (ray σ).2) (ray σ).2

lemma ray_Lup (σ : Slope) : ray (Lup σ) = ((ray σ).1 + (ray σ).2, (ray σ).2) := by
  apply ray_slopeOf
  rw [Nat.coprime_add_self_left]; exact ray_coprime σ

lemma Lup_mono {σ τ : Slope} (h : σ ≤ τ) : Lup σ ≤ Lup τ := by
  rw [slope_le_iff, ray_Lup, ray_Lup]
  rw [slope_le_iff] at h
  simp only; nlinarith

lemma ray_one : ray ((1 : ℚ≥0) : Slope) = (1, 1) := by rw [ray_coe']; simp

lemma Lup_le_one (σ : Slope) : Lup σ ≤ ((1 : ℚ≥0) : Slope) := by
  rw [slope_le_iff, ray_Lup, ray_one]; simp

lemma le_one_iff (τ : Slope) : τ ≤ ((1 : ℚ≥0) : Slope) ↔ (ray τ).2 ≤ (ray τ).1 := by
  rw [slope_le_iff, ray_one]; simp

/-- The inverse on cone slopes: `(P, Q) ↦ (P − Q, Q)`. -/
def Ldown (τ : Slope) : Slope := slopeOf ((ray τ).1 - (ray τ).2) (ray τ).2

lemma Ldown_Lup (σ : Slope) : Ldown (Lup σ) = σ := by
  rw [Ldown, ray_Lup]; simp only [Nat.add_sub_cancel]; exact slopeOf_ray σ

lemma ray_Ldown {τ : Slope} (h : τ ≤ ((1 : ℚ≥0) : Slope)) :
    ray (Ldown τ) = ((ray τ).1 - (ray τ).2, (ray τ).2) := by
  apply ray_slopeOf
  rw [le_one_iff] at h
  have := ray_coprime τ
  rw [← Nat.coprime_add_self_left, Nat.sub_add_cancel h]; exact this

lemma Lup_Ldown {τ : Slope} (h : τ ≤ ((1 : ℚ≥0) : Slope)) : Lup (Ldown τ) = τ := by
  rw [Lup, ray_Ldown h]
  rw [le_one_iff] at h
  simp only [Nat.sub_add_cancel h]; exact slopeOf_ray τ

/-! ## The substitution `ι` -/

/-- `u ↦ x`, `w ↦ x y`. -/
def ιv : Fin 2 → B := ![X 0, X 0 * X 1]

lemma subVec_ιv : SubVec ιv := by
  intro i; fin_cases i
  · exact ord_X 0
  · exact (ord_X 0).mul_right _

/-- `ι : A → B`. -/
def ι (h : B) : B := subst ιv h

lemma monomial_eq_XX (e : Fin 2 →₀ ℕ) (c : ℚ) :
    (monomial e c : B) = C c * X 0 ^ (e 0) * X 1 ^ (e 1) := monomial_eq_θ e c

lemma ι_rayMono (σ : Slope) : ι (rayMono σ) = rayMono (Lup σ) := by
  rw [ι, rayMono_eq, subst_monomial' _ subVec_ιv, rayMono_eq, monomial_eq_XX]
  simp only [ιv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, rvec,
    Finsupp.add_apply, Finsupp.single_eq_same, ray_Lup]
  simp
  ring

lemma ι_rayEval (σ : Slope) (f : PowerSeries ℚ) : ι (rayEval σ f) = rayEval (Lup σ) f := by
  rw [ι, rayEval, rayEval, PowerSeries.subst_def, PowerSeries.subst_def,
    subst_comp_subst_apply (hasSubst_rayMono σ).const subVec_ιv.hasSubst]
  congr 1
  funext _
  exact ι_rayMono σ


lemma inv_mul_of_cc {G H : B} (hG : Ord 1 (G - 1)) (hH : Ord 1 (H - 1)) :
    (G * H)⁻¹ = G⁻¹ * H⁻¹ := by
  apply inv_eq_of_mul
  have h1 := mul_inv_of_cc hG
  have h2 := mul_inv_of_cc hH
  linear_combination (H * H⁻¹) * h1 + h2

/-- `ι` intertwines walls: `ι ∘ θ_{σ,f} = θ_{Lup σ, f} ∘ ι`. -/
lemma ι_wall (σ : Slope) {f : PowerSeries ℚ} (hf : PowerSeries.constantCoeff f = 1) (h : B) :
    ι (wall σ f h) = wall (Lup σ) f (ι h) := by
  rw [ι, ι, wall_eq, wall_eq, subst_comp_subst_apply (subVec_wv σ f).hasSubst subVec_ιv.hasSubst,
    subst_comp_subst_apply subVec_ιv.hasSubst (subVec_wv (Lup σ) f).hasSubst]
  congr 1
  funext i
  have hFB := (ord_rayEval_sub_one (Lup σ) hf).mono (rlen_pos _)
  have hι : ∀ g : B, subst ιv g = ι g := fun _ => rfl
  have hG := ord_pow_sub_one hFB (ray σ).1
  have hH := ord_pow_sub_one hFB (ray σ).2
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [show ιv 0 = X 0 from rfl, subst_X' _ (subVec_wv _ f)]
    simp only [wv, Matrix.cons_val_zero]
    rw [subst_mul subVec_ιv.hasSubst, subst_pow subVec_ιv.hasSubst, subst_X' _ subVec_ιv, hι,
      ι_rayEval, ray_Lup]
    rfl
  · simp only [Fin.mk_one, Fin.isValue]
    rw [show ιv 1 = X 0 * X 1 from rfl, subst_mul (subVec_wv _ f).hasSubst,
      subst_X' _ (subVec_wv _ f), subst_X' _ (subVec_wv _ f)]
    simp only [wv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have hcc : constantCoeff (rayEval σ f ^ (ray σ).1) ≠ 0 := by
      have := ord_one_iff.mp (ord_pow_sub_one ((ord_rayEval_sub_one σ hf).mono (rlen_pos _)) (ray σ).1)
      rw [map_sub, map_one, sub_eq_zero] at this; rw [this]; norm_num
    rw [subst_mul subVec_ιv.hasSubst, subst_X' _ subVec_ιv, subst_inv' subVec_ιv.hasSubst hcc,
      subst_pow subVec_ιv.hasSubst, hι, ι_rayEval, ray_Lup]
    simp only [ιv, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [pow_add, inv_mul_of_cc hG hH]
    have h2 := mul_inv_of_cc hH
    linear_combination (-(X 0 * X 1 * (rayEval (Lup σ) f ^ (ray σ).1)⁻¹)) * h2

/-- Transport of ordered products. -/
lemma ι_prodL (φ ψ : Slope → PowerSeries ℚ) (hφ : ∀ s, PowerSeries.constantCoeff (φ s) = 1)
    (L : List Slope) (hψ : ∀ σ ∈ L, ψ (Lup σ) = φ σ) (h : B) :
    ι (prodL φ L h) = prodL ψ (L.map Lup) (ι h) := by
  induction L with
  | nil => rw [prodL_nil, List.map_nil, prodL_nil]
  | cons σ L ih =>
    rw [prodL_cons, List.map_cons, prodL_cons, ι_wall σ (hφ σ), hψ σ List.mem_cons_self,
      ih (fun τ hτ => hψ τ (List.mem_cons_of_mem _ hτ))]

end ErsConj13.Scat
