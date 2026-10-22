import ErsConj13.KSTransport

/-!
# The pentagon, `θ_{(1,0),(1+x)⁵} = X⁵`, and `ι ∘ T = X Z ∘ ι`
-/

noncomputable section

namespace ErsConj13.Scat

open MvPowerSeries

/-- The constant family `1 + t`. -/
def famOne : Slope → PowerSeries ℚ := fun _ => 1 + PowerSeries.X

lemma famOne_cc (s : Slope) : PowerSeries.constantCoeff (famOne s) = 1 := by simp [famOne]

lemma rayEval_one_add_X' (s : Slope) : rayEval s (1 + PowerSeries.X) = 1 + rayMono s := by
  rw [rayEval, ← map_one (PowerSeries.C (R := ℚ)), PowerSeries.subst_add (hasSubst_rayMono s),
    PowerSeries.subst_C, PowerSeries.subst_X (hasSubst_rayMono s)]
  simp

lemma rayMono_zero' : rayMono ((0 : ℚ≥0) : Slope) = X 0 := by rw [rayMono, ray_zero']; simp [X_def]
lemma rayMono_top' : rayMono (⊤ : Slope) = X 1 := by rw [rayMono, ray_top']; simp [X_def]
lemma rayMono_one' : rayMono ((1 : ℚ≥0) : Slope) = X 0 * X 1 := by
  rw [rayMono, ray_one, monomial_eq_XX]; simp

@[simp] lemma ray_one'' : ray (1 : Slope) = (1, 1) := by rw [← WithTop.coe_one, ray_one]
@[simp] lemma rayMono_zero'' : rayMono (0 : Slope) = X 0 := by
  rw [← WithTop.coe_zero, rayMono_zero']
@[simp] lemma rayMono_one'' : rayMono (1 : Slope) = X 0 * X 1 := by
  rw [← WithTop.coe_one, rayMono_one']

lemma wvX : wv ((0 : ℚ≥0) : Slope) (1 + PowerSeries.X) = ![X 0, X 1 * (1 + X 0)⁻¹] := by
  funext i; fin_cases i <;> simp [wv, ray_zero', rayEval_one_add_X', rayMono_zero']
lemma wvY : wv (⊤ : Slope) (1 + PowerSeries.X) = ![X 0 * (1 + X 1), X 1] := by
  funext i; fin_cases i <;> simp [wv, ray_top', rayEval_one_add_X', rayMono_top']
lemma wvZ : wv ((1 : ℚ≥0) : Slope) (1 + PowerSeries.X) =
    ![X 0 * (1 + X 0 * X 1), X 1 * (1 + X 0 * X 1)⁻¹] := by
  funext i; fin_cases i <;> simp [wv, ray_one, rayEval_one_add_X', rayMono_one']

lemma ccu {a : B} (ha : Ord 1 a) : constantCoeff (1 + a) ≠ 0 := by
  rw [map_add, map_one, ord_one_iff.mp ha]; norm_num

lemma subvec_of {a : Fin 2 → B} (h0 : Ord 1 (a 0)) (h1 : Ord 1 (a 1)) : SubVec a := by
  intro i; fin_cases i; exact h0; exact h1

/-- The pentagon `Y ∘ X = X ∘ Z ∘ Y`. -/
lemma pentagon (h : B) :
    wall ⊤ (1 + PowerSeries.X) (wall ((0 : ℚ≥0) : Slope) (1 + PowerSeries.X) h) =
      wall ((0 : ℚ≥0) : Slope) (1 + PowerSeries.X)
        (wall ((1 : ℚ≥0) : Slope) (1 + PowerSeries.X) (wall ⊤ (1 + PowerSeries.X) h)) := by
  have sX := subVec_wv ((0 : ℚ≥0) : Slope) (1 + PowerSeries.X)
  have sY := subVec_wv (⊤ : Slope) (1 + PowerSeries.X)
  have sZ := subVec_wv ((1 : ℚ≥0) : Slope) (1 + PowerSeries.X)
  simp only [wall_eq]
  rw [subst_comp_subst_apply sX.hasSubst sY.hasSubst,
    subst_comp_subst_apply sY.hasSubst sZ.hasSubst,
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun i =>
      ord_one_iff.mp ((sY i).subst sZ)) sX.hasSubst]
  congr 1
  rw [wvX, wvY, wvZ] at *
  set vx : Fin 2 → B := ![X 0, X 1 * (1 + X 0)⁻¹] with hvx
  set vy : Fin 2 → B := ![X 0 * (1 + X 1), X 1] with hvy
  set vz : Fin 2 → B := ![X 0 * (1 + X 0 * X 1), X 1 * (1 + X 0 * X 1)⁻¹] with hvz
  have hx : Ord 1 (X 0 : B) := ord_X 0
  have hy : Ord 1 (X 1 : B) := ord_X 1
  have hxy : Ord 1 (X 0 * X 1 : B) := hx.mul_right _
  have hS1 : ∀ (a : Fin 2 → B), SubVec a → subst a (1 : B) = 1 := fun a ha => by
    simpa using subst_C' a 1
  set I := (1 + X 0 : B)⁻¹ with hIdef
  have hI : (1 + X 0 : B) * I = 1 := MvPowerSeries.mul_inv_cancel _ (ccu hx)
  have hxI : Ord 1 (X 0 * (X 1 * I) : B) := hx.mul_right _
  set J := (1 + X 0 * (X 1 * I) : B)⁻¹ with hJdef
  have hJ : (1 + X 0 * (X 1 * I) : B) * J = 1 := MvPowerSeries.mul_inv_cancel _ (ccu hxI)
  have hx1 : Ord 1 (X 0 * (1 + X 1) : B) := hx.mul_right _
  set K := (1 + X 0 * (1 + X 1) : B)⁻¹ with hKdef
  have hK : (1 + X 0 * (1 + X 1) : B) * K = 1 := MvPowerSeries.mul_inv_cancel _ (ccu hx1)
  have vx0 : subst vx (X 0 : B) = X 0 := subst_X' _ sX 0
  have vx1 : subst vx (X 1 : B) = X 1 * I := subst_X' _ sX 1
  have vy0 : subst vy (X 0 : B) = X 0 * (1 + X 1) := subst_X' _ sY 0
  have vy1 : subst vy (X 1 : B) = X 1 := subst_X' _ sY 1
  have vz0 : subst vz (X 0 : B) = X 0 * (1 + X 0 * X 1) := subst_X' _ sZ 0
  have vz1 : subst vz (X 1 : B) = X 1 * (1 + X 0 * X 1)⁻¹ := subst_X' _ sZ 1
  have vxInv : subst vx ((1 + X 0 * X 1 : B)⁻¹) = J := by
    rw [subst_inv' sX.hasSubst (ccu hxy), subst_add sX.hasSubst, subst_mul sX.hasSubst, hS1 _ sX,
      vx0, vx1]
  have vyInv : subst vy ((1 + X 0 : B)⁻¹) = K := by
    rw [subst_inv' sY.hasSubst (ccu hx), subst_add sY.hasSubst, hS1 _ sY, vy0]
  funext i
  fin_cases i
  · show subst vy (vx 0) = subst vx (subst vz (vy 0))
    simp only [hvx, hvy, Matrix.cons_val_zero]
    rw [← hvx, ← hvy, vy0, subst_mul sZ.hasSubst, subst_add sZ.hasSubst, hS1 _ sZ, vz0, vz1,
      subst_mul sX.hasSubst, subst_add sX.hasSubst, subst_mul sX.hasSubst, hS1 _ sX,
      subst_mul sX.hasSubst, subst_add sX.hasSubst, subst_mul sX.hasSubst, hS1 _ sX, vx0, vx1,
      vxInv]
    linear_combination (-(X 0 * X 1 * I)) * hJ - (X 0 * X 1) * hI
  · show subst vy (vx 1) = subst vx (subst vz (vy 1))
    simp only [hvx, hvy, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [← hvx, ← hvy, subst_mul sY.hasSubst, vy1, vyInv, vz1, subst_mul sX.hasSubst, vx1, vxInv]
    have : K = I * J := by
      rw [hKdef]; apply inv_eq_of_mul
      linear_combination (J) * hI + hJ
    rw [this]; ring


lemma rayEval_mul (s : Slope) (F G : PowerSeries ℚ) :
    rayEval s (F * G) = rayEval s F * rayEval s G := by
  rw [rayEval, rayEval, rayEval, PowerSeries.subst_mul (hasSubst_rayMono s)]

/-- A substitution fixing `x` fixes every series in `x` alone. -/
lemma subst_rayEval_zero {a : Fin 2 → B} (ha : SubVec a) (h0 : a 0 = X 0) (G : PowerSeries ℚ) :
    subst a (rayEval ((0 : ℚ≥0) : Slope) G) = rayEval ((0 : ℚ≥0) : Slope) G := by
  rw [rayEval, PowerSeries.subst_def, subst_comp_subst_apply
    (hasSubst_rayMono _).const ha.hasSubst, rayMono_zero', subst_X' _ ha, h0]

/-- Walls on the ray `(1,0)` compose multiplicatively. -/
lemma wall_zero_mul {F G : PowerSeries ℚ} (hF : PowerSeries.constantCoeff F = 1)
    (hG : PowerSeries.constantCoeff G = 1) (h : B) :
    wall ((0 : ℚ≥0) : Slope) (F * G) h =
      wall ((0 : ℚ≥0) : Slope) F (wall ((0 : ℚ≥0) : Slope) G h) := by
  have sF := subVec_wv ((0 : ℚ≥0) : Slope) F
  have sG := subVec_wv ((0 : ℚ≥0) : Slope) G
  simp only [wall_eq]
  rw [subst_comp_subst_apply sG.hasSubst sF.hasSubst]
  congr 1
  have hF0 : wv ((0 : ℚ≥0) : Slope) F 0 = X 0 := by simp [wv, ray_zero']
  have hFc := (ord_rayEval_sub_one ((0 : ℚ≥0) : Slope) hF).mono (rlen_pos _)
  have hGc := (ord_rayEval_sub_one ((0 : ℚ≥0) : Slope) hG).mono (rlen_pos _)
  have ccG : constantCoeff (rayEval ((0 : ℚ≥0) : Slope) G) ≠ 0 := by
    have := ord_one_iff.mp hGc; rw [map_sub, map_one, sub_eq_zero] at this; rw [this]; norm_num
  funext i; fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [show wv ((0 : ℚ≥0) : Slope) G 0 = X 0 by simp [wv, ray_zero'], subst_X' _ sF, hF0]
    simp [wv, ray_zero']
  · simp only [Fin.mk_one, Fin.isValue]
    have e1 : ∀ K : PowerSeries ℚ, wv ((0 : ℚ≥0) : Slope) K 1 =
        X 1 * (rayEval ((0 : ℚ≥0) : Slope) K)⁻¹ := fun K => by simp [wv, ray_zero']
    rw [e1 G, e1 (F * G), subst_mul sF.hasSubst, subst_X' _ sF, subst_inv' sF.hasSubst ccG,
      subst_rayEval_zero sF hF0, rayEval_mul, inv_mul_of_cc hFc hGc, e1 F]
    ring

lemma wall_zero_pow (n : ℕ) (h : B) :
    wall ((0 : ℚ≥0) : Slope) ((1 + PowerSeries.X) ^ n) h =
      (wall ((0 : ℚ≥0) : Slope) (1 + PowerSeries.X))^[n] h := by
  induction n generalizing h with
  | zero => simp only [pow_zero, Function.iterate_zero, id]; exact wall_one _ h
  | succ n ih =>
    rw [pow_succ', wall_zero_mul (by simp) (by simp), ih, Function.iterate_succ_apply']

/-- The list `0, 1, 0, 1, …` (five times): `(X Z)⁵`. -/
def Lpent : List Slope :=
  [(0 : ℚ≥0), (1 : ℚ≥0), (0 : ℚ≥0), (1 : ℚ≥0), (0 : ℚ≥0), (1 : ℚ≥0), (0 : ℚ≥0), (1 : ℚ≥0),
    (0 : ℚ≥0), (1 : ℚ≥0)]

lemma prodL_Lpent (h : B) : prodL famOne Lpent h =
    (fun g => wall ((0 : ℚ≥0) : Slope) (1 + PowerSeries.X)
      (wall ((1 : ℚ≥0) : Slope) (1 + PowerSeries.X) g))^[5] h := by
  simp only [Lpent, prodL_cons, prodL_nil, famOne, Function.iterate_succ, Function.comp_apply,
    Function.iterate_zero, id]

/-- `Y ∘ X⁵ = (X Z)⁵ ∘ Y`. -/
lemma Y_X5 (h : B) :
    wall ⊤ (1 + PowerSeries.X) (wall ((0 : ℚ≥0) : Slope) ((1 + PowerSeries.X) ^ 5) h) =
      prodL famOne Lpent (wall ⊤ (1 + PowerSeries.X) h) := by
  rw [wall_zero_pow, prodL_Lpent]
  have key : ∀ n (g : B), wall ⊤ (1 + PowerSeries.X)
      ((wall ((0 : ℚ≥0) : Slope) (1 + PowerSeries.X))^[n] g) =
      (fun g => wall ((0 : ℚ≥0) : Slope) (1 + PowerSeries.X)
        (wall ((1 : ℚ≥0) : Slope) (1 + PowerSeries.X) g))^[n] (wall ⊤ (1 + PowerSeries.X) g) := by
    intro n
    induction n with
    | zero => intro g; rfl
    | succ n ih =>
      intro g
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', pentagon, ih]
  exact key 5 h

end ErsConj13.Scat
