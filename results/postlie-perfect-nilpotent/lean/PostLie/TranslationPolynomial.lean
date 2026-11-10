import PostLie.Translation
import PostLie.PolynomialFlow
import PostLie.Determinant

namespace PostLie

open LieAlgebra Polynomial

variable {k g n I J : Type*} [Field k] [CharZero k]
  [LieRing g] [LieAlgebra k g] [LieRing n] [LieAlgebra k n]
  [LieRing.IsNilpotent n]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

local instance rationalModuleFlow (L : g →ₗ⁅k⁆ LieDerivation k n n) :
    Module ℚ (SemiDirectSum n g L) := Module.compHom _ (Rat.castHom k)

omit [CharZero k] [LieRing.IsNilpotent n] in
lemma translationDerivation_smul (L : g →ₗ⁅k⁆ LieDerivation k n n)
    (t : k) (z : n) :
    (translationDerivation L (t • z)).toLinearMap =
      t • (translationDerivation L z).toLinearMap := by
  apply LinearMap.ext
  intro h
  ext
  · simp [smul_add]
    rw [← lie_skew z h.left, smul_neg, neg_neg]
  · simp

/-- A polynomial matrix for the first component of a translated graph. -/
noncomputable def translationMatrix
    (L : g →ₗ⁅k⁆ LieDerivation k n n) (e : g ≃ₗ[k] n)
    (P : g →ₗ[k] n) (hP : IsCocycle L P) (z : n)
    (b : Module.Basis I k n) (c : Module.Basis J k (SemiDirectSum n g L))
    (r : ℕ) : Matrix I I k[X] :=
  matrixFlow (LinearMap.toMatrix c b (SemiDirectSum.projl L))
    (LinearMap.toMatrix c c (translationDerivation L z).toLinearMap)
    (LinearMap.toMatrix b c ((graph L P hP).toLinearMap.comp e.symm.toLinearMap)) r

lemma eval_translationMatrix
    (L : g →ₗ⁅k⁆ LieDerivation k n n) (e : g ≃ₗ[k] n)
    (P : g →ₗ[k] n) (hP : IsCocycle L P) (z : n)
    (b : Module.Basis I k n) (c : Module.Basis J k (SemiDirectSum n g L))
    (r : ℕ) (hr : (translationDerivation L z).toLinearMap ^ r = 0) (t : k) :
    Matrix.toLin b b ((translationMatrix L e P hP z b c r).map (evalRingHom t)) =
      (translated L P hP (t • z)).comp e.symm.toLinearMap := by
  have hA : (LinearMap.toMatrix c c (translationDerivation L z).toLinearMap) ^ r = 0 := by
    rw [LinearMap.toMatrix_pow, hr, map_zero]
  rw [translationMatrix, eval_matrixFlow, Matrix.toLin_mul b c b,
    Matrix.toLin_mul c c b, toLin_eval_expMatrix c _ r hA t]
  simp only [Matrix.toLin_toMatrix]
  change (SemiDirectSum.projl L).comp
    ((IsNilpotent.exp (t • (translationDerivation L z).toLinearMap)).comp
      ((graph L P hP).toLinearMap.comp e.symm.toLinearMap)) = _
  rw [← translationDerivation_smul]
  rfl

/-- The polynomial first component satisfies the translation differential equation. -/
lemma eval_derivative_translationMatrix
    (L : g →ₗ⁅k⁆ LieDerivation k n n) (e : g ≃ₗ[k] n)
    (P : g →ₗ[k] n) (hP : IsCocycle L P) (z : n)
    (b : Module.Basis I k n) (c : Module.Basis J k (SemiDirectSum n g L))
    (r : ℕ) (hr : (translationDerivation L z).toLinearMap ^ (r + 1) = 0) (t : k) :
    (Matrix.toLin b b (((translationMatrix L e P hP z b c (r + 1)).map derivative).map
      (evalRingHom t))).comp e.toLinearMap =
      velocity L (translated L P hP (t • z)) z := by
  have hA : (LinearMap.toMatrix c c (translationDerivation L z).toLinearMap) ^
      (r + 1) = 0 := by rw [LinearMap.toMatrix_pow, hr, map_zero]
  rw [translationMatrix, eval_derivative_matrixFlow _ _ _ r hA t,
    Matrix.toLin_mul b c b, Matrix.toLin_mul c c b, Matrix.toLin_mul c c b,
    toLin_eval_expMatrix c _ (r + 1) hA t]
  simp only [Matrix.toLin_toMatrix]
  rw [← translationDerivation_smul]
  apply LinearMap.ext
  intro a
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  change (translationDerivation L z (translation L (t • z) (graph L P hP a))).left = _
  rw [translationDerivation_apply]
  simp only [translation_right, velocity_apply]
  rfl

variable [FiniteDimensional k g] [FiniteDimensional k n]

/-- The determinant of the polynomial translation family is constant. -/
theorem det_translationMatrix_constant
    (L : g →ₗ⁅k⁆ LieDerivation k n n) (e : g ≃ₗ[k] n)
    (P : g →ₗ[k] n) (hP : IsCocycle L P) (z : n)
    (b : Module.Basis I k n) (c : Module.Basis J k (SemiDirectSum n g L))
    (r : ℕ) (hr : (translationDerivation L z).toLinearMap ^ (r + 1) = 0)
    (htrace : ∀ a, LinearMap.trace k n (L a).toLinearMap =
      LinearMap.trace k g (LieAlgebra.ad k g a)) :
    (translationMatrix L e P hP z b c (r + 1)).det =
      C ((translationMatrix L e P hP z b c (r + 1)).det.eval 0) := by
  apply det_constant_of_cocycle_flow L e b _ z _ _ htrace
  · intro t
    rw [eval_translationMatrix L e P hP z b c (r + 1) hr t]
    simpa only [LinearMap.comp_assoc, LinearEquiv.symm_comp,
      LinearMap.comp_id] using translated_isCocycle L P hP (t • z)
  · intro t
    rw [eval_derivative_translationMatrix L e P hP z b c r hr t,
      eval_translationMatrix L e P hP z b c (r + 1) hr t]
    simp only [LinearMap.comp_assoc, LinearEquiv.symm_comp, LinearMap.comp_id]

/-- A finite translation preserves the determinant of the first component. -/
theorem det_translated
    (L : g →ₗ⁅k⁆ LieDerivation k n n) (e : g ≃ₗ[k] n)
    (P : g →ₗ[k] n) (hP : IsCocycle L P) (z : n)
    (b : Module.Basis I k n) (c : Module.Basis J k (SemiDirectSum n g L))
    (htrace : ∀ a, LinearMap.trace k n (L a).toLinearMap =
      LinearMap.trace k g (LieAlgebra.ad k g a)) :
    (LinearMap.toMatrix b b ((translated L P hP z).comp e.symm.toLinearMap)).det =
      (LinearMap.toMatrix b b (P.comp e.symm.toLinearMap)).det := by
  obtain ⟨r, hr⟩ := translationDerivation_nilpotent L z
  have hr' : (translationDerivation L z).toLinearMap ^ (r + 1) = 0 := by
    rw [pow_succ, hr, zero_mul]
  let M := translationMatrix L e P hP z b c (r + 1)
  have hconst := det_translationMatrix_constant L e P hP z b c r hr' htrace
  have h0 : M.map (evalRingHom 0) = LinearMap.toMatrix b b (P.comp e.symm.toLinearMap) := by
    rw [show M = translationMatrix L e P hP z b c (r + 1) from rfl,
      translationMatrix, eval_matrixFlow, eval_zero_expMatrix, Matrix.mul_one,
      ← LinearMap.toMatrix_comp b c b]
    congr 1
  have h1 : M.map (evalRingHom 1) =
      LinearMap.toMatrix b b ((translated L P hP z).comp e.symm.toLinearMap) := by
    apply (Matrix.toLin b b).injective
    rw [eval_translationMatrix L e P hP z b c (r + 1) hr' 1]
    simp
  have hh := congrArg (Polynomial.eval 1) hconst
  change M.det.eval 1 = (C (M.det.eval 0)).eval 1 at hh
  rw [eval_C] at hh
  have heval (t : k) : M.det.eval t = (M.map (evalRingHom t)).det :=
    (evalRingHom t).map_det M
  rw [heval 1, heval 0, h1, h0] at hh
  exact hh

/-- Under the trace hypothesis every translation of an invertible cocycle stays invertible. -/
theorem translated_bijective
    (L : g →ₗ⁅k⁆ LieDerivation k n n) (P : g ≃ₗ[k] n)
    (hP : IsCocycle L P.toLinearMap) (z : n)
    (htrace : ∀ a, LinearMap.trace k n (L a).toLinearMap =
      LinearMap.trace k g (LieAlgebra.ad k g a)) :
    Function.Bijective (translated L P.toLinearMap hP z) := by
  classical
  let : FiniteDimensional k (SemiDirectSum n g L) :=
    FiniteDimensional.of_injective (SemiDirectSum.toProdl L).toLinearMap
      (SemiDirectSum.toProdl L).injective
  let b := Module.finBasis k n
  let c := Module.finBasis k (SemiDirectSum n g L)
  let F := (translated L P.toLinearMap hP z).comp P.symm.toLinearMap
  have hd : (LinearMap.toMatrix b b F).det = 1 := by
    simpa only [LinearEquiv.comp_symm, LinearMap.toMatrix_id, Matrix.det_one] using
      det_translated L P P.toLinearMap hP z b c htrace
  let Q := Matrix.toLinearEquiv b (LinearMap.toMatrix b b F)
    (isUnit_iff_ne_zero.mpr (hd ▸ one_ne_zero))
  have hQ : Q.toLinearMap = F := by
    change Matrix.toLin b b (LinearMap.toMatrix b b F) = F
    simp
  have hQP : (P.trans Q).toLinearMap = translated L P.toLinearMap hP z := by
    change Q.toLinearMap.comp P.toLinearMap = _
    rw [hQ]
    ext a
    simp [F]
  simpa only [← hQP, LinearEquiv.coe_coe] using (P.trans Q).bijective

end PostLie
