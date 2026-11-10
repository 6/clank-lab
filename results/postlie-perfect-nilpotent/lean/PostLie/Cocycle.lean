import PostLie.Basic
import Mathlib.Algebra.Lie.Derivation.Basic

namespace PostLie

attribute [local instance] LieRing.ofAssociativeRing

variable {k g n : Type*} [Field k]
  [LieRing g] [LieAlgebra k g] [LieRing n] [LieAlgebra k n]

/-- The nonlinear cocycle identity for an action by derivations. -/
def IsCocycle (L : g →ₗ⁅k⁆ LieDerivation k n n) (P : g →ₗ[k] n) : Prop :=
  ∀ a b, P ⁅a, b⁆ = ⁅P a, P b⁆ + L a (P b) - L b (P a)

/-- The error in the nonlinear cocycle identity. -/
def defect (L : g →ₗ⁅k⁆ LieDerivation k n n) (P : g →ₗ[k] n) (a b : g) : n :=
  P ⁅a, b⁆ - ⁅P a, P b⁆ - L a (P b) + L b (P a)

/-- Infinitesimal translation in the direction `z`. -/
def velocity (L : g →ₗ⁅k⁆ LieDerivation k n n) (P : g →ₗ[k] n) (z : n) :
    g →ₗ[k] n :=
  -(LieAlgebra.ad k n z).comp P +
    ((LieDerivation.toLinearMapLieHom k n).comp L).toLinearMap.flip z

@[simp] lemma velocity_apply (L : g →ₗ⁅k⁆ LieDerivation k n n)
    (P : g →ₗ[k] n) (z : n) (a : g) :
    velocity L P z a = -⁅z, P a⁆ + L a z := rfl

/-- The infinitesimal cocycle error evolves by `E' = -ad(z) E`. -/
lemma defect_variation (L : g →ₗ⁅k⁆ LieDerivation k n n)
    (P : g →ₗ[k] n) (z : n) (a b : g) :
    velocity L P z ⁅a, b⁆ - ⁅velocity L P z a, P b⁆ - ⁅P a, velocity L P z b⁆ -
        L a (velocity L P z b) + L b (velocity L P z a) =
      -⁅z, defect L P a b⁆ := by
  have hrep : L ⁅a, b⁆ z = L a (L b z) - L b (L a z) := by
    rw [L.map_lie]
    rfl
  simp only [velocity_apply, defect, lie_add, add_lie, lie_neg, neg_lie,
    lie_sub, map_add, map_neg, hrep, (L a).apply_lie_eq_add,
    (L b).apply_lie_eq_add]
  rw [leibniz_lie z (P a) (P b), ← lie_skew (L b z) (P a)]
  abel

/-- Invertible cocycles transport the adjoint identity to the target space. -/
lemma cocycle_adjoint_identity (L : g →ₗ⁅k⁆ LieDerivation k n n)
    (P : g ≃ₗ[k] n) (hP : IsCocycle L P.toLinearMap) (a : g) :
    P.conj (LieAlgebra.ad k g a) =
      LieAlgebra.ad k n (P a) + (L a).toLinearMap -
        (((LieDerivation.toLinearMapLieHom k n).comp L).toLinearMap.flip (P a)).comp
          P.symm.toLinearMap := by
  ext w
  change P ⁅a, P.symm w⁆ = ⁅P a, w⁆ + L a w - L (P.symm w) (P a)
  have h := hP a (P.symm w)
  change P ⁅a, P.symm w⁆ =
    ⁅P a, P (P.symm w)⁆ + L a (P (P.symm w)) - L (P.symm w) (P a) at h
  simpa only [LinearEquiv.apply_symm_apply] using h

/-- The trace identity used in the determinant argument, in the invertible case. -/
lemma trace_velocity_of_cocycle [FiniteDimensional k g] [FiniteDimensional k n]
    [LieRing.IsNilpotent n] (L : g →ₗ⁅k⁆ LieDerivation k n n)
    (P : g ≃ₗ[k] n) (hP : IsCocycle L P.toLinearMap)
    (htrace : ∀ a, LinearMap.trace k n (L a).toLinearMap =
      LinearMap.trace k g (LieAlgebra.ad k g a)) (z : n) :
    LinearMap.trace k n ((velocity L P.toLinearMap z).comp P.symm.toLinearMap) = 0 := by
  have hid := congrArg (LinearMap.trace k n) (cocycle_adjoint_identity L P hP (P.symm z))
  simp only [LinearMap.trace_conj', map_sub, map_add, trace_ad_nilpotent,
    htrace, LinearEquiv.apply_symm_apply, zero_add] at hid
  have hrho : LinearMap.trace k n
      ((((LieDerivation.toLinearMapLieHom k n).comp L).toLinearMap.flip z).comp
        P.symm.toLinearMap) = 0 := by
    exact (sub_eq_self.mp hid.symm)
  have hv : (velocity L P.toLinearMap z).comp P.symm.toLinearMap =
      -LieAlgebra.ad k n z +
      (((LieDerivation.toLinearMapLieHom k n).comp L).toLinearMap.flip z).comp
        P.symm.toLinearMap := by
    ext w
    simp [velocity_apply]
    rfl
  rw [hv, map_add, map_neg, trace_ad_nilpotent, hrho, neg_zero, add_zero]

end PostLie
