import PostLie.Cocycle

namespace PostLie

attribute [local instance] LieRing.ofAssociativeRing

variable {k g n : Type*} [Field k]
  [LieRing g] [LieAlgebra k g] [LieRing n] [LieAlgebra k n]

/-- Left multiplication transported to a derivation of the second bracket. -/
def leftDerivation {e : g ≃ₗ[k] n} (p : Product e) (x : g) : LieDerivation k n n where
  toLinearMap := e.conj (p.mul x)
  leibniz' y z := by
    change e (p.mul x (e.symm ⁅y, z⁆)) =
      ⁅y, e (p.mul x (e.symm z))⁆ - ⁅z, e (p.mul x (e.symm y))⁆
    have h := congrArg e (p.derivation x (e.symm y) (e.symm z))
    simp only [LinearEquiv.apply_symm_apply, map_add] at h
    rw [← lie_skew (e (p.mul x (e.symm y))) z] at h
    simpa only [sub_eq_add_neg, add_comm] using h

@[simp] lemma leftDerivation_apply {e : g ≃ₗ[k] n} (p : Product e) (x : g) (y : n) :
    leftDerivation p x y = e (p.mul x (e.symm y)) := rfl

/-- The representation by derivations associated to a post-Lie product. -/
def action {e : g ≃ₗ[k] n} (p : Product e) : g →ₗ⁅k⁆ LieDerivation k n n where
  toFun := leftDerivation p
  map_add' x y := by
    ext z
    change e (p.mul (x + y) (e.symm z)) =
      e (p.mul x (e.symm z)) + e (p.mul y (e.symm z))
    simp
  map_smul' t x := by
    ext z
    change e (p.mul (t • x) (e.symm z)) = t • e (p.mul x (e.symm z))
    simp
  map_lie' {x y} := by
    ext z
    change e (p.mul ⁅x, y⁆ (e.symm z)) =
      e (p.mul x (e.symm (e (p.mul y (e.symm z))))) -
      e (p.mul y (e.symm (e (p.mul x (e.symm z)))))
    rw [p.left_lie]
    simp

@[simp] lemma action_apply {e : g ≃ₗ[k] n} (p : Product e) (x : g) (y : n) :
    action p x y = e (p.mul x (e.symm y)) := rfl

/-- The identification of the underlying spaces is the initial nonlinear cocycle. -/
lemma identification_isCocycle {e : g ≃ₗ[k] n} (p : Product e) :
    IsCocycle (action p) e.toLinearMap := by
  intro a b
  change e ⁅a, b⁆ = ⁅e a, e b⁆ + action p a (e b) - action p b (e a)
  apply e.symm.injective
  simp only [map_sub, map_add, action_apply, LinearEquiv.symm_apply_apply]
  have h := p.skew a b
  rw [add_sub_assoc, h]
  abel

/-- Traceless right multiplication gives the trace hypothesis in Lemma A. -/
lemma trace_action_eq_trace_ad [FiniteDimensional k g] [FiniteDimensional k n]
    [LieRing.IsNilpotent n] {e : g ≃ₗ[k] n} (p : Product e)
    (htrace : ∀ x, LinearMap.trace k g (right p x) = 0) (x : g) :
    LinearMap.trace k n (action p x).toLinearMap =
      LinearMap.trace k g (LieAlgebra.ad k g x) := by
  have h := congrArg (LinearMap.trace k g) (adjoint_identity p x)
  rw [map_add, map_sub, trace_transportedAd, htrace, sub_zero, add_zero] at h
  change LinearMap.trace k n (e.conj (left p x)) = _
  rw [LinearMap.trace_conj']
  exact h.symm

end PostLie
