import PostLie.Definitions

namespace PostLie

attribute [local instance] LieRing.ofAssociativeRing

variable {k g n : Type*} [Field k]
  [LieRing g] [LieAlgebra k g] [LieRing n] [LieAlgebra k n]

/-- The left multiplications form a representation. -/
def left {e : g ≃ₗ[k] n} (p : Product e) : g →ₗ⁅k⁆ Module.End k g where
  toLinearMap := p.mul
  map_lie' := by
    intro x y
    ext z
    exact p.left_lie x y z

/-- Any scalar-valued linear map vanishing on brackets vanishes on a perfect algebra. -/
lemma linear_eq_zero_of_perfect
    (hperfect : ⁅(⊤ : LieIdeal k g), (⊤ : LieIdeal k g)⁆ = ⊤)
    (f : g →ₗ[k] k) (hf : ∀ (x y : g), f ⁅x, y⁆ = 0) (x : g) : f x = 0 := by
  have hspan : (⊤ : Submodule k g) =
      Submodule.span k {⁅x, y⁆ | (x : g) (y : g)} := by
    rw [← LieAlgebra.coe_derivedSeries_one_eq]
    change (⊤ : Submodule k g) =
      (⁅(⊤ : LieIdeal k g), (⊤ : LieIdeal k g)⁆ : LieIdeal k g).toSubmodule
    rw [hperfect]
    rfl
  have hle : (⊤ : Submodule k g) ≤ LinearMap.ker f := by
    rw [hspan, Submodule.span_le]
    rintro _ ⟨a, b, rfl⟩
    exact hf a b
  exact hle (Submodule.mem_top : x ∈ (⊤ : Submodule k g))

/-- Representations of perfect Lie algebras are traceless. -/
lemma trace_representation_of_perfect
    {M : Type*} [AddCommGroup M] [Module k M]
    (hperfect : ⁅(⊤ : LieIdeal k g), (⊤ : LieIdeal k g)⁆ = ⊤)
    (f : g →ₗ⁅k⁆ Module.End k M) (x : g) : LinearMap.trace k M (f x) = 0 := by
  apply linear_eq_zero_of_perfect hperfect ((LinearMap.trace k M).comp f.toLinearMap)
  intro a b
  change LinearMap.trace k M (f ⁅a, b⁆) = 0
  rw [f.map_lie, LinearMap.trace_lie]

/-- Nilpotency of the second bracket implies that every adjoint is traceless. -/
lemma trace_ad_nilpotent [LieRing.IsNilpotent n] (x : n) :
    LinearMap.trace k n (LieAlgebra.ad k n x) = 0 := by
  obtain ⟨r, hr⟩ := LieAlgebra.nilpotent_ad_of_nilpotent_algebra k n
  exact (LinearMap.isNilpotent_trace_of_isNilpotent ⟨r, hr x⟩).eq_zero

/-- The adjoint of the second bracket, transported to the first space. -/
def transportedAd (e : g ≃ₗ[k] n) (x : g) : Module.End k g :=
  e.symm.toLinearMap ∘ₗ LieAlgebra.ad k n (e x) ∘ₗ e.toLinearMap

lemma adjoint_identity {e : g ≃ₗ[k] n} (p : Product e) (x : g) :
    LieAlgebra.ad k g x = left p x - right p x + transportedAd e x := by
  ext y
  change ⁅x, y⁆ = p.mul x y - p.mul y x + e.symm ⁅e x, e y⁆
  have h := p.skew x y
  rw [h]
  exact (sub_add_cancel _ _).symm

lemma trace_transportedAd [FiniteDimensional k g] [FiniteDimensional k n]
    [LieRing.IsNilpotent n] (e : g ≃ₗ[k] n) (x : g) :
    LinearMap.trace k g (transportedAd e x) = 0 := by
  change LinearMap.trace k g (e.symm.conj (LieAlgebra.ad k n (e x))) = 0
  rw [LinearMap.trace_conj']
  exact trace_ad_nilpotent (e x)

/-- Perfectness supplies the trace hypothesis of the stronger theorem. -/
lemma trace_right_of_perfect [FiniteDimensional k g] [FiniteDimensional k n]
    [LieRing.IsNilpotent n] {e : g ≃ₗ[k] n} (p : Product e)
    (hperfect : ⁅(⊤ : LieIdeal k g), (⊤ : LieIdeal k g)⁆ = ⊤) (x : g) :
    LinearMap.trace k g (right p x) = 0 := by
  have h := congrArg (LinearMap.trace k g) (adjoint_identity p x)
  rw [map_add, map_sub, trace_transportedAd,
    trace_representation_of_perfect hperfect (LieAlgebra.ad k g),
    trace_representation_of_perfect hperfect (left p)] at h
  simpa using h.symm

end PostLie
