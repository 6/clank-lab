import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Quotient.Basic

namespace PostLie

attribute [local instance] LieRing.ofAssociativeRing

variable {k s V : Type*} [Field k] [LieRing s] [LieAlgebra k s]
  [AddCommGroup V] [Module k V]

/-- Restriction of a representation to an invariant subspace. -/
def subspaceRepresentation (ρ : s →ₗ⁅k⁆ Module.End k V) (I : Submodule k V)
    (hI : ∀ x v, v ∈ I → ρ x v ∈ I) : s →ₗ⁅k⁆ Module.End k I where
  toFun x :=
    { toFun := fun v => ⟨ρ x v, hI x v v.property⟩
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp
  map_lie' {x y} := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change ρ ⁅x, y⁆ v = ρ x (ρ y v) - ρ y (ρ x v)
    rw [ρ.map_lie]
    rfl

@[simp] lemma subspaceRepresentation_apply
    (ρ : s →ₗ⁅k⁆ Module.End k V) (I : Submodule k V)
    (hI : ∀ x v, v ∈ I → ρ x v ∈ I) (x : s) (v : I) :
    (subspaceRepresentation ρ I hI x v : V) = ρ x v := rfl

/-- Descent of a representation to a quotient by an invariant subspace. -/
def quotientRepresentation (ρ : s →ₗ⁅k⁆ Module.End k V) (J : Submodule k V)
    (hJ : ∀ x v, v ∈ J → ρ x v ∈ J) : s →ₗ⁅k⁆ Module.End k (V ⧸ J) where
  toFun x := J.mapQ J (ρ x) (hJ x)
  map_add' x y := by
    apply LinearMap.ext
    intro w
    refine Quotient.inductionOn' w ?_
    intro v
    change J.mkQ (ρ (x + y) v) = J.mkQ (ρ x v) + J.mkQ (ρ y v)
    rw [map_add, LinearMap.add_apply, map_add]
  map_smul' t x := by
    apply LinearMap.ext
    intro w
    refine Quotient.inductionOn' w ?_
    intro v
    change J.mkQ (ρ (t • x) v) = t • J.mkQ (ρ x v)
    rw [map_smul, LinearMap.smul_apply, map_smul]
  map_lie' {x y} := by
    apply LinearMap.ext
    intro w
    refine Quotient.inductionOn' w ?_
    intro v
    change J.mkQ (ρ ⁅x, y⁆ v) =
      J.mkQ (ρ x (ρ y v)) - J.mkQ (ρ y (ρ x v))
    rw [ρ.map_lie]
    change J.mkQ (ρ x (ρ y v) - ρ y (ρ x v)) = _
    rw [map_sub]

@[simp] lemma quotientRepresentation_apply
    (ρ : s →ₗ⁅k⁆ Module.End k V) (J : Submodule k V)
    (hJ : ∀ x v, v ∈ J → ρ x v ∈ J) (x : s) (v : V) :
    quotientRepresentation ρ J hJ x (J.mkQ v) = J.mkQ (ρ x v) := rfl

end PostLie
