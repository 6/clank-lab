import Uniform5.CompositionFamilies
import Uniform5.CompositionCongruence
import Uniform5.CompositionSymmetry

/-!
# Classification predicates and uniformity under congruence

The concrete known families depend only on the intrinsic Euclidean hull.
The ambient-symmetry definition of uniformity also respects intrinsic
congruence in a fixed finite-dimensional ambient space, by extending each
intrinsic congruence to an actual ambient affine isometry.
-/

noncomputable section
namespace Uniform5.Composition
open Set

section Metric
variable {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
  {P : Set E} {Q : Set F}

theorem k1_congruent_iff (h : Congruent P Q) : K1 P ↔ K1 Q :=
  ⟨k1_congruent (congruent_symm h), k1_congruent h⟩

theorem k2_congruent_iff (h : Congruent P Q) : K2 P ↔ K2 Q :=
  ⟨k2_congruent (congruent_symm h), k2_congruent h⟩

theorem k3_congruent_iff (h : Congruent P Q) : K3 P ↔ K3 Q :=
  ⟨k3_congruent (congruent_symm h), k3_congruent h⟩

theorem known_congruent_iff (h : Congruent P Q) : Known P ↔ Known Q :=
  ⟨known_congruent (congruent_symm h), known_congruent h⟩
end Metric

section Euclidean
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

@[simp] theorem k1_affineIsometryEquiv_image_iff (g : E ≃ᵃⁱ[ℝ] F) (P : Set E) :
    K1 (g '' P) ↔ K1 P :=
  (k1_congruent_iff (congruent_affineIsometryEquiv_image g P)).symm

@[simp] theorem k2_affineIsometryEquiv_image_iff (g : E ≃ᵃⁱ[ℝ] F) (P : Set E) :
    K2 (g '' P) ↔ K2 P :=
  (k2_congruent_iff (congruent_affineIsometryEquiv_image g P)).symm

@[simp] theorem k3_affineIsometryEquiv_image_iff (g : E ≃ᵃⁱ[ℝ] F) (P : Set E) :
    K3 (g '' P) ↔ K3 P :=
  (k3_congruent_iff (congruent_affineIsometryEquiv_image g P)).symm

@[simp] theorem known_affineIsometryEquiv_image_iff (g : E ≃ᵃⁱ[ℝ] F) (P : Set E) :
    Known (g '' P) ↔ Known P :=
  (known_congruent_iff (congruent_affineIsometryEquiv_image g P)).symm

variable [FiniteDimensional ℝ E] {P Q : Set E}

theorem affineDimension_congruent (h : Congruent P Q) :
    affineDimension P = affineDimension Q := by
  obtain ⟨g, rfl⟩ := (congruent_iff_affineIsometryEquiv_image P Q).mp h
  exact (affineDimension_image g P).symm

theorem finitePolytope_congruent_iff (h : Congruent P Q) :
    FinitePolytope P ↔ FinitePolytope Q := by
  obtain ⟨g, rfl⟩ := (congruent_iff_affineIsometryEquiv_image P Q).mp h
  exact (finitePolytope_image_iff g P).symm

theorem uniform_congruent_iff (h : Congruent P Q) (n : ℕ) :
    Uniform n P ↔ Uniform n Q := by
  obtain ⟨g, rfl⟩ := (congruent_iff_affineIsometryEquiv_image P Q).mp h
  exact (uniform_image_iff g n P).symm

theorem unitEdges_congruent_iff (h : Congruent P Q) : UnitEdges P ↔ UnitEdges Q := by
  obtain ⟨g, rfl⟩ := (congruent_iff_affineIsometryEquiv_image P Q).mp h
  exact (unitEdges_image_iff g P).symm

theorem unitUniform_congruent_iff (h : Congruent P Q) (n : ℕ) :
    UnitUniform n P ↔ UnitUniform n Q := by
  obtain ⟨g, rfl⟩ := (congruent_iff_affineIsometryEquiv_image P Q).mp h
  exact (unitUniform_image_iff g n P).symm
end Euclidean

end Uniform5.Composition
