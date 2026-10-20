import Uniform5.CompositionPolarMetrics
import Uniform5.CompositionTransverseFace

/-! Transport of actual polar directions from a transverse subspace. -/
noncomputable section
namespace Uniform5.Composition
open Set InnerProductGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Inclusion of a Euclidean subspace preserves the exact spherical tangent. -/
theorem subspace_sphericalTangent_coe (S : Submodule ℝ E) (w u : S) :
    (sphericalTangent w u : E) = sphericalTangent (w : E) (u : E) := rfl

/-- Subspace and ambient tangent angles coincide, with their actual metrics. -/
theorem subspace_sphericalTangent_angle (S : Submodule ℝ E) (w u v : S) :
    angle (sphericalTangent w u) (sphericalTangent w v) =
      angle (sphericalTangent (w : E) (u : E)) (sphericalTangent (w : E) (v : E)) := by
  exact (S.subtypeₗᵢ.angle_map (sphericalTangent w u) (sphericalTangent w v)).symm

variable [FiniteDimensional ℝ E]

/-- When an actual ray is already normal to the collapsed face, the
quotient projection preserves that ray, rather than changing its angle. -/
theorem transverseProjection_coe_of_mem_orthogonal (G : Set E) (f x : E)
    (hx : x - f ∈ (affineSpan ℝ G).directionᗮ) :
    (transverseProjection G f x : E) = x - f := by
  rw [transverseProjection_apply]
  exact congrArg Subtype.val (Submodule.orthogonalProjection_mem_subspace_eq_self
    (⟨x - f, hx⟩ : (affineSpan ℝ G).directionᗮ))

/-- Normalize in the quotient and then include into the ambient space. -/
theorem transverseProjection_normalized_coe (G : Set E) (f x : E)
    (hx : x - f ∈ (affineSpan ℝ G).directionᗮ) :
    ((‖transverseProjection G f x‖⁻¹ • transverseProjection G f x :
      (affineSpan ℝ G).directionᗮ) : E) = ‖x - f‖⁻¹ • (x - f) := by
  have hc := transverseProjection_coe_of_mem_orthogonal G f x hx
  have hn : ‖transverseProjection G f x‖ = ‖x - f‖ := by
    change ‖(transverseProjection G f x : E)‖ = _
    rw [hc]
  simp only [Submodule.coe_smul, hc, hn]

/-- The exact fan used by closure can be transferred from the quotient
when all three center offsets lie in the transverse space. -/
theorem transverse_normalized_tangent_angle (G : Set E) (f o a b : E)
    (ho : o - f ∈ (affineSpan ℝ G).directionᗮ)
    (ha : a - f ∈ (affineSpan ℝ G).directionᗮ)
    (hb : b - f ∈ (affineSpan ℝ G).directionᗮ) :
    let q := transverseProjection G f
    angle (sphericalTangent (‖q o‖⁻¹ • q o) (‖q a‖⁻¹ • q a))
      (sphericalTangent (‖q o‖⁻¹ • q o) (‖q b‖⁻¹ • q b)) =
    angle (sphericalTangent (‖o - f‖⁻¹ • (o - f)) (‖a - f‖⁻¹ • (a - f)))
      (sphericalTangent (‖o - f‖⁻¹ • (o - f)) (‖b - f‖⁻¹ • (b - f))) := by
  dsimp only
  rw [subspace_sphericalTangent_angle,
    transverseProjection_normalized_coe G f o ho,
    transverseProjection_normalized_coe G f a ha,
    transverseProjection_normalized_coe G f b hb]

end Uniform5.Composition
