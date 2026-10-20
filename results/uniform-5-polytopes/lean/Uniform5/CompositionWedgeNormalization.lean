import Uniform5.CompositionWedgeInput
import Uniform5.CompositionActualWedgeCover

/-! The finite two-sphere formulation and the normalized compact chart
have exactly the same admissible points for an actual positive radius. -/
noncomputable section
namespace Uniform5.Composition.Wedge
open Set
open scoped RealInnerProductSpace

/-- Normalize a finite fan's centre without changing its geometric sets. -/
def normalize (F : CaseB.WFanGeometry (Space 5)) : Geometry where
  root := F.v
  normal := (1 / F.radius) • (F.centre - F.v)
  offset := 1 / (2 * F.radius)
  vertices := F.vertices
  ends := F.ends
  halfspaces := F.halfspaces
  specialPair := F.specialPair

/-- Equality to the second sphere is precisely the normalized affine
hyperplane equation on the unit sphere about the root. -/
theorem two_spheres_normalized {p v c : Space 5} {R : ℝ}
    (hR : 0 < R) (hc : dist c v = R) (hp : dist p v = 1) :
    dist p c = R ↔ ⟪p - v, (1 / R) • (c - v)⟫ = 1 / (2 * R) := by
  have hsq : dist p c ^ 2 = 1 + R ^ 2 - 2 * ⟪p - v, c - v⟫ := by
    rw [dist_eq_norm, show p - c = (p - v) - (c - v) by abel, norm_sub_sq_real]
    rw [← dist_eq_norm, ← dist_eq_norm, hp, hc]
    ring
  rw [real_inner_smul_right]
  constructor
  · intro he
    rw [he] at hsq
    have hi : ⟪p - v, c - v⟫ = 1 / 2 := by linarith
    rw [hi]
    ring
  · intro hi
    have hi' : ⟪p - v, c - v⟫ = 1 / 2 := by
      apply mul_left_cancel₀ (one_div_ne_zero hR.ne')
      calc
        (1 / R) * ⟪p - v, c - v⟫ = 1 / (2 * R) := hi
        _ = (1 / R) * (1 / 2) := by ring
    apply (sq_eq_sq₀ dist_nonneg hR.le).mp
    rw [hsq, hi']
    ring

theorem normalize_normal_unit (F : CaseB.WFanGeometry (Space 5))
    (hR : 0 < F.radius) (hc : dist F.centre F.v = F.radius) :
    ‖(normalize F).normal‖ = 1 := by
  change ‖(1 / F.radius) • (F.centre - F.v)‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hR),
    ← dist_eq_norm, hc]
  exact one_div_mul_cancel hR.ne'

theorem normalize_onFigureSphere (F : CaseB.WFanGeometry (Space 5))
    (hR : 0 < F.radius) (hc : dist F.centre F.v = F.radius) (p : Space 5) :
    (normalize F).OnFigureSphere p ↔ dist p F.v = 1 ∧ dist p F.centre = F.radius := by
  constructor
  · rintro ⟨hp, hs⟩
    exact ⟨hp, (two_spheres_normalized hR hc hp).mpr hs⟩
  · rintro ⟨hp, hs⟩
    exact ⟨hp, (two_spheres_normalized hR hc hp).mp hs⟩

theorem normalize_admissible (F : CaseB.WFanGeometry (Space 5))
    (hR : 0 < F.radius) (hc : dist F.centre F.v = F.radius) (p : Space 5) :
    (normalize F).Admissible p ↔ F.Admissible p := by
  rw [Geometry.Admissible, normalize_onFigureSphere F hR hc]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩,
    fun h => ⟨⟨h.1, h.2.1⟩, h.2.2.1, h.2.2.2⟩⟩

@[simp] theorem normalize_allowed (F : CaseB.WFanGeometry (Space 5)) (p : Space 5) :
    (normalize F).Allowed p ↔ F.Allowed p := Iff.rfl

/-- The proved actual-polytope coverage applies unchanged to the normalized
sphere used by the exact semantic W input. -/
theorem actual_fan_or_admissible {P : Set (Space 5)}
    (hP : UnitUniform 5 P) {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (F : CaseB.WFanGeometry (Space 5))
    (hvF : F.v = v)
    (hcF : F.centre = vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
    (hRF : F.radius = intrinsicRadius P)
    (hvertices : (F.vertices : Set (Space 5)) ⊆
      (vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ)
    (hhalfspaces : ∀ H ∈ F.halfspaces,
      vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) ⊆ H) :
    ∀ x ∈ (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ,
      x ∈ (normalize F).vertices ∨ (normalize F).Admissible x := by
  have hR : 0 < F.radius := hRF.symm ▸ uniform_intrinsicRadius_pos hP.1
  have hcent : dist F.centre F.v = F.radius := by
    rw [hvF, hcF, hRF, dist_comm]
    obtain ⟨R, hRp, hs⟩ := unitUniform5_centroid_sphere hP
    have heq : R = intrinsicRadius P := HasIntrinsicRadius.eq_intrinsicRadius
      ⟨uniform_finitePolytope hP.1, hRp.le, fun x hx => by rw [← dist_eq_norm, hs x hx]⟩
    rw [← heq]
    exact hs v hv
  intro x hx
  rcases unitUniform5_vertexFigure_fan_or_admissible hP hv F hvF hcF hRF
    hvertices hhalfspaces x hx with hm | ha
  · exact Or.inl hm
  · exact Or.inr ((normalize_admissible F hR hcent x).mpr ha)

end Uniform5.Composition.Wedge
