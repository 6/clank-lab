import Uniform5.CompositionWedgeActualHalfspaces

/-! Assemble normalized fan geometry directly from actual vertices and
whole incident facet sections. All parent containment and admissibility
properties are consequences of these incidences. -/
noncomputable section
namespace Uniform5.Composition.Wedge
open Set

/-- A finite chart before its supporting halfspaces are installed. -/
def actualBase {P : Set (Space 5)} (hP : UnitUniform 5 P) (v : Space 5)
    (points ends : Finset (Space 5)) (special : Space 5 → Space 5 → Prop) :
    CaseB.WFanGeometry (Space 5) where
  v := v
  centre := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
  radius := intrinsicRadius P
  vertices := points
  ends := ends
  specialPair := special
  halfspaces := ∅

/-- Install precisely the oriented supports of the literal whole facets. -/
def actualGeometry {P : Set (Space 5)} (hP : UnitUniform 5 P) (v : Space 5)
    (points ends : Finset (Space 5)) (special : Space 5 → Space 5 → Prop)
    (facets : Set (Set (Space 5))) : Geometry :=
  let F := normalize (actualBase hP v points ends special)
  { F with halfspaces := {H | ∃ B ∈ facets, SupportingHalfspace F B H} }

@[simp] theorem actualGeometry_support {P : Set (Space 5)} (hP : UnitUniform 5 P)
    (v : Space 5) (points ends : Finset (Space 5)) (special : Space 5 → Space 5 → Prop)
    (facets : Set (Set (Space 5))) (B H : Set (Space 5)) :
    SupportingHalfspace (actualGeometry hP v points ends special facets) B H ↔
      SupportingHalfspace (normalize (actualBase hP v points ends special)) B H := Iff.rfl

/-- Literal actual incidences discharge every finite geometric realization
condition, before any computed W inequality is used. -/
theorem actualGeometry_realizes {P : Set (Space 5)} (hP : UnitUniform 5 P)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (points ends : Finset (Space 5)) (special : Space 5 → Space 5 → Prop)
    (facets : Set (Set (Space 5))) {n : Parameter} {f : CaseB.WFan}
    (hfinite : finiteParameters n f)
    (hpoints : (points : Set (Space 5)) ⊆
      (vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ)
    (hlarge : ∃ a ∈ points, ∃ b ∈ points, 1 < dist a b)
    (hfacets : ∀ B ∈ facets, ∃ K, Facet P K ∧ v ∈ K ∧
      B = K ∩ vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) :
    Realizes n f (actualGeometry hP v points ends special facets) points facets ends special := by
  let F := actualBase hP v points ends special
  have hR := uniform_intrinsicRadius_pos hP.1
  obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius hP.1
  have hc : dist F.centre F.v = F.radius := by
    change dist _ v = intrinsicRadius P
    rw [dist_comm, dist_eq_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) hR.le).mp (hs v hv)
  have hvertices : (F.vertices : Set (Space 5)) ⊆ P := by
    intro x hx
    exact (hpoints hx).1.1
  have hhalf : 1 < 2 * intrinsicRadius P := by
    obtain ⟨a, ha, b, hb, hab⟩ := hlarge
    have haR := (unitUniform5_vertexFigure_two_spheres hP hv a (hpoints ha)).2
    have hbR := (unitUniform5_vertexFigure_two_spheres hP hv b (hpoints hb)).2
    have ht := dist_triangle a F.centre b
    change dist a F.centre = intrinsicRadius P at haR
    change dist b F.centre = intrinsicRadius P at hbR
    rw [haR, dist_comm F.centre b, hbR] at ht
    linarith
  refine ⟨normalize_normal_unit F hR hc, (one_div_pos.mpr (by positivity)).le,
    (div_lt_one (by positivity)).mpr hhalf, ?_, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · constructor
    · intro he
      have hp : 0 < (actualGeometry hP v points ends special facets).offset :=
        one_div_pos.mpr (by change 0 < 2 * intrinsicRadius P; positivity)
      exact (hp.ne' he).elim
    · intro hi
      exact (hfinite hi).elim
  · intro x hx
    exact (normalize_onFigureSphere F hR hc x).mpr
      (unitUniform5_vertexFigure_two_spheres hP hv x (hpoints hx))
  · intro B hB
    obtain ⟨K, hK, hvK, rfl⟩ := hfacets B hB
    obtain ⟨H, hH, _⟩ := actual_facet_supporting_halfspace hP hK hv hvK F rfl rfl rfl hvertices
    exact ⟨H, hH⟩

/-- Every installed supporting halfspace contains the actual parent. -/
theorem actualGeometry_halfspaces {P : Set (Space 5)} (hP : UnitUniform 5 P)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (points ends : Finset (Space 5)) (special : Space 5 → Space 5 → Prop)
    (facets : Set (Set (Space 5)))
    (hfacets : ∀ B ∈ facets, ∃ K, Facet P K ∧ v ∈ K ∧
      B = K ∩ vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) :
    ∀ H ∈ (actualGeometry hP v points ends special facets).halfspaces, P ⊆ H := by
  rintro H ⟨B, hB, hH⟩
  obtain ⟨K, hK, hvK, rfl⟩ := hfacets B hB
  exact actual_supporting_halfspace_contains hP hK hv hvK
    (actualBase hP v points ends special) rfl rfl rfl hH

/-- Every actual figure vertex is a fan vertex or an admissible point of
this constructed geometry; this is derived, rather than supplied to W. -/
theorem actualGeometry_coverage {P : Set (Space 5)} (hP : UnitUniform 5 P)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (points ends : Finset (Space 5)) (special : Space 5 → Space 5 → Prop)
    (facets : Set (Set (Space 5)))
    (hpoints : (points : Set (Space 5)) ⊆
      (vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ)
    (hfacets : ∀ B ∈ facets, ∃ K, Facet P K ∧ v ∈ K ∧
      B = K ∩ vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) :
    ∀ x ∈ (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ,
      x ∈ points ∨ (actualGeometry hP v points ends special facets).Admissible x := by
  intro x hx
  by_cases hm : x ∈ points
  · exact Or.inl hm
  · right
    have hR := uniform_intrinsicRadius_pos hP.1
    obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius hP.1
    have hc : dist (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) v =
        intrinsicRadius P := by
      rw [dist_comm, dist_eq_norm]
      exact (sq_eq_sq₀ (norm_nonneg _) hR.le).mp (hs v hv)
    refine ⟨?_, ?_, ?_⟩
    · exact (normalize_onFigureSphere (actualBase hP v points ends special) hR hc x).mpr
        (unitUniform5_vertexFigure_two_spheres hP hv x hx)
    · intro H hH
      exact actualGeometry_halfspaces hP hv points ends special facets hfacets H hH hx.1.1
    · intro y hy
      exact (unitUniform5_vertexFigure_vertex_metric hP hv).2 x hx y (hpoints hy)
        (fun he => hm (he.symm ▸ hy))

end Uniform5.Composition.Wedge
