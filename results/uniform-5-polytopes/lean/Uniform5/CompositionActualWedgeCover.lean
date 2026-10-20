import Uniform5.CompositionFigureNormalization
import Uniform5.CaseBWedge

/-! The metric and admissibility part of applying W to an actual polytope.
Only the literal chart placement and its supporting halfspaces need to be
identified by the fan construction; sphere, separation, and coverage are
proved from the actual parent. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- Every actual figure vertex lies on both spheres used by W. -/
theorem unitUniform5_vertexFigure_two_spheres {P : Set (Space 5)}
    (hP : UnitUniform 5 P) {v : Space 5} (hv : v ∈ P.extremePoints ℝ) :
    let c := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
    ∀ x ∈ (vertexFigure P v c).extremePoints ℝ,
      dist x v = 1 ∧ dist x c = intrinsicRadius P := by
  dsimp only
  obtain ⟨R, hR, hs⟩ := unitUniform5_centroid_sphere hP
  have heq : R = intrinsicRadius P := HasIntrinsicRadius.eq_intrinsicRadius
    ⟨uniform_finitePolytope hP.1, hR.le, fun x hx => by rw [← dist_eq_norm, hs x hx]⟩
  subst R
  have hs2 : ∀ x ∈ P.extremePoints ℝ,
      ‖x - vertexCentroid (vertices P (uniform_finitePolytope hP.1))‖ ^ 2 =
        intrinsicRadius P ^ 2 := by
    intro x hx
    rw [← dist_eq_norm, hs x hx]
  intro x hx
  have hm := (unitUniform5_vertexFigure_vertex_metric hP hv).1 x hx
  rw [finitePolytope_unit_vertexFigure_extremePoints
    (uniform_finitePolytope hP.1) hv _ _ hs2 hP.2] at hx
  exact ⟨hm, hs x hx.2.1⟩

/-- The dichotomy fan vertex/admissible point follows from actual convex
containment and separation. It is not an additional W coverage input. -/
theorem unitUniform5_vertexFigure_fan_or_admissible {P : Set (Space 5)}
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
      x ∈ F.vertices ∨ F.Admissible x := by
  intro x hx
  by_cases hxf : x ∈ F.vertices
  · exact Or.inl hxf
  · right
    obtain ⟨hs1, hsR⟩ := unitUniform5_vertexFigure_two_spheres hP hv x hx
    refine ⟨hvF.symm ▸ hs1, ?_, fun H hH => hhalfspaces H hH hx.1, ?_⟩
    · rwa [hcF, hRF]
    · intro y hy
      exact (unitUniform5_vertexFigure_vertex_metric hP hv).2 x hx y (hvertices hy)
        (fun he => hxf (he.symm ▸ hy))

/-- Apply W to genuine figure edges. All metric premises and the
fan/admissible dichotomy are discharged here. The remaining premises are
literal properties of the chosen fan chart and its crossing diagonals. -/
theorem unitUniform5_wedge_only_protected_edges
    (p1 : CaseB.P1)
    (chart : CaseB.PolygonParameter → CaseB.WFan → CaseB.WFanGeometry (Space 5))
    (hW : CaseB.W p1 chart) {n : CaseB.PolygonParameter} {f : CaseB.WFan}
    (hn : CaseB.LargeParameter n) (hf : CaseB.WListed p1 n f)
    {P : Set (Space 5)} (hP : UnitUniform 5 P) {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (hvF : (chart n f).v = v)
    (hcF : (chart n f).centre = vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
    (hRF : (chart n f).radius = intrinsicRadius P)
    (hvertices : ((chart n f).vertices : Set (Space 5)) ⊆
      (vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ)
    (hhalfspaces : ∀ H ∈ (chart n f).halfspaces,
      vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) ⊆ H)
    (protectedEdge diagonal : Space 5 → Space 5 → Prop)
    (hprotected_symm : ∀ {x y}, protectedEdge x y → protectedEdge y x)
    (hends : ∀ x ∈ (chart n f).ends,
      ∃ y ∈ (vertexFigure P v
        (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ,
        protectedEdge x y ∧ CaseB.chord 17 ≤ dist x y)
    (hspecial : ∀ x y, (chart n f).specialPair x y → protectedEdge x y ∨ diagonal x y)
    (hcross : ∀ x y, diagonal x y →
      ∃ a ∈ (vertexFigure P v
        (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ,
      ∃ b ∈ (vertexFigure P v
        (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ,
      ∃ t, a ≠ x ∧ a ≠ y ∧ t ∈ segment ℝ x y ∧ t ∈ openSegment ℝ a b)
    {x y : Space 5}
    (he : Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y)
    (hlong : CaseB.chord 17 ≤ dist x y) : protectedEdge x y := by
  let Q := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
  obtain ⟨g, Q₄, him, _, _, hQ₄, _⟩ := unitUniform5_vertexFigure_centered_model hP hv
  have hQ : FinitePolytope Q := by
    rw [show Q = g '' Q₄ from him.symm]
    exact finitePolytope_affineMap_image g.toAffineMap hQ₄
  have hmetric := unitUniform5_vertexFigure_vertex_metric hP hv
  apply CaseB.wedge_only_protected_edges p1 chart hW hn hf
    (V := vertices Q hQ) (o := v) (r := 1)
    (fun z hz => hmetric.1 z ((mem_vertices hQ z).mp hz)) (by norm_num)
    (fun z hz w hw hzw => hmetric.2 z ((mem_vertices hQ z).mp hz)
      w ((mem_vertices hQ w).mp hw) hzw)
    protectedEdge diagonal hprotected_symm
  · intro z hz
    obtain ⟨w, hw, hp, hl⟩ := hends z hz
    exact ⟨w, (mem_vertices hQ w).mpr hw, hp, hl⟩
  · intro z hz
    exact unitUniform5_vertexFigure_fan_or_admissible hP hv (chart n f)
      hvF hcF hRF hvertices hhalfspaces z ((mem_vertices hQ z).mp hz)
  · exact hspecial
  · intro z w hzw
    obtain ⟨a, ha, b, hb, t, hax, hay, ht, ht'⟩ := hcross z w hzw
    exact ⟨a, (mem_vertices hQ a).mpr ha, b, (mem_vertices hQ b).mpr hb,
      t, hax, hay, ht, ht'⟩
  · exact (edge_iff_vertices_isEdge hQ x y).mp he
  · exact hlong

end Uniform5.Composition
