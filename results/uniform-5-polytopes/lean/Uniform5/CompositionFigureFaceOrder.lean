import Uniform5.CompositionFigureRidgeCorrespondence

/-! Inclusion and equality of actual faces are reflected by the vertex
section at an arbitrary apex. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem finitePolytope_vertexFigure_section_subset_iff {P F G : Set E}
    (hP : FinitePolytope P) {v : E} (hv : v ∈ P.extremePoints ℝ)
    (c : E) (R : ℝ) (hs : ∀ x ∈ P.extremePoints ℝ, ‖x - c‖ ^ 2 = R ^ 2)
    (hu : UnitEdges P) (hF : IsConvexFace P F) (hG : IsConvexFace P G)
    (hvF : v ∈ F) (hvG : v ∈ G) :
    F ∩ vertexFigure P v c ⊆ G ∩ vertexFigure P v c ↔ F ⊆ G := by
  constructor
  · intro hh
    let g := AffineIsometryEquiv.constVAdd ℝ E (-v)
    have hg (x : E) : g x = x - v := by simp [g, sub_eq_add_neg, add_comm]
    have hgv : g v = 0 := by rw [hg, sub_self]
    have hz : (0 : E) ∈ (g '' P).extremePoints ℝ := by
      rw [← affineIsometry_image_extremePoints, ← hgv]
      exact mem_image_of_mem g hv
    have hp := finitePolytope_image g hP
    let V := vertices (g '' P) hp
    have hzero : 0 ∈ V := (mem_vertices hp 0).mpr hz
    have hs' : ∀ x ∈ (g '' P).extremePoints ℝ, ‖x - g c‖ ^ 2 = R ^ 2 := by
      rw [← affineIsometry_image_extremePoints]
      rintro x ⟨y, hy, rfl⟩
      have he : g y - g c = y - c := by rw [hg, hg]; abel
      rw [he]
      exact hs y hy
    have hu' := unitEdges_image g hu
    have hheight := (cosphericalUnit_simpleVertex_heights V hzero (g c) R
      (fun x hx => hs' x ((mem_vertices hp x).mp hx))
      (fun x y hxy => hu' x y ((edge_iff_vertices_isEdge hp x y).mpr hxy))).1
    have hHull : convexHull ℝ (V : Set E) = g '' P := convexHull_vertices hp
    have hQ : heightSection (convexHull ℝ (V : Set E)) (sphereHeight (g c)) =
        g '' vertexFigure P v c := by
      rw [vertexFigure_image, hgv]
      simp only [heightSection, vertexFigure, hHull, sub_zero]
    have hsub : g '' F ⊆ g '' G := apexFace_subset_of_section_subset V _ hheight
      (hHull.symm ▸ isConvexFace_image g hF) (hHull.symm ▸ isConvexFace_image g hG)
      (hgv ▸ mem_image_of_mem g hvF) (hgv ▸ mem_image_of_mem g hvG) (by
        rw [hQ, ← Set.image_inter g.injective, ← Set.image_inter g.injective]
        exact Set.image_mono hh)
    intro x hx
    obtain ⟨y, hy, he⟩ := hsub (mem_image_of_mem g hx)
    exact g.injective he ▸ hy
  · exact fun hh x hx => ⟨hh hx.1, hx.2⟩

theorem unitUniform_vertexFigure_section_subset_iff {n : ℕ} {P F G : Set E}
    (hP : UnitUniform (n + 3) P) {v : E} (hv : v ∈ P.extremePoints ℝ)
    (hF : IsConvexFace P F) (hG : IsConvexFace P G) (hvF : v ∈ F) (hvG : v ∈ G) :
    let c := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
    F ∩ vertexFigure P v c ⊆ G ∩ vertexFigure P v c ↔ F ⊆ G := by
  obtain ⟨R, _, hs⟩ := finitePolytope_transitive_cospherical
    (uniform_finitePolytope hP.1) (uniform_vertexTransitive hP.1)
  exact finitePolytope_vertexFigure_section_subset_iff
    (uniform_finitePolytope hP.1) hv _ R hs hP.2 hF hG hvF hvG

end Uniform5.Composition
