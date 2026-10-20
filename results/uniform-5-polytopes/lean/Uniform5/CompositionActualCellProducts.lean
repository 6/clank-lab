import Uniform5.CompositionPolygonCellProducts
import Uniform5.CompositionGraph

/-! Convert selected actual faces and their local orthogonal translations
to the proved cell reconstruction. Connectivity and factor uniformity are
consequences of the actual parent geometry. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- The only geometric transport obligation is equality or an orthogonal
translate along each actual parent edge. -/
def FaceCellTransport {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : Set E) (C : E → Set E) : Prop :=
  ∀ v w, Edge P v w → C w = C v ∨
    ∃ d ∈ CaseB.normals (C v), C w = CaseB.translate (C v) d

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def actualFaceCellSystem {P : Set E} (hP : UnitUniform 5 P)
    (C : E → Set E)
    (hface : ∀ v ∈ P.extremePoints ℝ, IsConvexFace P (C v))
    (hmem : ∀ v ∈ P.extremePoints ℝ, v ∈ C v)
    (htransport : FaceCellTransport P C) : CaseB.CellSystem E where
  vertices := P.extremePoints ℝ
  finite_vertices := finitePolytope_extremePoints_finite (uniform_finitePolytope hP.1)
  cell v := (C v).extremePoints ℝ
  self_mem v hv := by
    rw [face_extremePoints_eq (hface v hv)]
    exact ⟨hmem v hv, hv⟩
  cell_subset v hv := (hface v hv).2.extremePoints_subset_extremePoints
  edge := Edge P
  connected := fun _ hv _ hw => finitePolytope_edge_connected
    (uniform_finitePolytope hP.1) hv hw
  local_transport := by
    intro v w he
    rcases htransport v w he with hc | ⟨d, hd, hc⟩
    · exact Or.inl (congrArg (fun A : Set E => A.extremePoints ℝ) hc)
    · refine Or.inr ⟨d, ?_, ?_⟩
      · intro a ha b hb
        exact hd a ha.1 b hb.1
      · rw [hc]
        change ((AffineIsometryEquiv.vaddConst ℝ d) '' C v).extremePoints ℝ =
          (AffineIsometryEquiv.vaddConst ℝ d) '' (C v).extremePoints ℝ
        exact (affineIsometry_image_extremePoints _ _).symm

/-- Selecting polygon cells gives K3 once their actual edge transports
have been established; the three-dimensional factor is derived. -/
theorem actual_polygon_cells_mem_K3 {P : Set E} (hP : UnitUniform 5 P)
    (C : E → Set E)
    (hface : ∀ v ∈ P.extremePoints ℝ, IsConvexFace P (C v))
    (hmem : ∀ v ∈ P.extremePoints ℝ, v ∈ C v)
    (htransport : FaceCellTransport P C)
    {r : E} (hr : r ∈ P.extremePoints ℝ) (hd : affineDimension (C r) = 2) : K3 P := by
  let D := actualFaceCellSystem hP C hface hmem htransport
  have heq : convexHull ℝ D.vertices = P :=
    (finitePolytope_eq_convexHull_extremePoints (uniform_finitePolytope hP.1)).symm
  have hC : convexHull ℝ (D.cell r) = C r :=
    (finitePolytope_eq_convexHull_extremePoints (finitePolytope_face
      (uniform_finitePolytope hP.1) (hface r hr) ⟨r, hmem r hr⟩)).symm
  rw [← heq]
  apply polygonCellSystem_mem_K3 D hr (heq.symm ▸ hP)
  rw [hC, ← hd]
  exact unitUniform_all_faces hP (hface r hr) ⟨r, hmem r hr⟩

/-- Selecting three-dimensional cells gives K3 with a derived polygon
offset factor. -/
theorem actual_three_cells_mem_K3 {P : Set E} (hP : UnitUniform 5 P)
    (C : E → Set E)
    (hface : ∀ v ∈ P.extremePoints ℝ, IsConvexFace P (C v))
    (hmem : ∀ v ∈ P.extremePoints ℝ, v ∈ C v)
    (htransport : FaceCellTransport P C)
    {r : E} (hr : r ∈ P.extremePoints ℝ) (hd : affineDimension (C r) = 3) : K3 P := by
  let D := actualFaceCellSystem hP C hface hmem htransport
  have heq : convexHull ℝ D.vertices = P :=
    (finitePolytope_eq_convexHull_extremePoints (uniform_finitePolytope hP.1)).symm
  have hC : convexHull ℝ (D.cell r) = C r :=
    (finitePolytope_eq_convexHull_extremePoints (finitePolytope_face
      (uniform_finitePolytope hP.1) (hface r hr) ⟨r, hmem r hr⟩)).symm
  rw [← heq]
  apply cellSystem_mem_K3 D hr (heq.symm ▸ hP)
  rw [hC, ← hd]
  exact unitUniform_all_faces hP (hface r hr) ⟨r, hmem r hr⟩

end Uniform5.Composition
