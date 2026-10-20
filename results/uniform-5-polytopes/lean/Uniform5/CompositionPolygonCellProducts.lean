import Uniform5.CompositionProductDimensions
import Uniform5.CompositionProductPolygonFaces

/-! The polygon-cell form of the product reconstruction has a
three-dimensional offset factor; uniformity follows from an actual face. -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem unitUniform_two_finitePolytope {C : Set E} (hC : UnitUniform 2 C) :
    FinitePolytope C := by
  obtain ⟨n, hn, f, rfl⟩ := unitUniform_two_unitPolygon hC
  exact (finitePolytope_affineIsometry_image_iff f _).mpr (unitPolygon_finitePolytope hn)

theorem unitUniform_two_dimension {C : Set E} (hC : UnitUniform 2 C) :
    affineDimension C = 2 := by
  obtain ⟨n, hn, f, rfl⟩ := unitUniform_two_unitPolygon hC
  rw [affineDimension_affineIsometry_image]
  exact (unitPolygon_self_polygonFace hn).2.1

theorem orthogonal_polygon_offset_dimension
    {C X : Set E} (hP : UnitUniform 5 (C + X)) (hC : UnitUniform 2 C)
    (hV : FinitePolytope X) (hX : X ⊆ CaseB.normals C) : affineDimension X = 3 := by
  have h := affineDimension_orthogonal_sum
    (finitePolytope_nonempty (unitUniform_two_finitePolytope hC)) (finitePolytope_nonempty hV) hX
  rw [uniform_dimension hP.1, unitUniform_two_dimension hC] at h
  omega

theorem orthogonal_polygon_sum_mem_K3
    {C X : Set E} (hP : UnitUniform 5 (C + X)) (hC : UnitUniform 2 C)
    (hV : FinitePolytope X) (hX : X ⊆ CaseB.normals C) : K3 (C + X) :=
  orthogonal_sum_mem_K3 hX hC (unitUniform_orthogonal_factor (n := 2) hP
    (unitUniform_two_finitePolytope hC) hV hX (orthogonal_polygon_offset_dimension hP hC hV hX))

theorem polygonCellSystem_mem_K3 (D : CaseB.CellSystem E)
    {r : E} (hr : r ∈ D.vertices)
    (hP : UnitUniform 5 (convexHull ℝ D.vertices))
    (hC : UnitUniform 2 (convexHull ℝ (D.cell r))) :
    K3 (convexHull ℝ D.vertices) := by
  classical
  have hV : FinitePolytope (convexHull ℝ (D.offsets hr)) :=
    ⟨(D.offsets_finite hr).toFinset,
      (D.offsets_finite hr).toFinset_nonempty.mpr (D.offsets_nonempty hr),
      by rw [Set.Finite.coe_toFinset]⟩
  rw [D.convexHull_eq_cell_add_offsets hr] at hP ⊢
  exact orthogonal_polygon_sum_mem_K3 hP hC hV
    (CaseB.convexHull_normal_subset (D.offsets_normal hr))

end Uniform5.Composition
