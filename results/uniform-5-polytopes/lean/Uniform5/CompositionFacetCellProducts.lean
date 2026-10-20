import Uniform5.CompositionActualCellProducts
import Uniform5.CompositionCaseBCellModels

/-! A four-dimensional selected cell leaves a one-dimensional unit offset
factor, hence gives precisely a prism in K2. -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem orthogonal_facet_offset_dimension
    {C X : Set E} (hP : UnitUniform 5 (C + X)) (hC : UnitUniform 4 C)
    (hV : FinitePolytope X) (hX : X ⊆ CaseB.normals C) : affineDimension X = 1 := by
  have h := affineDimension_orthogonal_sum
    (finitePolytope_nonempty (uniform_finitePolytope hC.1)) (finitePolytope_nonempty hV) hX
  rw [uniform_dimension hP.1, uniform_dimension hC.1] at h
  omega

theorem orthogonal_facet_sum_mem_K2
    {C X : Set E} (hP : UnitUniform 5 (C + X)) (hC : UnitUniform 4 C)
    (hV : FinitePolytope X) (hX : X ⊆ CaseB.normals C) : K2 (C + X) := by
  have hd := orthogonal_facet_offset_dimension hP hC hV hX
  have hU := unitUniform_orthogonal_factor (n := 2) hP
    (uniform_finitePolytope hC.1) hV hX hd
  have hx := finitePolytope_unitEdges_dim_one_congruent hV hU.2 hd
  obtain ⟨_, Q, _, hQC, hQ⟩ := exists_unitUniform_intrinsic_model (n := 1) hC
  exact ⟨Q, hQ, congruent_orthogonal_sum_product hX (congruent_symm hQC) hx⟩

theorem facetCellSystem_mem_K2 (D : CaseB.CellSystem E)
    {r : E} (hr : r ∈ D.vertices)
    (hP : UnitUniform 5 (convexHull ℝ D.vertices))
    (hC : UnitUniform 4 (convexHull ℝ (D.cell r))) : K2 (convexHull ℝ D.vertices) := by
  classical
  have hV : FinitePolytope (convexHull ℝ (D.offsets hr)) :=
    ⟨(D.offsets_finite hr).toFinset,
      (D.offsets_finite hr).toFinset_nonempty.mpr (D.offsets_nonempty hr),
      by rw [Set.Finite.coe_toFinset]⟩
  rw [D.convexHull_eq_cell_add_offsets hr] at hP ⊢
  exact orthogonal_facet_sum_mem_K2 hP hC hV
    (CaseB.convexHull_normal_subset (D.offsets_normal hr))

theorem actual_four_cells_mem_K2 {P : Set E} (hP : UnitUniform 5 P)
    (C : E → Set E)
    (hface : ∀ v ∈ P.extremePoints ℝ, IsConvexFace P (C v))
    (hmem : ∀ v ∈ P.extremePoints ℝ, v ∈ C v)
    (htransport : FaceCellTransport P C)
    {r : E} (hr : r ∈ P.extremePoints ℝ) (hd : affineDimension (C r) = 4) : K2 P := by
  let D := actualFaceCellSystem hP C hface hmem htransport
  have heq : convexHull ℝ D.vertices = P :=
    (finitePolytope_eq_convexHull_extremePoints (uniform_finitePolytope hP.1)).symm
  have hC : convexHull ℝ (D.cell r) = C r :=
    (finitePolytope_eq_convexHull_extremePoints (finitePolytope_face
      (uniform_finitePolytope hP.1) (hface r hr) ⟨r, hmem r hr⟩)).symm
  rw [← heq]
  apply facetCellSystem_mem_K2 D hr (heq.symm ▸ hP)
  rw [hC, ← hd]
  exact unitUniform_all_faces hP (hface r hr) ⟨r, hmem r hr⟩

end Uniform5.Composition
