import Uniform5.CompositionGlobalLabels
import Uniform5.CompositionFigureModelTransport

/-! Actual two-dimensional ridge templates from intrinsic cell types. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical

/-- A representative vertex figure of a uniform three-dimensional cell.
The selected vertex is an actual extreme point of the whole cell model. -/
noncomputable def uniformCellFigure (C : Set (Space 3)) (hC : UnitUniform 3 C) :
    Set (Space 3) :=
  let hF := uniform_finitePolytope hC.1
  vertexFigure C (Classical.choose (vertices_nonempty hF)) (vertexCentroid (vertices C hF))

/-- The fallback applies only to types without a unit-uniform cell model.
Actual three-cells are proved to take the genuine branch. -/
noncomputable def cellFigureModel (c : CellType) : Set (Space 3) :=
  if h : UnitUniform 3 (cellTypeModel c) then uniformCellFigure (cellTypeModel c) h else ∅

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem actual_cell_figure_matches {C : Set E} (hC : UnitUniform 3 C)
    {c : CellType} (hc : Congruent C (cellTypeModel c))
    {v : E} (hv : v ∈ C.extremePoints ℝ) :
    Congruent (vertexFigure C v (vertexCentroid (vertices C (uniform_finitePolytope hC.1))))
      (cellFigureModel c) := by
  have hm := (unitUniform_cross_congruent_iff hc 3).mp hC
  let hF := uniform_finitePolytope hm.1
  have hw : Classical.choose (vertices_nonempty hF) ∈ (cellTypeModel c).extremePoints ℝ := by
    rw [← coe_vertices (cellTypeModel c) hF]
    exact Classical.choose_spec (vertices_nonempty hF)
  rw [cellFigureModel, dif_pos hm]
  exact unitUniform_vertexFigure_model_congruent (n := 0) hC hc hv hw

/-- A cell's intersection with the parent figure is its own intrinsic
figure template, labeled consistently with every incident cycle. -/
theorem unitUniform5_cell_figure_matches {P C : Set E} (hP : UnitUniform 5 P)
    (hC : IsConvexFace P C) (hd : affineDimension C = 3)
    {v : E} (hv : v ∈ C.extremePoints ℝ) :
    Congruent (C ∩ vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))))
      (cellFigureModel (globalCellLabel C)) := by
  have hne : C.Nonempty := ⟨v, hv.1⟩
  have hUC : UnitUniform 3 C := by
    have h := unitUniform_face hP hC hne (by rw [hd]; omega)
    simpa only [hd] using h
  have hc := globalCellLabel_matches C
    (exists_actual_cellType (uniform_finitePolytope hUC.1) hd)
  rw [uniform_vertexFigure_face_inter hP.1 hC hne hv.1]
  exact actual_cell_figure_matches hUC hc hv

end Uniform5.Composition
