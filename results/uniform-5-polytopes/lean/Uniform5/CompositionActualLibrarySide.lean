import Uniform5.CompositionModelWordOrbit

/-! Genuine incident cells determine the side labels of an actual cycle. -/
noncomputable section
namespace Uniform5.Composition
open Set

namespace ActualLibraryCycle
variable {N : LibraryNumericalData} {P G : Set (Space 5)} {k : LibraryPolygonSize}
  (A : ActualLibraryCycle N P G k)

theorem side_of_actual (hP : UnitUniform 5 P) (hG : PolygonFace P G k.val)
    (i : Fin A.cycle.length) (s : LibraryWordSide) (hk : k.val = s.polygon)
    (hf : A.labels.facetLabel i = s.facet) {C D : Set (Space 5)}
    (hC : Facet (A.cycle.facet i) C) (hD : Facet (A.cycle.facet i) D)
    (hGC : G ⊆ C) (hGD : G ⊆ D) (hCD : C ≠ D)
    (hCA : Congruent C (cellTypeModel s.left))
    (hDB : Congruent D (cellTypeModel s.right)) : s ∈ A.word.sideSet := by
  have hK := A.cycle.facet_unitUniform hP i
  have hGi : PolygonFace (A.cycle.facet i) G k.val :=
    ⟨face_restrict hG.1 (A.cycle.facet_incidence i).1.1.2.1
      (A.cycle.facet_incidence i).2.1, hG.2⟩
  have hleft : Facet (A.cycle.facet i) (A.cycle.cell i) :=
    ⟨face_restrict (A.cycle.cell_face i) (A.cycle.facet_incidence i).1.1.2.1
      (A.cycle.facet_incidence i).2.2.1,
      (polygonFace_nonempty hG).mono (A.cycle.cell_contains i), by
        rw [A.cycle.cell_dimension, uniform_dimension hK.1]⟩
  have hright : Facet (A.cycle.facet i) (A.cycle.cell (i.val + 1)) :=
    ⟨face_restrict (A.cycle.cell_face (i.val + 1)) (A.cycle.facet_incidence i).1.1.2.1
      (A.cycle.facet_incidence i).2.2.2,
      (polygonFace_nonempty hG).mono (A.cycle.cell_contains (i.val + 1)), by
        rw [A.cycle.cell_dimension, uniform_dimension hK.1]⟩
  have htwo : TwoContainingFacets (A.cycle.facet i) G :=
    finitePolytope_ridge_two_facets (uniform_finitePolytope hK.1) hGi.1
      (polygonFace_nonempty hG) (by rw [hGi.2.1, uniform_dimension hK.1])
  have hp := htwo.pairs ⟨hleft, A.cycle.cell_contains i⟩
    ⟨hright, A.cycle.cell_contains (i.val + 1)⟩
    (cell_cycle_consecutive_ne A.cycle.length_ge A.cycle.cell A.cycle.cell_closed
      A.cycle.cell_injective i.isLt) ⟨hC, hGC⟩ ⟨hD, hGD⟩ hCD
  apply (A.word.mem_sideSet s).mpr
  refine ⟨hk, i, hf, ?_⟩
  change (A.labels.cellLabel i = s.left ∧
      A.labels.cellLabel (finRotate A.cycle.length i) = s.right) ∨
    (A.labels.cellLabel i = s.right ∧
      A.labels.cellLabel (finRotate A.cycle.length i) = s.left)
  rw [cycle_apply_finRotate (by have := A.cycle.length_ge; omega)
    A.labels.cellLabel A.closed]
  rcases hp with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl ⟨A.cellLabel_eq_of_congruent i s.left (ha ▸ hCA),
      A.cellLabel_eq_of_congruent (i.val + 1) s.right (hb ▸ hDB)⟩
  · exact Or.inr ⟨A.cellLabel_eq_of_congruent i s.right (ha ▸ hDB),
      A.cellLabel_eq_of_congruent (i.val + 1) s.left (hb ▸ hCA)⟩

end ActualLibraryCycle
end Uniform5.Composition
