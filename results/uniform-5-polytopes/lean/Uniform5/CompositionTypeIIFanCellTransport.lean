import Uniform5.CompositionPairedMixedCoverage
import Uniform5.CompositionAntiprismCellSlices

/-! Every vertex in a coherent Type II fan belongs to a whole actual
antiprism cell obtained by an orthogonal translation of its base cell. -/
noncomputable section
namespace Uniform5.Composition
open Set
namespace TypeIIActualFanData
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIIActualFanData D v n)

theorem fan_vertex_cell_translate (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hvG : v ∈ G.extremePoints ℝ) {w : Space 5}
    (hw : w ∈ actualPolygonFanVertices hP D v) :
    ∃ d ∈ CaseB.normals (D.cell T.anti),
      IsConvexFace P (CaseB.translate (D.cell T.anti) d) ∧
      Congruent (CaseB.translate (D.cell T.anti) d) (antiprismModel n) ∧
      w ∈ CaseB.translate (D.cell T.anti) d := by
  have hside : Edge (D.facet T.anti) v w ∨
      Edge (D.facet ((finRotate D.length).symm T.anti)) v w := by
    rcases (T.mem_fan_vertices hP hG hn hvG w).mp hw with h | h | h | h | h | h
    · exact Or.inl ((T.first_neighbors w).mpr (Or.inl h))
    · exact Or.inl ((T.first_neighbors w).mpr (Or.inr (Or.inl h)))
    · exact Or.inl ((T.first_neighbors w).mpr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inl ((T.first_neighbors w).mpr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inl ((T.first_neighbors w).mpr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
    · exact Or.inr ((T.last_neighbors w).mpr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  have translate_at (j : Fin D.length) (hmodel : Congruent (D.facet j) (antiprismPrismModel n))
      (hC : Facet (D.facet j) (D.cell T.anti)) (he : Edge (D.facet j) v w) :
      ∃ d ∈ CaseB.normals (D.cell T.anti),
        IsConvexFace P (CaseB.translate (D.cell T.anti) d) ∧
        Congruent (CaseB.translate (D.cell T.anti) d) (antiprismModel n) ∧
        w ∈ CaseB.translate (D.cell T.anti) d := by
    have hK := (D.facet_incidence j).1
    have hGK : PolygonFace (D.facet j) G n :=
      ⟨face_restrict hG.1 hK.1.2.1 (D.facet_incidence j).2.1, hG.2⟩
    obtain ⟨d, hd, hF, hFA, hwF⟩ := unitUniform4_antiprismPrism_cell_translate
      (D.facet_unitUniform hP j) (by omega) hmodel hGK hC (D.cell_contains T.anti)
      T.antiprism he.2.1
    exact ⟨d, hd, ⟨hF.1.1, hK.1.2.trans hF.1.2⟩, hFA, hwF⟩
  rcases hside with he | he
  · exact translate_at T.anti T.first_model (D.cell_facet hP hG T.anti) he
  · apply translate_at _ T.last_model (D.cell_facet_of_not_away hP hG T.anti _ ?_) he
    rw [D.slotsAwayFrom_mem]
    exact fun hh => hh.2 ((finRotate D.length).apply_symm_apply T.anti)

end TypeIIActualFanData
end Uniform5.Composition
