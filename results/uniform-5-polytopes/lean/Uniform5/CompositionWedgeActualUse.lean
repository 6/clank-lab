import Uniform5.CompositionWedgeActualGeometry

/-! Apply the literal W computation to actual parent edges. Admissibility,
endpoint protection, and exclusion of exceptional diagonals are kept
separate from the two computed distance conclusions. -/
noncomputable section
namespace Uniform5.Composition.Wedge
open Set

theorem pair_symm {a b x y : Space 5} (h : pair a b x y) : pair a b y x := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [pair]

/-- Paper Wuse with actual edge exclusion for the exceptional diagonals.
All distances and separation are inherited from the actual parent. -/
theorem actual_only_protected_edges (p1 : CaseB.P1) (hW : W p1)
    {n : Parameter} {f : CaseB.WFan} (hn : CaseB.LargeParameter n)
    (hf : CaseB.WListed p1 n f) (F : Geometry) (hreal : RealizesWFan p1 n f F)
    {P : Set (Space 5)} (hP : UnitUniform 5 P) {v : Space 5}
    (hv : v ∈ P.extremePoints ℝ)
    (protectedEdge diagonal : Space 5 → Space 5 → Prop)
    (hprotected_symm : ∀ {x y}, protectedEdge x y → protectedEdge y x)
    (hends : ∀ x ∈ F.ends, ∃ y ∈ (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ,
      protectedEdge x y ∧ CaseB.chord 17 ≤ dist x y)
    (hcover : ∀ x ∈ (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ,
      x ∈ F.vertices ∨ F.Admissible x)
    (hspecial : ∀ x y, F.specialPair x y → protectedEdge x y ∨ diagonal x y)
    (hdiagonal : ∀ x y, diagonal x y → ¬ Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y)
    {x y : Space 5} (he : Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y)
    (hlong : CaseB.chord 17 ≤ dist x y) : protectedEdge x y := by
  let Q := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
  have hm := unitUniform5_vertexFigure_vertex_metric hP hv
  by_contra hnot
  have hxends : x ∉ F.ends := by
    intro hx
    obtain ⟨z, hz, hxz, hlz⟩ := hends x hx
    have hzy := CaseB.long_edges_same_endpoint (hm.1 x he.1) (hm.1 y he.2.1)
      (hm.1 z hz) (le_refl 1) hlong hlz (hm.2 y he.2.1 z hz)
    exact hnot (hzy ▸ hxz)
  have hyends : y ∉ F.ends := by
    intro hy
    obtain ⟨z, hz, hyz, hlz⟩ := hends y hy
    have hzx := CaseB.long_edges_same_endpoint (hm.1 y he.2.1) (hm.1 x he.1)
      (hm.1 z hz) (le_refl 1) (by simpa only [dist_comm] using hlong) hlz (hm.2 x he.1 z hz)
    exact hnot (hprotected_symm (hzx ▸ hyz))
  have heligible : ∀ z ∈ Q.extremePoints ℝ, z ∉ F.ends → F.Admissible z ∨ F.Allowed z := by
    intro z hz hends
    rcases hcover z hz with hfan | ha
    · exact Or.inr ⟨hfan, hends⟩
    · exact Or.inl ha
  have hfan := hW.no_long_pair n f hn hf F hreal x y
    (heligible x he.1 hxends) (heligible y he.2.1 hyends) hlong
  have hsp : F.specialPair x y := by
    by_contra hh
    exact (not_lt_of_ge hlong) (hW.fan_distances n f hn hf F hreal x hfan.1 y hfan.2 hh)
  rcases hspecial x y hsp with hp | hd
  · exact hnot hp
  · exact hdiagonal x y hd he

end Uniform5.Composition.Wedge
