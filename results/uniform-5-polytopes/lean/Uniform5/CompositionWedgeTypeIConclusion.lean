import Uniform5.CompositionWedgeTypeIUse
import Uniform5.CompositionWedgeCyclicLabels
import Uniform5.CompositionWedgePartnerLabels

/-! Compose actual P1 and partner filtering, cyclic labels, literal W
realization, and the Wuse proof. No case-exclusion premise is supplied. -/
noncomputable section
namespace Uniform5.Composition.TypeIFanChart
open Set
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIFanChart D v n)

/-- An actual Type I fan has at most its original long edge and one
partner long edge. Every premise after the named computed inputs is actual
polytope, polygon, cycle, or facet data. -/
theorem typeI_long_edges_indexed_pair (classification4D : CitedClassification4D)
    (p1 : CaseB.P1) (partner : CaseB.PartnerRadiusFilter) (hW : Wedge.W p1)
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hvG : v ∈ G.extremePoints ℝ) (geometry : D.Stage1Geometry n)
    (q : Fin D.length → ℕ) (hq : ∀ i, 3 ≤ q i)
    (hmodel : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    (hcell : ∀ i : Fin D.length, Congruent (D.cell i) (polygonPrismModel n)) :
    ∃ j : Fin D.length, ∀ x y,
      Edge (vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y →
      CaseB.chord 17 ≤ dist x y → Wedge.pair T.a T.b x y ∨
        Wedge.pair (T.lateral j) (T.lateral (finRotate D.length j)) x y := by
  have hlen := D.nonexceptional_length_le_five classification4D hP hG
    (large_polygon_nonexceptional hn)
  rcases D.typeI_actual_wListed classification4D p1 partner hP hG hn geometry q hq
    hmodel hcell with ⟨cs, hcyclic, hw⟩ | ⟨m, cs, hm, hperm, hw, _⟩
  · obtain ⟨L⟩ := cyclicLabels_of_dihedral q hcyclic
    refine ⟨⟨0, by have := D.length_ge; omega⟩, fun x y he hl => Or.inl ?_⟩
    exact T.wedge_unpaired_only_edge p1 hW hP hG hn hvG hlen hq hmodel hcell (cs := cs) (by simpa [← List.map_eq_flatMap, List.map_map, Function.comp_def] using L) hw he hl
  · have hcyclic := CaseB.wListed_paired_dihedral hw hperm
    obtain ⟨L₀⟩ := cyclicLabels_of_dihedral q hcyclic
    have L : CyclicLabels (D := D) (some (m : ℝ) :: cs.map (fun k => some (k : ℝ))) q := by
      simpa [← List.map_eq_flatMap, List.map_map, Function.comp_def] using L₀
    let S := T.wedgeShape hP hG (by omega) (by omega) hvG hlen hq hmodel hcell L
    refine ⟨L.facet S.first, fun x y he hl => ?_⟩
    rcases T.wedge_paired_only_edges p1 hW hP hG hn hvG hlen hq hmodel hcell hm L hw he hl with hh | hh
    · exact Or.inl hh
    · right
      change Wedge.pair (T.lateral (L.vertex S.first))
        (T.lateral (L.vertex (finRotate _ S.first))) x y at hh
      rcases L.incidence S.first with ⟨ha,hb⟩ | ⟨hb,ha⟩
      · simpa only [ha,hb] using hh
      · rw [ha,hb] at hh
        rcases hh with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
        · exact Or.inr ⟨h₁,h₂⟩
        · exact Or.inl ⟨h₁,h₂⟩

/-- An actual Type I fan has at most its original long edge and one
partner long edge. Every premise after the named computed inputs is actual
polytope, polygon, cycle, or facet data. -/
theorem typeI_long_edges_two_pairs (classification4D : CitedClassification4D)
    (p1 : CaseB.P1) (partner : CaseB.PartnerRadiusFilter) (hW : Wedge.W p1)
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hvG : v ∈ G.extremePoints ℝ) (geometry : D.Stage1Geometry n)
    (q : Fin D.length → ℕ) (hq : ∀ i, 3 ≤ q i)
    (hmodel : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    (hcell : ∀ i : Fin D.length, Congruent (D.cell i) (polygonPrismModel n)) :
    ∃ a b : Space 5, ∀ x y,
      Edge (vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y →
      CaseB.chord 17 ≤ dist x y → Wedge.pair T.a T.b x y ∨ Wedge.pair a b x y := by
  have hlen := D.nonexceptional_length_le_five classification4D hP hG
    (large_polygon_nonexceptional hn)
  rcases D.typeI_actual_wListed classification4D p1 partner hP hG hn geometry q hq
    hmodel hcell with ⟨cs, hcyclic, hw⟩ | ⟨m, cs, hm, hperm, hw, _⟩
  · obtain ⟨L⟩ := cyclicLabels_of_dihedral q hcyclic
    refine ⟨T.a, T.b, fun x y he hl => Or.inl ?_⟩
    exact T.wedge_unpaired_only_edge p1 hW hP hG hn hvG hlen hq hmodel hcell (cs := cs) (by simpa [← List.map_eq_flatMap, List.map_map, Function.comp_def] using L) hw he hl
  · have hcyclic := CaseB.wListed_paired_dihedral hw hperm
    obtain ⟨L₀⟩ := cyclicLabels_of_dihedral q hcyclic
    have L : CyclicLabels (D := D) (some (m : ℝ) :: cs.map (fun k => some (k : ℝ))) q := by
      simpa [← List.map_eq_flatMap, List.map_map, Function.comp_def] using L₀
    let S := T.wedgeShape hP hG (by omega) (by omega) hvG hlen hq hmodel hcell L
    refine ⟨S.x S.first, S.x (finRotate _ S.first), fun x y he hl => ?_⟩
    exact T.wedge_paired_only_edges p1 hW hP hG hn hvG hlen hq hmodel hcell hm L hw he hl

end Uniform5.Composition.TypeIFanChart
