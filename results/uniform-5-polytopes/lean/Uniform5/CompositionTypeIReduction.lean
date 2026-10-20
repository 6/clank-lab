import Uniform5.CompositionWedgeTypeIConclusion
import Uniform5.CompositionLongPairReduction

/-! The actual Type I fan and W force all large polygons at the root
into one pair contained in a single actual duoprism facet. -/
noncomputable section
namespace Uniform5.Composition.ActualPolygonCycle
open Set
variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

theorem typeI_two_large_reduction
    (classification4D : CitedClassification4D) (p1 : CaseB.P1)
    (partner : CaseB.PartnerRadiusFilter) (hW : Wedge.W p1)
    {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    {v : Space 5} (hvG : v ∈ G.extremePoints ℝ)
    (geometry : D.Stage1Geometry n) (hI : D.CaseBTypeI n)
    {H : Set (Space 5)} {m : ℕ} (hH : PolygonFace P H m) (hm : 17 ≤ m)
    (hvH : v ∈ H.extremePoints ℝ) (hGH : G ≠ H) :
    TwoLargeFacesCoverAt P v G H ∧
      ∃ K, Facet P K ∧ G ⊆ K ∧ H ⊆ K := by
  obtain ⟨_, q, hq, _⟩ := hI
  obtain ⟨T⟩ := D.typeI_fan_chart hP hG (by omega) (by omega) hvG q
    (fun i => (hq i).1) (fun i => (hq i).2.1)
  obtain ⟨j, hj⟩ := T.typeI_long_edges_indexed_pair classification4D p1 partner hW
    hP hG hn hvG geometry q (fun i => (hq i).1)
    (fun i => (hq i).2.1) (fun i => (hq i).2.2)
  have ha := (T.polygon_neighbors T.a).mpr (Or.inl rfl)
  have hb := (T.polygon_neighbors T.b).mpr (Or.inr rfl)
  refine ⟨twoLargeFacesCoverAt_of_two_long_pairs hP hG hH hm hvG hvH hGH ha hb hj,
    D.facet j, (D.facet_incidence j).1, (D.facet_incidence j).2.1, ?_⟩
  apply partner_polygon_subset_of_long_pairs hP hG hH hm hvG hvH hGH ha hb
    (D.facet_incidence j).1.1 ((D.facet_incidence j).2.1 hvG.1) _ _ hj
  · exact ((T.facet_neighbors j (T.lateral j)).mpr (Or.inr (Or.inr (Or.inl rfl)))).2.1.1
  · exact ((T.facet_neighbors j (T.lateral (finRotate D.length j))).mpr
      (Or.inr (Or.inr (Or.inr rfl)))).2.1.1

end Uniform5.Composition.ActualPolygonCycle
