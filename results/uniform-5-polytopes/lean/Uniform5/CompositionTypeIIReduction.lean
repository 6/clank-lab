import Uniform5.CompositionWedgeTypeIIUse
import Uniform5.CompositionLongPairReduction

/-! The actual Type II fan and W force the same two-face reduction. -/
noncomputable section
namespace Uniform5.Composition.ActualPolygonCycle
open Set
variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

theorem typeII_two_large_reduction (p1 : CaseB.P1) (hW : Wedge.W p1)
    {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    {v : Space 5} (hvG : v ∈ G.extremePoints ℝ) (hII : D.CaseBTypeII n)
    {H : Set (Space 5)} {m : ℕ} (hH : PolygonFace P H m) (hm : 17 ≤ m)
    (hvH : v ∈ H.extremePoints ℝ) (hGH : G ≠ H) :
    TwoLargeFacesCoverAt P v G H ∧ ∃ K, Facet P K ∧ G ⊆ K ∧ H ⊆ K := by
  obtain ⟨T⟩ := D.typeII_actual_fan hP hG hn hvG hII
  have ha := (T.base.polygon_neighbors T.base.a).mpr (Or.inl rfl)
  have hb := (T.base.polygon_neighbors T.base.b).mpr (Or.inr rfl)
  have hbound := fun x y => T.long_edges_two_pairs p1 hW hP hG hn hvG (x := x) (y := y)
  have hends := T.opposite_contains_apexes hP hG hn hvG
  refine ⟨twoLargeFacesCoverAt_of_two_long_pairs hP hG hH hm hvG hvH hGH ha hb hbound,
    D.facet T.opposite, (D.facet_incidence T.opposite).1,
    (D.facet_incidence T.opposite).2.1, ?_⟩
  exact partner_polygon_subset_of_long_pairs hP hG hH hm hvG hvH hGH ha hb
    (D.facet_incidence T.opposite).1.1 ((D.facet_incidence T.opposite).2.1 hvG.1)
    hends.1 hends.2 hbound

end Uniform5.Composition.ActualPolygonCycle
