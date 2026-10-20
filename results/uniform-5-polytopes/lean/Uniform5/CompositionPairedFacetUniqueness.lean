import Uniform5.CompositionPairedCommonFacet
import Uniform5.CompositionTypeIFanEdges
import Uniform5.CompositionFacetNeighborDetermination

/-! The common facet of two distinct large polygons in an actual Type I
fan is unique, because their four root neighbors determine that facet. -/
noncomputable section
namespace Uniform5.Composition
open Set

namespace TypeIFanChart
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIFanChart D v n)

include T in
theorem common_facet_unique (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hvG : v ∈ G.extremePoints ℝ)
    {H : Set (Space 5)} {m : ℕ} (hH : PolygonFace P H m) (hm : 17 ≤ m)
    (hvH : v ∈ H.extremePoints ℝ) (hGH : G ≠ H)
    (q : Fin D.length → ℕ) (hq : ∀ i, 3 ≤ q i)
    (hmodel : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    {K F : Set (Space 5)} (hK : Facet P K) (hGK : G ⊆ K) (hHK : H ⊆ K)
    (hF : Facet P F) (hGF : G ⊆ F) (hHF : H ⊆ F) : K = F := by
  obtain ⟨j, hj⟩ := (D.facet_coverage K).mp ⟨hK, hGK⟩
  have hHK' : H ⊆ D.facet j := hj.symm ▸ hHK
  have hp := T.common_facet_partner_edges hP hG hn hvG hH hm hvH hGH q hq hmodel j hHK'
  apply facets_eq_of_figure_vertices hP hK hF
    (hG.1.2.extremePoints_subset_extremePoints hvG) (hGK hvG.1) (hGF hvG.1)
  rw [← hj, T.facet_figure_vertices hP hG hvG j]
  rintro x (rfl | rfl | rfl | rfl)
  · exact hGF ((T.polygon_neighbors T.a).mpr (Or.inl rfl)).2.1.1
  · exact hGF ((T.polygon_neighbors T.b).mpr (Or.inr rfl)).2.1.1
  · exact hHF hp.1.2.1.1
  · exact hHF hp.2.1.2.1.1

end TypeIFanChart

theorem unitUniform5_paired_typeI_common_facet_unique
    {P G H K F : Set (Space 5)} (hP : UnitUniform 5 P) {n m : ℕ}
    (hG : PolygonFace P G n) (hn : 17 ≤ n) (hH : PolygonFace P H m) (hm : 17 ≤ m)
    {v : Space 5} (hvG : v ∈ G.extremePoints ℝ) (hvH : v ∈ H.extremePoints ℝ)
    (hGH : G ≠ H) (D : ActualPolygonCycle P G) (hI : D.CaseBTypeI n)
    (hK : Facet P K) (hGK : G ⊆ K) (hHK : H ⊆ K)
    (hF : Facet P F) (hGF : G ⊆ F) (hHF : H ⊆ F) : K = F := by
  obtain ⟨_, q, hq, _⟩ := hI
  obtain ⟨T⟩ := D.typeI_fan_chart hP hG (by omega) (by omega) hvG q
    (fun i => (hq i).1) (fun i => (hq i).2.1)
  exact T.common_facet_unique hP hG hn hvG hH hm hvH hGH q
    (fun i => (hq i).1) (fun i => (hq i).2.1) hK hGK hHK hF hGF hHF

end Uniform5.Composition
