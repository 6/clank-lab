import Uniform5.CompositionPairedFanCardinality
import Uniform5.CompositionTypeIISecondCorner
import Uniform5.CompositionPairedTypeIIImpossible

/-! Both actual Type II base corners are forced into the partner fan.
Equal six-point cardinalities then give equality of the mixed fan vertex
sets and complete coverage of every root neighbor by the Type II fan. -/
noncomputable section
namespace Uniform5.Composition
open Set
namespace TypeIFanChart
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIFanChart D v n)

include T in
theorem paired_mixed_fan_vertices_eq
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hvG : v ∈ G.extremePoints ℝ) {H : Set (Space 5)} {m : ℕ}
    (hH : PolygonFace P H m) (hm : 17 ≤ m) (hvH : v ∈ H.extremePoints ℝ)
    (hGH : G ≠ H) (A : ActualPolygonCycle P H) (U : TypeIIActualFanData A v m)
    (hcover : TwoLargeFacesCoverAt P v G H) (hlen : D.length = 4)
    (j : Fin D.length) (hHK : H ⊆ D.facet j)
    (q : Fin D.length → ℕ) (hq : ∀ i, 3 ≤ q i)
    (hmodel : ∀ i, Congruent (D.facet i) (duoprismModel n (q i))) :
    actualPolygonFanVertices hP D v = actualPolygonFanVertices hP A v := by
  have hc := T.common_facet_partner_edges hP hG hn hvG hH hm hvH hGH q hq hmodel j hHK
  obtain ⟨k, hk⟩ := (A.facet_coverage (D.facet j)).mp ⟨(D.facet_incidence j).1, hHK⟩
  have hGk : G ⊆ A.facet k := hk.symm ▸ (D.facet_incidence j).2.1
  have ha := U.common_facet_partner_edges hP hH hm hvH hG hn hvG hGH.symm k hGk
  have hrev : TwoLargeFacesCoverAt P v H G := fun F l hF hl hvF =>
    (hcover F l hF hl hvF).symm
  have hx := U.base_x_mem_partner classification3D classification4D N S hLIB hS1 hB2
    hP hH hm hvH hG D hrev ha.1 ha.2
  have hy := U.base_y_mem_partner classification3D classification4D N S hLIB hS1 hB2
    hP hH hm hvH hG D hrev ha.1 ha.2
  have hGmem (x : Space 5) (he : Edge G v x) : x ∈ actualPolygonFanVertices hP D v := by
    rw [T.mem_fan_vertices hP hG hvG]
    rcases (T.polygon_neighbors x).mp he with hh | hh
    · exact Or.inl hh
    · exact Or.inr (Or.inl hh)
  have hcd : T.lateral j ≠ T.lateral (finRotate D.length j) :=
    fun he => (finRotate_ne_and_twice_ne D.length_ge j).1 (T.lateral_injective he).symm
  have hp := finitePolytope_planar_neighbors
    (finitePolytope_face (uniform_finitePolytope hP.1) hH.1 (polygonFace_nonempty hH))
    hH.2.1 hc.1 hc.2.1 hcd
  have hHmem (x : Space 5) (he : Edge H v x) : x ∈ actualPolygonFanVertices hP D v := by
    rw [T.mem_fan_vertices hP hG hvG]
    rcases (hp x).mp he with he | he
    · exact Or.inr (Or.inr ⟨j, he⟩)
    · exact Or.inr (Or.inr ⟨_, he⟩)
  have hsub : actualPolygonFanVertices hP A v ⊆ actualPolygonFanVertices hP D v := by
    intro x hxA
    rcases (U.mem_fan_vertices hP hH hm hvH x).mp hxA with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hHmem _ ((U.base.polygon_neighbors _).mpr (Or.inl rfl))
    · exact hHmem _ ((U.base.polygon_neighbors _).mpr (Or.inr rfl))
    · exact hx
    · exact hy
    · exact hGmem _ ha.1
    · exact hGmem _ ha.2
  symm
  exact Set.eq_of_subset_of_ncard_le hsub
    (by rw [T.four_fan_vertices_ncard hP hG hvG hlen, U.fan_vertices_ncard hP hH hm hvH])
    (by rw [T.four_fan_vertices_range hP hG hvG hlen j]; exact Set.finite_range _)

end TypeIFanChart

theorem unitUniform5_paired_mixed_typeII_vertex_cover
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    {P G H K : Set (Space 5)} (hP : UnitUniform 5 P) {n m : ℕ}
    (hG : PolygonFace P G n) (hn : 17 ≤ n) (hH : PolygonFace P H m) (hm : 17 ≤ m)
    {v : Space 5} (hvG : v ∈ G.extremePoints ℝ) (hvH : v ∈ H.extremePoints ℝ)
    (hGH : G ≠ H) (hcover : TwoLargeFacesCoverAt P v G H)
    (hK : Facet P K) (hGK : G ⊆ K) (hHK : H ⊆ K)
    (D : ActualPolygonCycle P G) (A : ActualPolygonCycle P H)
    (hI : D.CaseBTypeI n) (hII : A.CaseBTypeII m)
    {w : Space 5} (hw : Edge P v w) : w ∈ actualPolygonFanVertices hP A v := by
  obtain ⟨hlen, q, j, hq, hj, _, _⟩ :=
    unitUniform5_paired_mixed_four_and_parameters classification3D classification4D N S
      hLIB hS1 hB2 hP hG hn hH hm hvG hvH hGH hcover hK hGK hHK D A hI hII
  obtain ⟨T⟩ := D.typeI_fan_chart hP hG (by omega) (by omega) hvG q
    (fun i => (hq i).1) (fun i => (hq i).2.1)
  obtain ⟨U⟩ := A.typeII_actual_fan hP hH hm hvH hII
  have heq := T.paired_mixed_fan_vertices_eq classification3D classification4D N S
    hLIB hS1 hB2 hP hG hn hvG hH hm hvH hGH A U hcover hlen j (hj.symm ▸ hHK)
    q (fun i => (hq i).1) (fun i => (hq i).2.1)
  obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius hP.1
  have hwV : w ∈ (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ := by
    rw [finitePolytope_unit_vertexFigure_extremePoints (uniform_finitePolytope hP.1)
      hw.1 _ (intrinsicRadius P) hs hP.2]
    exact hw
  rcases unitUniform5_two_fan_vertex_cover classification3D classification4D N S
    hLIB hS1 hB2 hP hG hn hw.1 hcover D A hwV with hD | hA
  · exact heq ▸ hD
  · exact hA

end Uniform5.Composition
