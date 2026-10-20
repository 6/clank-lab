import Uniform5.CompositionPairedFacetTransport

/-! All root data needed for the paired Type I product are derived from
the actual two cycles, including the common unit normal and the two
whole translated polygon faces. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem unitUniform5_paired_typeI_root_transport
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    {P G H K : Set (Space 5)} (hP : UnitUniform 5 P) {n m : ℕ}
    (hG : PolygonFace P G n) (hn : 17 ≤ n) (hH : PolygonFace P H m) (hm : 17 ≤ m)
    {v : Space 5} (hvG : v ∈ G.extremePoints ℝ) (hvH : v ∈ H.extremePoints ℝ)
    (hGH : G ≠ H) (hcover : TwoLargeFacesCoverAt P v G H)
    (hK : Facet P K) (hGK : G ⊆ K) (hHK : H ⊆ K)
    (D : ActualPolygonCycle P G) (A : ActualPolygonCycle P H)
    (hI : D.CaseBTypeI n) (hJ : A.CaseBTypeI m) :
    Congruent K (duoprismModel n m) ∧ ∃ z, Edge P v z ∧ z - v ∈ CaseB.normals K ∧
      PolygonFace P (CaseB.translate G (z - v)) n ∧
      PolygonFace P (CaseB.translate H (z - v)) m ∧
      ∀ w, Edge P v w → w ∈ K ∨ w = z := by
  have hrev : TwoLargeFacesCoverAt P v H G := fun F k hF hk hvF =>
    (hcover F k hF hk hvF).symm
  obtain ⟨hlen, q, j, hq, hj, hqm, hother⟩ :=
    unitUniform5_paired_typeI_three_and_parameters classification3D classification4D N S
      hLIB hS1 hB2 hP hG hn hH hm hvG hvH hGH hcover hK hGK hHK D A hI hJ
  obtain ⟨hlenA, r, k, hr, hk, hrn, hotherA⟩ :=
    unitUniform5_paired_typeI_three_and_parameters classification3D classification4D N S
      hLIB hS1 hB2 hP hH hm hG hn hvH hvG hGH.symm hrev hK hHK hGK A D hJ hI
  obtain ⟨T⟩ := D.typeI_fan_chart hP hG (by omega) (by omega) hvG q
    (fun i => (hq i).1) (fun i => (hq i).2.1)
  obtain ⟨U⟩ := A.typeI_fan_chart hP hH (by omega) (by omega) hvH r
    (fun i => (hr i).1) (fun i => (hr i).2.1)
  have hparams := finRotate_ne_and_twice_ne D.length_ge j
  have hparamsA := finRotate_ne_and_twice_ne A.length_ge k
  have hGedges := T.common_facet_partner_edges hP hG hn hvG hH hm hvH hGH q
    (fun i => (hq i).1) (fun i => (hq i).2.1) j (hj.symm ▸ hHK)
  have hmem := T.paired_k3_lateral_mem_partner classification3D classification4D N S
    hLIB hS1 hB2 hP hG hn hvG hH A hcover hlen j hGedges.1 hGedges.2.1
  have heq := T.remaining_eq_partner_remaining hP hG hvG hH hvH A U hlenA j k
    (hj.trans hk.symm) hmem
  let z := T.lateral (finRotate D.length (finRotate D.length j))
  have hzC := (T.cell_neighbors (finRotate D.length (finRotate D.length j)) z).mpr
    (Or.inr (Or.inr rfl))
  have hzP := (edge_face_iff (uniform_finitePolytope hP.1)
    (D.cell_face (finRotate D.length (finRotate D.length j))) hzC.1.1 hzC.2.1.1).mpr hzC
  have hnK := T.paired_remaining_normal hP hG (by omega) (by omega) hvG hlen j q
    (fun i => (hq i).1) (fun i => (hq i).2.1)
    (hother _ hparams.1) (hother _ hparams.2)
  have hGt := T.paired_remaining_polygon_translate hP hG (by omega) (by omega) hvG hlen j q
    (fun i => (hq i).1) (fun i => (hq i).2.1)
    (hother _ hparams.1) (hother _ hparams.2)
  have hHt := U.paired_remaining_polygon_translate hP hH (by omega) (by omega) hvH hlenA k r
    (fun i => (hr i).1) (fun i => (hr i).2.1)
    (hotherA _ hparamsA.1) (hotherA _ hparamsA.2)
  refine ⟨?_, z, hzP, hj ▸ hnK, hGt, ?_, ?_⟩
  · simpa only [hj, hqm] using (hq j).2.1
  · simpa only [← heq] using hHt
  · intro w hw
    simpa only [hj] using T.paired_three_neighbor_coverage classification3D classification4D
      N S hLIB hS1 hB2 hP hG hn hvG hH hvH A U hcover hlen hlenA j k
      (hj.trans hk.symm) hGedges.1 hGedges.2.1 hw

end Uniform5.Composition
