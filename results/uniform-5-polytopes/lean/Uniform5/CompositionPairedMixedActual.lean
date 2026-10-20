import Uniform5.CompositionPairedMixedThree

/-! The actual mixed Type I / Type II branch has a four-slot Type I
cycle, with all three nonshared duoprism parameters equal to three. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem unitUniform5_paired_mixed_four_and_parameters
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    {P G H K : Set (Space 5)} (hP : UnitUniform 5 P) {n m : ℕ}
    (hG : PolygonFace P G n) (hn : 17 ≤ n) (hH : PolygonFace P H m) (hm : 17 ≤ m)
    {v : Space 5} (hvG : v ∈ G.extremePoints ℝ) (hvH : v ∈ H.extremePoints ℝ)
    (hGH : G ≠ H) (hcover : TwoLargeFacesCoverAt P v G H)
    (hK : Facet P K) (hGK : G ⊆ K) (hHK : H ⊆ K)
    (D : ActualPolygonCycle P G) (A : ActualPolygonCycle P H)
    (hI : D.CaseBTypeI n) (hII : A.CaseBTypeII m) :
    D.length = 4 ∧ ∃ (q : Fin D.length → ℕ) (j : Fin D.length),
      (∀ i, 3 ≤ q i ∧ Congruent (D.facet i) (duoprismModel n (q i)) ∧
        Congruent (D.cell i) (polygonPrismModel n)) ∧
      D.facet j = K ∧ q j = m ∧ ∀ i, i ≠ j → q i = 3 := by
  obtain ⟨_, q, hq, hangle⟩ := hI
  obtain ⟨T⟩ := D.typeI_fan_chart hP hG (by omega) (by omega) hvG q
    (fun i => (hq i).1) (fun i => (hq i).2.1)
  obtain ⟨U⟩ := A.typeII_actual_fan hP hH hm hvH hII
  obtain ⟨j, hj⟩ := (D.facet_coverage K).mp ⟨hK, hGK⟩
  have hHK' : H ⊆ D.facet j := hj.symm ▸ hHK
  obtain ⟨_, _, hqm⟩ := T.common_facet_partner_edges hP hG hn hvG hH hm hvH hGH q
    (fun i => (hq i).1) (fun i => (hq i).2.1) j hHK'
  have hlen : D.length = 4 := by
    rcases paired_angle_cycle_length D.length_ge q (fun i => (hq i).1) j
      (hqm.symm ▸ hm) hangle with h3 | h4
    · exact (T.paired_k3_typeII_partner_impossible classification3D classification4D
        N S hLIB hS1 hB2 hP hG hn hvG hH hm hvH hGH A U hcover h3 j hHK'
        q (fun i => (hq i).1) (fun i => (hq i).2.1)).elim
    · exact h4
  refine ⟨hlen, q, j, hq, hj, hqm, ?_⟩
  exact paired_four_small_parameters hlen q (fun i => (hq i).1) j (hqm.symm ▸ hm) hangle

end Uniform5.Composition
