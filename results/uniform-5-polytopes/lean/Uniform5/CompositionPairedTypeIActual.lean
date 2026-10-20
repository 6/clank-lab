import Uniform5.CompositionPairedTypeIFour

/-! The actual Type I / Type I paired branch has two three-slot fans,
and the two parameters away from the shared duoprism are exactly four. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem unitUniform5_paired_typeI_three_and_parameters
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
    D.length = 3 ∧ ∃ (q : Fin D.length → ℕ) (j : Fin D.length),
      (∀ i, 3 ≤ q i ∧ Congruent (D.facet i) (duoprismModel n (q i)) ∧
        Congruent (D.cell i) (polygonPrismModel n)) ∧
      D.facet j = K ∧ q j = m ∧ ∀ i, i ≠ j → q i = 4 := by
  obtain ⟨_, q, hq, hangle⟩ := hI
  obtain ⟨_, r, hr, _⟩ := hJ
  obtain ⟨T⟩ := D.typeI_fan_chart hP hG (by omega) (by omega) hvG q
    (fun i => (hq i).1) (fun i => (hq i).2.1)
  obtain ⟨U⟩ := A.typeI_fan_chart hP hH (by omega) (by omega) hvH r
    (fun i => (hr i).1) (fun i => (hr i).2.1)
  obtain ⟨j, hj⟩ := (D.facet_coverage K).mp ⟨hK, hGK⟩
  have hHK' : H ⊆ D.facet j := hj.symm ▸ hHK
  obtain ⟨hcH, hdH, hqm⟩ := T.common_facet_partner_edges hP hG hn hvG hH hm hvH hGH q
    (fun i => (hq i).1) (fun i => (hq i).2.1) j hHK'
  have hlen : D.length = 3 := by
    rcases paired_angle_cycle_length D.length_ge q (fun i => (hq i).1) j
      (hqm.symm ▸ hm) hangle with h3 | h4
    · exact h3
    · exact (T.paired_k4_typeI_partner_impossible classification3D classification4D
        N S hLIB hS1 hB2 hP hG hn hvG hH hm hvH hGH A U hcover h4 j hHK'
        q (fun i => (hq i).1) (fun i => (hq i).2.1) hangle
        r (fun i => (hr i).1) (fun i => (hr i).2.1)).elim
  have hparams := T.paired_k3_typeI_partner_parameters classification3D classification4D
    N S hLIB hS1 hB2 hP hG hn hvG hH hm hvH A U hcover hlen j hcH hdH
    q (fun i => (hq i).1) (fun i => (hq i).2.1)
    r (fun i => (hr i).1) (fun i => (hr i).2.1)
  refine ⟨hlen, q, j, hq, hj, hqm, ?_⟩
  intro i hij
  rcases finRotate_three_enumeration hlen j i with he | rfl | rfl
  · exact (hij he).elim
  · exact hparams.1
  · exact hparams.2

end Uniform5.Composition
