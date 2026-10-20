import Uniform5.CompositionPairedTypeIRootTransport
import Uniform5.CompositionPairedModelUniqueness
import Uniform5.CompositionDuoprismFactorSum

/-! The actual paired Type I / Type I branch is a prism. Whole translated
factor polygons determine the translated duoprism, and root uniqueness
propagates this partition along the actual parent edge graph. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem unitUniform5_paired_typeI_mem_K2
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    {P G H K : Set (Space 5)} (hP : UnitUniform 5 P) {n m : ℕ}
    (hG : PolygonFace P G n) (hn : 17 ≤ n) (hH : PolygonFace P H m) (hm : 17 ≤ m)
    {v : Space 5} (hvG : v ∈ G.extremePoints ℝ) (hvH : v ∈ H.extremePoints ℝ)
    (hGH : G ≠ H) (hcover : TwoLargeFacesCoverAt P v G H)
    (hK : Facet P K) (hGK : G ⊆ K) (hHK : H ⊆ K)
    (D : ActualPolygonCycle P G) (A : ActualPolygonCycle P H)
    (hI : D.CaseBTypeI n) (hJ : A.CaseBTypeI m) : K2 P := by
  obtain ⟨hmodel, z, hz, hnormal, hG', hH', hneighbors⟩ :=
    unitUniform5_paired_typeI_root_transport classification3D classification4D
      N S hLIB hS1 hB2 hP hG hn hH hm hvG hvH hGH hcover hK hGK hHK D A hI hJ
  have hv := hG.1.2.extremePoints_subset_extremePoints hvG
  have hvK := hGK hvG.1
  have hdK : affineDimension K = 4 := by
    have hh := hK.2.2
    rw [uniform_dimension hP.1] at hh
    omega
  have hsum := unitUniform4_duoprism_eq_rootedFaceSum (unitUniform_facet hP hK)
    (by omega : 3 ≤ n) (by omega : 3 ≤ m) hmodel
    ⟨face_restrict hG.1 hK.1.2.1 hGK, hG.2⟩ (by omega : n ≠ 4)
    ⟨face_restrict hH.1 hK.1.2.1 hHK, hH.2⟩ (by omega : m ≠ 4) hvG.1 hvH.1 hGH
  obtain ⟨F, hF, hFM, hzF, hGF, hHF⟩ :=
    unitUniform5_paired_translated_polygons_common_facet hP hn hm hv hz.2.1
      hvG.1 hvH.1 hcover hK hGK hHK hmodel hG' hH'
  have hne' : CaseB.translate G (z - v) ≠ CaseB.translate H (z - v) := by
    intro he
    apply hGH
    exact (Set.image_injective.mpr (show Function.Injective (fun x : Space 5 => x + (z - v))
      from fun _ _ hh => add_right_cancel hh)) he
  have hzG : z ∈ CaseB.translate G (z - v) := ⟨v, hvG.1, by dsimp; abel⟩
  have hzH : z ∈ CaseB.translate H (z - v) := ⟨v, hvH.1, by dsimp; abel⟩
  have hsumF := unitUniform4_duoprism_eq_rootedFaceSum (unitUniform_facet hP hF)
    (by omega : 3 ≤ n) (by omega : 3 ≤ m) hFM
    ⟨face_restrict hG'.1 hF.1.2.1 hGF, hG'.2⟩ (by omega : n ≠ 4)
    ⟨face_restrict hH'.1 hF.1.2.1 hHF, hH'.2⟩ (by omega : m ≠ 4) hzG hzH hne'
  have htranslate : F = CaseB.translate K (z - v) := by
    calc
      F = rootedFaceSum (CaseB.translate G (z - v)) (CaseB.translate H (z - v))
          (v + (z - v)) := by simpa only [add_sub_cancel_left, add_sub_cancel_right, add_sub_cancel] using hsumF
      _ = CaseB.translate (rootedFaceSum G H v) (z - v) := rootedFaceSum_translate G H v _
      _ = CaseB.translate K (z - v) := congrArg (fun C => CaseB.translate C (z - v)) hsum.symm
  apply unitUniform5_mem_K2_of_unique_root_cell hP hK.1 hdK hv hvK
  · intro F hF hvF hFK
    exact unitUniform5_paired_duoprism_model_unique hP hG hn hH hm hvG hvH hGH hcover
      D hI hK hGK hHK hmodel hF hvF hFK
  · intro w hw
    rcases hneighbors w hw with hwK | hwz
    · exact ⟨0, (CaseB.normals K).zero_mem, by simpa using hK.1,
        by simpa using congruent_refl K, by simpa using hwK⟩
    · subst w
      refine ⟨z - v, hnormal, htranslate ▸ hF.1, ?_, htranslate ▸ hzF⟩
      rw [← htranslate]
      exact congruent_trans hFM (congruent_symm hmodel)

end Uniform5.Composition
