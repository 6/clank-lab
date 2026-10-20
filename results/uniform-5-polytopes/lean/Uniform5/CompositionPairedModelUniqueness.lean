import Uniform5.CompositionPairedFacetUniqueness
import Uniform5.CompositionDuoprismFactorPair
import Uniform5.CompositionUniqueModelCells
import Uniform5.CompositionTwoFanCover

/-! The two actual large factor polygons identify every duoprism model
face through the root, including the equal-parameter case. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem unitUniform5_paired_duoprism_model_unique
    {P G H K F : Set (Space 5)} (hP : UnitUniform 5 P) {n m : ℕ}
    (hG : PolygonFace P G n) (hn : 17 ≤ n) (hH : PolygonFace P H m) (hm : 17 ≤ m)
    {v : Space 5} (hvG : v ∈ G.extremePoints ℝ) (hvH : v ∈ H.extremePoints ℝ)
    (hGH : G ≠ H) (hcover : TwoLargeFacesCoverAt P v G H)
    (D : ActualPolygonCycle P G) (hI : D.CaseBTypeI n)
    (hK : Facet P K) (hGK : G ⊆ K) (hHK : H ⊆ K)
    (hmodel : Congruent K (duoprismModel n m))
    (hF : IsConvexFace P F) (hvF : v ∈ F) (hFK : Congruent F K) : F = K := by
  have hv := hG.1.2.extremePoints_subset_extremePoints hvG
  have hdK : affineDimension K = 4 := by
    have hh := hK.2.2
    rw [uniform_dimension hP.1] at hh
    omega
  have hdF : affineDimension F = 4 := by
    obtain ⟨g, hg⟩ := (congruent_iff_affineIsometryEquiv_image _ _).mp hFK
    rw [← hg, affineDimension_image] at hdK
    exact hdK
  have hFfacet : Facet P F := ⟨hF, ⟨v, hvF⟩, by rw [hdF, uniform_dimension hP.1]⟩
  have hvF' : v ∈ F.extremePoints ℝ := by
    rw [face_extremePoints_eq hF]
    exact ⟨hvF, hv⟩
  obtain ⟨A, B, hA, hB, hAF, hBF, hvA, hvB, hAB⟩ :=
    unitUniform5_duoprism_factor_pair_at_vertex hP hFfacet (by omega) (by omega)
      (congruent_trans hFK hmodel) hvF'
  have ha := hcover A n hA hn hvA
  have hb := hcover B m hB hm hvB
  have hh : G ⊆ F ∧ H ⊆ F := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hAB rfl).elim
    · exact ⟨hAF, hBF⟩
    · exact ⟨hBF, hAF⟩
    · exact (hAB rfl).elim
  exact (unitUniform5_paired_typeI_common_facet_unique hP hG hn hH hm hvG hvH
    hGH D hI hK hGK hHK hFfacet hh.1 hh.2).symm

end Uniform5.Composition
