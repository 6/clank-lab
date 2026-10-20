import Uniform5.CompositionUniqueAntiprismCells
import Uniform5.CompositionUniqueModelCells
import Uniform5.CompositionTwoFanCover

/-! In a mixed pair only the Type II polygon can belong to an antiprism
cell. This identifies every congruent cell through the root geometrically. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem unitUniform5_mixed_antiprism_model_unique
    (classification4D : CitedClassification4D)
    {P G H C F : Set (Space 5)} (hP : UnitUniform 5 P) {n m : ℕ}
    (hG : PolygonFace P G n) (hH : PolygonFace P H m) (hm : 17 ≤ m)
    {v : Space 5} (hvG : v ∈ G.extremePoints ℝ)
    (hcover : TwoLargeFacesCoverAt P v G H)
    (D : ActualPolygonCycle P G) (hI : D.CaseBTypeI n)
    (hC : IsConvexFace P C) (hHC : H ⊆ C) (hdC : affineDimension C = 3)
    (hCA : Congruent C (antiprismModel m))
    (hF : IsConvexFace P F) (hvF : v ∈ F) (hFC : Congruent F C) : F = C := by
  have hv := hG.1.2.extremePoints_subset_extremePoints hvG
  have hdF : affineDimension F = 3 := by
    obtain ⟨g, hg⟩ := (congruent_iff_affineIsometryEquiv_image _ _).mp hFC
    rw [← hg, affineDimension_image] at hdC
    exact hdC
  have hFA := congruent_trans hFC hCA
  have hvF' : v ∈ F.extremePoints ℝ := by
    rw [face_extremePoints_eq hF]
    exact ⟨hvF, hv⟩
  obtain ⟨J, hJ, hJF, hvJ⟩ := antiprism_cell_polygon_through_vertex hP hF hdF
    (by omega : 3 ≤ m) hFA hvF'
  rcases hcover J m hJ hm hvJ with hJG | hJH
  · subst J
    have hnm : n = m := (polygonFace_extremePoints_ncard hG).symm.trans
      (polygonFace_extremePoints_ncard hJ)
    subst m
    obtain ⟨i, hi, hFi⟩ := D.cell_coverage F hF hJF hdF
    obtain ⟨_, q, hq, _⟩ := hI
    have hp : Congruent F (polygonPrismModel n) := by
      simpa only [← hFi] using (hq (⟨i, hi⟩ : Fin D.length)).2.2
    have hFU : UnitUniform 3 F := by
      have hh := unitUniform_all_faces hP hF ⟨v, hvF⟩
      rwa [hdF] at hh
    exact (unitUniform3_prism_antiprism_disjoint (by omega) hFU hp hFA).elim
  · subst J
    exact unitUniform5_antiprism_cell_unique classification4D hP hH hm hF hC hJF hHC
      hdF hdC hFA hCA

end Uniform5.Composition
