import Uniform5.CompositionPairedTypeITranslations

/-! The actual symmetry orbit supplies a common duoprism facet through
the two translated large polygons at the remaining root neighbor. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem unitUniform5_paired_translated_polygons_common_facet
    {P G H K : Set (Space 5)} (hP : UnitUniform 5 P) {n m : ℕ}
    (hn : 17 ≤ n) (hm : 17 ≤ m)
    {v z : Space 5} (hv : v ∈ P.extremePoints ℝ) (hz : z ∈ P.extremePoints ℝ)
    (hvG : v ∈ G) (hvH : v ∈ H)
    (hcover : TwoLargeFacesCoverAt P v G H)
    (hK : Facet P K) (hGK : G ⊆ K) (hHK : H ⊆ K)
    (hmodel : Congruent K (duoprismModel n m))
    (hG' : PolygonFace P (CaseB.translate G (z - v)) n)
    (hH' : PolygonFace P (CaseB.translate H (z - v)) m) :
    ∃ F, Facet P F ∧ Congruent F (duoprismModel n m) ∧ z ∈ F ∧
      CaseB.translate G (z - v) ⊆ F ∧ CaseB.translate H (z - v) ⊆ F := by
  obtain ⟨g, hg, hgv⟩ := uniform_vertexTransitive hP.1 v hv z hz
  have hcoverz := hcover.image g
  rw [hg, hgv] at hcoverz
  have hmem (C : Set (Space 5)) (hvC : v ∈ C) : z ∈ CaseB.translate C (z - v) :=
    ⟨v, hvC, by dsimp; abel⟩
  have hzG' : z ∈ (CaseB.translate G (z - v)).extremePoints ℝ := by
    rw [face_extremePoints_eq hG'.1]
    exact ⟨hmem G hvG, hz⟩
  have hzH' : z ∈ (CaseB.translate H (z - v)).extremePoints ℝ := by
    rw [face_extremePoints_eq hH'.1]
    exact ⟨hmem H hvH, hz⟩
  have hsub (C : Set (Space 5)) (hc : C = g '' G ∨ C = g '' H) : C ⊆ g '' K := by
    rcases hc with rfl | rfl
    · exact image_mono hGK
    · exact image_mono hHK
  refine ⟨g '' K, ?_, congruent_trans
    (congruent_symm (congruent_affineIsometryEquiv_image g K)) hmodel,
    ⟨v, hGK hvG, hgv⟩,
    hsub _ (hcoverz _ n hG' hn hzG'), hsub _ (hcoverz _ m hH' hm hzH')⟩
  simpa only [AffineIsometryEquiv.coe_toAffineIsometry, hg] using
    embedding_facet_image g.toAffineIsometry hK

end Uniform5.Composition
