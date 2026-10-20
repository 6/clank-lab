import Uniform5.CompositionFacetContainment

/-! Distinct actual faces immediately above a common face cannot share
any point outside that face. This supplies distinct lateral vertices
without a diagram or a coordinate-identification assumption. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem faces_eq_of_common_point_above_face {P G C D : Set E}
    (hG : IsConvexFace P G) (hC : IsConvexFace P C) (hD : IsConvexFace P D)
    (hne : G.Nonempty) (hGC : G ⊆ C) (hGD : G ⊆ D)
    (hdC : affineDimension C = affineDimension G + 1)
    (hdD : affineDimension D = affineDimension G + 1)
    {z : E} (hzC : z ∈ C) (hzD : z ∈ D) (hzG : z ∉ G) : C = D := by
  have hGI : G ⊆ C ∩ D := fun x hx => ⟨hGC hx, hGD hx⟩
  have hI : IsConvexFace P (C ∩ D) := ⟨hC.1.inter hD.1, hC.2.inter hD.2⟩
  have hGIf : IsConvexFace (C ∩ D) G :=
    ⟨hG.1, hG.2.mono hI.2.1 hGI⟩
  have hstrict : affineDimension G < affineDimension (C ∩ D) :=
    face_affineDimension_lt hGIf hne (by
      intro heq
      exact hzG (heq.symm ▸ show z ∈ C ∩ D from ⟨hzC, hzD⟩))
  have hIC : C ∩ D = C := by
    by_contra hh
    have h := face_affineDimension_lt
      (show IsConvexFace C (C ∩ D) from ⟨hI.1, hI.2.mono hC.2.1 inter_subset_left⟩)
      (hne.mono hGI) hh
    omega
  have hID : C ∩ D = D := by
    by_contra hh
    have h := face_affineDimension_lt
      (show IsConvexFace D (C ∩ D) from ⟨hI.1, hI.2.mono hD.2.1 inter_subset_right⟩)
      (hne.mono hGI) hh
    omega
  exact hIC.symm.trans hID

/-- Three-faces through the same polygon have distinct lateral points
unless the three-faces themselves coincide. -/
theorem three_faces_eq_of_common_point {P G C D : Set E}
    (hG : IsConvexFace P G) (hC : IsConvexFace P C) (hD : IsConvexFace P D)
    (hne : G.Nonempty) (hGC : G ⊆ C) (hGD : G ⊆ D)
    (hdG : affineDimension G = 2) (hdC : affineDimension C = 3)
    (hdD : affineDimension D = 3) {z : E}
    (hzC : z ∈ C) (hzD : z ∈ D) (hzG : z ∉ G) : C = D :=
  faces_eq_of_common_point_above_face hG hC hD hne hGC hGD
    (by omega) (by omega) hzC hzD hzG

theorem three_faces_eq_of_common_point_outside_span {P G C D : Set E}
    (hG : IsConvexFace P G) (hC : IsConvexFace P C) (hD : IsConvexFace P D)
    (hne : G.Nonempty) (hGC : G ⊆ C) (hGD : G ⊆ D)
    (hdG : affineDimension G = 2) (hdC : affineDimension C = 3)
    (hdD : affineDimension D = 3) {z : E}
    (hzC : z ∈ C) (hzD : z ∈ D) (hzG : z ∉ affineSpan ℝ G) : C = D :=
  three_faces_eq_of_common_point hG hC hD hne hGC hGD hdG hdC hdD hzC hzD
    (fun hz => hzG (subset_affineSpan ℝ G hz))

end Uniform5.Composition
