import Uniform5.CompositionTransverseCells

/-! A four-face centroid lies strictly between its two incident cell rays.
The whole uniform four-polytope is allowed as the four-face. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical InnerProductGeometry
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- When both points belong to the polytope, positive radial scaling
preserves membership in any actual face through the origin. -/
theorem radialPoint_mem_face_iff_of_pos {P F : Set E} (hF : IsConvexFace P F)
    (hz : (0 : E) ∈ F) (L : E →L[ℝ] ℝ) {x : E} (hx : x ∈ P)
    (hp : 0 < L x) (hr : radialPoint L x ∈ P) :
    radialPoint L x ∈ F ↔ x ∈ F := by
  by_cases hh : 1 ≤ L x
  · exact radialPoint_mem_face_iff hF hz L hx hh
  · have h := smul_mem_face_iff hF hz hr hp (le_of_not_ge hh)
    simpa only [radialPoint, smul_smul, mul_inv_cancel₀ hp.ne', one_smul] using h.symm

noncomputable local instance (G : Set E) : DecidableEq (affineSpan ℝ G).directionᗮ := Classical.decEq _

/-- Two different actual three-cells inside a four-face and above the
same two-face give precisely the two endpoints of the four-face's link. -/
theorem transverse_fourFace_twoCells_segment {P G F C₁ C₂ : Set E}
    (hP : FinitePolytope P) (hG : IsConvexFace P G) (hdG : affineDimension G = 2)
    {c : E} (hc : c ∈ G) (hF : IsConvexFace P F) (hdF : affineDimension F = 4)
    (hC₁ : IsConvexFace P C₁) (hC₂ : IsConvexFace P C₂)
    (hGC₁ : G ⊆ C₁) (hGC₂ : G ⊆ C₂) (hC₁F : C₁ ⊆ F) (hC₂F : C₂ ⊆ F)
    (hdC₁ : affineDimension C₁ = 3) (hdC₂ : affineDimension C₂ = 3) (hne : C₁ ≠ C₂) :
    ∃ v₁ v₂ : (affineSpan ℝ G).directionᗮ, v₁ ≠ v₂ ∧
      transverseProjection G c '' C₁ ∩ transverseLink hP hG hc = {v₁} ∧
      transverseProjection G c '' C₂ ∩ transverseLink hP hG hc = {v₂} ∧
      transverseProjection G c '' F ∩ transverseLink hP hG hc = segment ℝ v₁ v₂ := by
  let S := transverseLink hP hG hc
  have hGF : G ⊆ F := hGC₁.trans hC₁F
  obtain ⟨v₁, hv₁, hs₁⟩ := transverseLink_cell_vertex hP hG hdG hc hC₁ hGC₁ hdC₁
  obtain ⟨v₂, hv₂, hs₂⟩ := transverseLink_cell_vertex hP hG hdG hc hC₂ hGC₂ hdC₂
  have hvne : v₁ ≠ v₂ := by
    intro heq
    obtain ⟨C, hC, huniq⟩ := transverseLink_vertex_unique_cell hP hG hdG hc hv₁
    apply hne
    exact (huniq C₁ ⟨hC₁, hGC₁, hdC₁, hs₁⟩).trans
      (huniq C₂ ⟨hC₂, hGC₂, hdC₂, by simpa only [heq] using hs₂⟩).symm
  let F' : {H : GeometricFace P // G ⊆ H.val} := ⟨⟨F, hF⟩, hGF⟩
  let A := (transverseLinkFaceEquiv hP hG hc F').val
  have hAF : IsConvexFace S A := (transverseLinkFaceEquiv hP hG hc F').property
  have hA : A = transverseProjection G c '' F ∩ S := transverseLinkFaceEquiv_apply hP hG hc F'
  have hFne : F ≠ G := by intro h; have hd := congrArg affineDimension h; omega
  have hdA := transverseLinkFaceEquiv_dimension hP hG hc F' hFne
  have hdA' : affineDimension A = 1 := by
    change affineDimension A + affineDimension G + 1 = affineDimension F at hdA
    omega
  have hdle : affineDimension F ≤ affineDimension P :=
    Submodule.finrank_mono (AffineSubspace.direction_le (affineSpan_mono ℝ hF.2.1))
  have hS : FinitePolytope S := (transverseLink_finite_dimension hP hG hc (by omega)).1
  have hvA (C : Set E) (hCF : C ⊆ F) (v : (affineSpan ℝ G).directionᗮ)
      (hs : transverseProjection G c '' C ∩ S = {v}) : v ∈ A := by
    have hm : v ∈ transverseProjection G c '' C ∩ S := hs.symm ▸ mem_singleton v
    rw [hA]
    exact ⟨image_mono hCF hm.1, hm.2⟩
  have hv₁A := hvA C₁ hC₁F v₁ hs₁
  have hv₂A := hvA C₂ hC₂F v₂ hs₂
  obtain ⟨a, b, hab, hseg, hext⟩ := finitePolytope_dim_one_segment
    (finitePolytope_face hS hAF ⟨v₁, hv₁A⟩) hdA'
  have he₁ : v₁ ∈ ({a, b} : Set _) := by
    rw [← hext, hAF.2.extremePoints_eq]
    exact ⟨hv₁A, hv₁⟩
  have he₂ : v₂ ∈ ({a, b} : Set _) := by
    rw [← hext, hAF.2.extremePoints_eq]
    exact ⟨hv₂A, hv₂⟩
  refine ⟨v₁, v₂, hvne, hs₁, hs₂, ?_⟩
  rw [← hA, hseg]
  simp only [mem_insert_iff, mem_singleton_iff] at he₁ he₂
  rcases he₁ with rfl | rfl <;> rcases he₂ with rfl | rfl
  · exact False.elim (hvne rfl)
  · rfl
  · exact segment_symm ℝ _ _
  · exact False.elim (hvne rfl)

/-- Normalizing the centroid of a nontrivial incident face lands in that
face's literal projected section. -/
theorem transverse_face_centroid_section {P G F : Set E} (hP : FinitePolytope P)
    (hG : IsConvexFace P G) {c : E} (hc : c ∈ G)
    (hF : IsConvexFace P F) (hGF : G ⊆ F) (hne : G ≠ F) :
    let a := vertexCentroid (vertices F (finitePolytope_face hP hF ⟨c, hGF hc⟩))
    radialPoint (transverseCutHeight hP hG hc) (transverseProjection G c a) ∈
      transverseProjection G c '' F ∩ transverseLink hP hG hc := by
  dsimp only
  let hFP := finitePolytope_face hP hF ⟨c, hGF hc⟩
  let a := vertexCentroid (vertices F hFP)
  let L := transverseCutHeight hP hG hc
  let Q := transverseProjection G c '' P
  let hQ := finitePolytope_transverse hP G c
  have hp := transverse_face_centroid_height_pos hP hG hc hF hGF hne
  have ha : a ∈ F := intrinsicInterior_subset (vertexCentroid_mem_intrinsicInterior hFP)
  have hx : transverseProjection G c a ∈ Q := ⟨a, hF.2.1 ha, rfl⟩
  have hr := finiteHull_radialPoint_mem_section (vertices Q hQ)
    ((mem_vertices hQ 0).mpr (transverse_origin_extreme hP hG hc)) L
    (transverseCutHeight_ge_one hP hG hc) (by simpa only [convexHull_vertices] using hx) hp
  refine ⟨?_, by simpa only [convexHull_vertices] using hr⟩
  exact radialPoint_mem_apex_face hQ (transverse_face_image hP hF hGF hc)
    ⟨c, hGF hc, transverseProjection_center G c⟩ L (transverseCutHeight_ge_one hP hG hc)
    ⟨a, ha, rfl⟩ hp

/-- The normalized centroid of a face cannot enter any proper subface's
projected cone. This supplies strictness at both edge endpoints. -/
theorem transverse_face_centroid_not_smaller {P G F C : Set E} (hP : FinitePolytope P)
    (hG : IsConvexFace P G) {c : E} (hc : c ∈ G)
    (hF : IsConvexFace P F) (hC : IsConvexFace P C) (hGC : G ⊆ C) (hCF : C ⊆ F)
    (hGFne : G ≠ F) (hCFne : C ≠ F) :
    let a := vertexCentroid (vertices F (finitePolytope_face hP hF ⟨c, hCF (hGC hc)⟩))
    radialPoint (transverseCutHeight hP hG hc) (transverseProjection G c a) ∉
      transverseProjection G c '' C := by
  dsimp only
  let hFP := finitePolytope_face hP hF ⟨c, hCF (hGC hc)⟩
  let a := vertexCentroid (vertices F hFP)
  have ha : a ∈ F := intrinsicInterior_subset (vertexCentroid_mem_intrinsicInterior hFP)
  have hp := transverse_face_centroid_height_pos hP hG hc hF (hGC.trans hCF) hGFne
  have hr := transverse_face_centroid_section hP hG hc hF (hGC.trans hCF) hGFne
  intro hmem
  have hx := (radialPoint_mem_face_iff_of_pos (transverse_face_image hP hC hGC hc)
    ⟨c, hGC hc, transverseProjection_center G c⟩ (transverseCutHeight hP hG hc)
    (show transverseProjection G c a ∈ transverseProjection G c '' P from ⟨a, hF.2.1 ha, rfl⟩)
    hp hr.2.1).mp hmem
  have haC : a ∈ C := by
    rw [← transverse_face_saturated hC hGC hc]
    exact ⟨hF.2.1 ha, hx⟩
  exact centroid_not_mem_proper_face hFP (face_restrict hC hF.2.1 hCF) hCFne haC

set_option maxHeartbeats 500000 in
/-- In transverse coordinates, a four-face centroid ray is a strictly
positive combination of its two actual three-cell centroid rays. -/
theorem projected_fourFace_centroid_positive_combination {P G F C₁ C₂ : Set E}
    (hP : FinitePolytope P) (hG : IsConvexFace P G) (hdG : affineDimension G = 2)
    {c : E} (hc : c ∈ G) (hF : IsConvexFace P F) (hdF : affineDimension F = 4)
    (hC₁ : IsConvexFace P C₁) (hC₂ : IsConvexFace P C₂)
    (hGC₁ : G ⊆ C₁) (hGC₂ : G ⊆ C₂) (hC₁F : C₁ ⊆ F) (hC₂F : C₂ ⊆ F)
    (hdC₁ : affineDimension C₁ = 3) (hdC₂ : affineDimension C₂ = 3) (hne : C₁ ≠ C₂) :
    let a := vertexCentroid (vertices F (finitePolytope_face hP hF ⟨c, hC₁F (hGC₁ hc)⟩))
    let b₁ := vertexCentroid (vertices C₁ (finitePolytope_face hP hC₁ ⟨c, hGC₁ hc⟩))
    let b₂ := vertexCentroid (vertices C₂ (finitePolytope_face hP hC₂ ⟨c, hGC₂ hc⟩))
    ∃ s t : ℝ, 0 < s ∧ 0 < t ∧
      transverseProjection G c a = s • transverseProjection G c b₁ + t • transverseProjection G c b₂ := by
  dsimp only
  let a := vertexCentroid (vertices F (finitePolytope_face hP hF ⟨c, hC₁F (hGC₁ hc)⟩))
  let b₁ := vertexCentroid (vertices C₁ (finitePolytope_face hP hC₁ ⟨c, hGC₁ hc⟩))
  let b₂ := vertexCentroid (vertices C₂ (finitePolytope_face hP hC₂ ⟨c, hGC₂ hc⟩))
  let x := transverseProjection G c a
  let x₁ := transverseProjection G c b₁
  let x₂ := transverseProjection G c b₂
  let L := transverseCutHeight hP hG hc
  obtain ⟨v₁, v₂, hvne, hs₁, hs₂, hsF⟩ := transverse_fourFace_twoCells_segment
    hP hG hdG hc hF hdF hC₁ hC₂ hGC₁ hGC₂ hC₁F hC₂F hdC₁ hdC₂ hne
  have hGFne : G ≠ F := by intro h; have hh := congrArg affineDimension h; omega
  have hC₁Fne : C₁ ≠ F := by intro h; have hh := congrArg affineDimension h; omega
  have hC₂Fne : C₂ ≠ F := by intro h; have hh := congrArg affineDimension h; omega
  have hp : 0 < L x := transverse_face_centroid_height_pos hP hG hc hF (hGC₁.trans hC₁F) hGFne
  have hr₁ : 0 < L x₁ ∧ x₁ = L x₁ • v₁ :=
    transverse_cell_centroid_ray hP hG hdG hc hC₁ hGC₁ hdC₁ hs₁
  have hr₂ : 0 < L x₂ ∧ x₂ = L x₂ • v₂ :=
    transverse_cell_centroid_ray hP hG hdG hc hC₂ hGC₂ hdC₂ hs₂
  have hqseg : radialPoint L x ∈ segment ℝ v₁ v₂ := by
    rw [← hsF]
    exact transverse_face_centroid_section hP hG hc hF (hGC₁.trans hC₁F) hGFne
  have hq₁ : radialPoint L x ≠ v₁ := by
    intro heq
    apply transverse_face_centroid_not_smaller hP hG hc hF hC₁ hGC₁ hC₁F hGFne hC₁Fne
    have hv : v₁ ∈ transverseProjection G c '' C₁ ∩ transverseLink hP hG hc :=
      hs₁.symm ▸ mem_singleton v₁
    exact heq.symm ▸ hv.1
  have hq₂ : radialPoint L x ≠ v₂ := by
    intro heq
    apply transverse_face_centroid_not_smaller hP hG hc hF hC₂ hGC₂ hC₂F hGFne hC₂Fne
    have hv : v₂ ∈ transverseProjection G c '' C₂ ∩ transverseLink hP hG hc :=
      hs₂.symm ▸ mem_singleton v₂
    exact heq.symm ▸ hv.1
  obtain ⟨s, t, hs, ht, _, hst⟩ := mem_openSegment_of_ne_left_right hq₁.symm hq₂.symm hqseg
  refine ⟨L x * s / L x₁, L x * t / L x₂, div_pos (mul_pos hp hs) hr₁.1,
    div_pos (mul_pos hp ht) hr₂.1, ?_⟩
  change x = (L x * s / L x₁) • x₁ + (L x * t / L x₂) • x₂
  calc
    x = L x • radialPoint L x := by simp only [radialPoint, smul_smul, mul_inv_cancel₀ hp.ne', one_smul]
    _ = L x • (s • v₁ + t • v₂) := by rw [hst]
    _ = (L x * s / L x₁) • x₁ + (L x * t / L x₂) • x₂ := by
      have h₁ := congrArg (fun z => (L x * s / L x₁) • z) hr₁.2
      have h₂ := congrArg (fun z => (L x * t / L x₂) • z) hr₂.2
      dsimp only at h₁ h₂
      rw [h₁, h₂]
      simp only [smul_add, smul_smul, div_mul_cancel₀ _ hr₁.1.ne', div_mul_cancel₀ _ hr₂.1.ne']

set_option maxHeartbeats 500000 in
/-- The actual four-face centroid offset lies strictly in the positive
cone of its two cell-centroid offsets at the actual two-face centroid.
The four-face may equal the ambient uniform polytope. -/
theorem uniform_fourFace_centroid_positive_combination {n : ℕ} {P G F C₁ C₂ : Set E}
    (hP : Uniform (n + 3) P) (hG : IsConvexFace P G) (hGne : G.Nonempty)
    (hdG : affineDimension G = 2) (hF : IsConvexFace P F) (hdF : affineDimension F = 4)
    (hC₁ : IsConvexFace P C₁) (hC₂ : IsConvexFace P C₂)
    (hGC₁ : G ⊆ C₁) (hGC₂ : G ⊆ C₂) (hC₁F : C₁ ⊆ F) (hC₂F : C₂ ⊆ F)
    (hdC₁ : affineDimension C₁ = 3) (hdC₂ : affineDimension C₂ = 3) (hne : C₁ ≠ C₂) :
    let hPP := uniform_finitePolytope hP
    let f := vertexCentroid (vertices G (finitePolytope_face hPP hG hGne))
    let a := vertexCentroid (vertices F (finitePolytope_face hPP hF (hGne.mono (hGC₁.trans hC₁F))))
    let b₁ := vertexCentroid (vertices C₁ (finitePolytope_face hPP hC₁ (hGne.mono hGC₁)))
    let b₂ := vertexCentroid (vertices C₂ (finitePolytope_face hPP hC₂ (hGne.mono hGC₂)))
    ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ a - f = s • (b₁ - f) + t • (b₂ - f) := by
  dsimp only
  let hPP := uniform_finitePolytope hP
  let f := vertexCentroid (vertices G (finitePolytope_face hPP hG hGne))
  let a := vertexCentroid (vertices F (finitePolytope_face hPP hF (hGne.mono (hGC₁.trans hC₁F))))
  let b₁ := vertexCentroid (vertices C₁ (finitePolytope_face hPP hC₁ (hGne.mono hGC₁)))
  let b₂ := vertexCentroid (vertices C₂ (finitePolytope_face hPP hC₂ (hGne.mono hGC₂)))
  have hf : f ∈ G := intrinsicInterior_subset (vertexCentroid_mem_intrinsicInterior
    (finitePolytope_face hPP hG hGne))
  obtain ⟨s, t, hs, ht, heq⟩ := projected_fourFace_centroid_positive_combination hPP hG hdG
    hf hF hdF hC₁ hC₂ hGC₁ hGC₂ hC₁F hC₂F hdC₁ hdC₂ hne
  have haorth : a - f ∈ (affineSpan ℝ G).directionᗮ :=
    (uniform_nested_face_rays_mem_orthogonal hP hF hG hGne (hGC₁.trans hC₁F)).2
  have hb₁orth : b₁ - f ∈ (affineSpan ℝ G).directionᗮ :=
    (uniform_nested_face_rays_mem_orthogonal hP hC₁ hG hGne hGC₁).2
  have hb₂orth : b₂ - f ∈ (affineSpan ℝ G).directionᗮ :=
    (uniform_nested_face_rays_mem_orthogonal hP hC₂ hG hGne hGC₂).2
  have hproj (x : E) (hx : x - f ∈ (affineSpan ℝ G).directionᗮ) :
      (transverseProjection G f x : E) = x - f := by
    rw [transverseProjection_apply]
    exact congrArg Subtype.val (Submodule.orthogonalProjection_mem_subspace_eq_self
      (⟨x - f, hx⟩ : (affineSpan ℝ G).directionᗮ))
  refine ⟨s, t, hs, ht, ?_⟩
  have hh := congrArg (fun z : (affineSpan ℝ G).directionᗮ => (z : E)) heq
  change (transverseProjection G f a : E) =
    s • (transverseProjection G f b₁ : E) + t • (transverseProjection G f b₂ : E) at hh
  rw [hproj a haorth, hproj b₁ hb₁orth, hproj b₂ hb₂orth] at hh
  exact hh

end Uniform5.Composition
