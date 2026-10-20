import Uniform5.CompositionExposedFaces

/-! Every nonempty proper geometric face is contained in a codimension-one facet. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Nonempty proper faces have strictly smaller affine dimension. -/
theorem face_affineDimension_lt [FiniteDimensional ℝ E] {P F : Set E}
    (hF : IsConvexFace P F) (hne : F.Nonempty) (hproper : F ≠ P) :
    affineDimension F < affineDimension P := by
  have hle := affineSpan_mono ℝ hF.2.1
  have hlt : affineSpan ℝ F < affineSpan ℝ P := lt_of_le_of_ne hle (by
    intro heq
    apply hproper
    rw [← face_affineSpan_inter hF hne, heq]
    exact Set.inter_eq_left.mpr (subset_affineSpan ℝ P))
  exact Submodule.finrank_lt_finrank_of_lt
    (AffineSubspace.direction_lt_of_nonempty hlt
      (hne.mono (subset_affineSpan ℝ F)))

/-- A supporting level hyperplane cuts out an exposed set. -/
theorem support_level_isExposed {P : Set E} (L : E →L[ℝ] ℝ) (c : E)
    (hc : c ∈ P) (hbound : ∀ x ∈ P, L x ≤ L c) :
    IsExposed ℝ P {x ∈ P | L x = L c} := by
  intro _
  refine ⟨L, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, heq⟩
    exact ⟨hx, fun y hy => (hbound y hy).trans_eq heq.symm⟩
  · rintro ⟨hx, hmax⟩
    exact ⟨hx, le_antisymm (hbound x hx) (hmax c hc)⟩

/-- If a nonempty face has codimension at least two, it lies strictly
inside another proper geometric face. The supporting hyperplane is tilted
until the first additional vertex reaches it. -/
theorem face_enlarge_of_dimension_gap [FiniteDimensional ℝ E]
    {P F : Set E} (hP : FinitePolytope P) (hF : IsConvexFace P F)
    (hne : F.Nonempty) (hgap : affineDimension F + 1 < affineDimension P) :
    ∃ G, IsConvexFace P G ∧ F ⊂ G ∧ G ≠ P := by
  classical
  obtain ⟨c, hc⟩ := hne
  let V := vertices P hP
  have hV : convexHull ℝ (V : Set E) = P := convexHull_vertices hP
  have hVP : (V : Set E) ⊆ P := fun x hx => ((mem_vertices hP x).mp hx).1
  have hproper : F ≠ P := by intro heq; rw [heq] at hgap; omega
  have hout : ∃ x ∈ V, x ∉ F := by
    by_contra hh
    push_neg at hh
    have hPF : P ⊆ F := by rw [← hV]; exact convexHull_min hh hF.1
    exact hproper (hF.2.1.antisymm hPF)
  obtain ⟨x, hxV, hxF⟩ := hout
  let A := affineSpan ℝ (insert x F)
  have hcA : c ∈ A := subset_affineSpan ℝ (insert x F) (Set.mem_insert_of_mem x hc)
  have hxA : x ∈ A := subset_affineSpan ℝ (insert x F) (Set.mem_insert x F)
  have hAdim : Module.finrank ℝ A.direction ≤ affineDimension F + 1 := by
    change Module.finrank ℝ (affineSpan ℝ (insert x F)).direction ≤
      Module.finrank ℝ (affineSpan ℝ F).direction + 1
    rw [direction_affineSpan, direction_affineSpan]
    exact finrank_vectorSpan_insert_le_set ℝ F x
  have hwexists : ∃ w ∈ V, w ∉ A := by
    by_contra hh
    push_neg at hh
    have hPA : P ⊆ A := by rw [← hV]; exact convexHull_min hh A.convex
    have hspan : affineSpan ℝ P ≤ A := affineSpan_le.mpr hPA
    have hd := Submodule.finrank_mono (AffineSubspace.direction_le hspan)
    change affineDimension P ≤ Module.finrank ℝ A.direction at hd
    omega
  obtain ⟨w, hwV, hwA⟩ := hwexists
  obtain ⟨M, b, hMA, hMw⟩ := geometric_hahn_banach_closed_point
    A.convex A.closed_of_finiteDimensional hwA
  have hMc : M c < b := hMA c hcA
  have hMconstant := linear_constant_on_affine_of_bounded A M hMA hcA
  have hMx : M x = M c := hMconstant x hxA
  have hMF : ∀ z ∈ F, M z = M c := fun z hz => hMconstant z
    (subset_affineSpan ℝ (insert x F) (Set.mem_insert_of_mem x hz))
  obtain ⟨L, hL⟩ := finitePolytope_face_isExposed hP hF ⟨c, hc⟩
  have hcmax := (Set.ext_iff.mp hL c).mp hc
  have hLbound : ∀ z ∈ P, L z ≤ L c := hcmax.2
  have hLeq : ∀ z ∈ P, L z = L c ↔ z ∈ F := by
    intro z hz
    constructor
    · intro heq
      rw [hL]
      exact ⟨hz, fun y hy => (hLbound y hy).trans_eq heq.symm⟩
    · intro hzF
      have hzmax := (Set.ext_iff.mp hL z).mp hzF
      exact le_antisymm (hLbound z hz) (hzmax.2 c (hF.2.1 hc))
  let W := V.filter (fun z => M c < M z)
  have hWne : W.Nonempty := ⟨w, Finset.mem_filter.mpr ⟨hwV, hMc.trans hMw⟩⟩
  obtain ⟨z, hzW, hmin⟩ := W.exists_min_image (fun y => (L c - L y) / (M y - M c)) hWne
  have hzV := (Finset.mem_filter.mp hzW).1
  have hzM := (Finset.mem_filter.mp hzW).2
  have hzF : z ∉ F := by intro hh; rw [hMF z hh] at hzM; exact lt_irrefl _ hzM
  have hzL : L z < L c := lt_of_le_of_ne (hLbound z (hVP hzV))
    (fun heq => hzF ((hLeq z (hVP hzV)).mp heq))
  let t := (L c - L z) / (M z - M c)
  have ht : 0 < t := div_pos (sub_pos.mpr hzL) (sub_pos.mpr hzM)
  let N : E →L[ℝ] ℝ := L + t • M
  have hNboundV : ∀ y ∈ V, N y ≤ N c := by
    intro y hy
    have hyL := hLbound y (hVP hy)
    change L y + t * M y ≤ L c + t * M c
    by_cases hyM : M c < M y
    · have hh := hmin y (Finset.mem_filter.mpr ⟨hy, hyM⟩)
      have hh' : t * (M y - M c) ≤ L c - L y :=
        (le_div_iff₀ (sub_pos.mpr hyM)).mp hh
      nlinarith
    · have hh := mul_nonpos_of_nonneg_of_nonpos ht.le (sub_nonpos.mpr (le_of_not_gt hyM))
      nlinarith
  have hNbound : ∀ y ∈ P, N y ≤ N c := by
    rw [← hV]
    exact convexHull_min hNboundV (convex_halfSpace_le N.toLinearMap.isLinear (N c))
  let G : Set E := {y ∈ P | N y = N c}
  have hGexp : IsExposed ℝ P G := support_level_isExposed N c (hF.2.1 hc) hNbound
  have hGface : IsConvexFace P G :=
    ⟨(finitePolytope_convex hP).inter
      ((convex_singleton (N c)).linear_preimage N.toLinearMap), hGexp.isExtreme⟩
  have hFG : F ⊆ G := by
    intro y hy
    refine ⟨hF.2.1 hy, ?_⟩
    change L y + t * M y = L c + t * M c
    rw [(hLeq y (hF.2.1 hy)).mpr hy, hMF y hy]
  have hzG : z ∈ G := by
    refine ⟨hVP hzV, ?_⟩
    change L z + t * M z = L c + t * M c
    have hh : t * (M z - M c) = L c - L z := div_mul_cancel₀ _ (sub_pos.mpr hzM).ne'
    nlinarith
  have hxG : x ∉ G := by
    rintro ⟨_, hh⟩
    have hxL : L x ≠ L c := fun heq => hxF ((hLeq x (hVP hxV)).mp heq)
    change L x + t * M x = L c + t * M c at hh
    rw [hMx] at hh
    exact hxL (add_right_cancel hh)
  exact ⟨G, hGface, ⟨hFG, fun hGF => hzF (hGF hzG)⟩,
    fun heq => hxG (heq.symm ▸ hVP hxV)⟩

/-- Every nonempty proper geometric face of a finite polytope is contained
in a facet with the required codimension-one dimension equation. -/
theorem finitePolytope_face_subset_facet [FiniteDimensional ℝ E]
    {P F : Set E} (hP : FinitePolytope P) (hF : IsConvexFace P F)
    (hne : F.Nonempty) (hproper : F ≠ P) :
    ∃ G, Facet P G ∧ F ⊆ G := by
  classical
  let S : Set (Set E) := {G | IsConvexFace P G ∧ F ⊆ G ∧ G ≠ P}
  have hS : S.Finite := (finitePolytope_faces_finite hP).subset (fun _ h => h.1)
  have hSne : S.Nonempty := ⟨F, hF, Set.Subset.rfl, hproper⟩
  obtain ⟨G, hG, hmax⟩ := hS.exists_maximal_wrt id S hSne
  have hGface := hG.1
  have hFG := hG.2.1
  have hGproper := hG.2.2
  have hGne : G.Nonempty := hne.mono hFG
  have hlt := face_affineDimension_lt hGface hGne hGproper
  have heq : affineDimension G + 1 = affineDimension P := by
    by_contra hh
    have hgap : affineDimension G + 1 < affineDimension P := by omega
    obtain ⟨H, hHface, hGH, hHproper⟩ := face_enlarge_of_dimension_gap hP hGface hGne hgap
    have hHS : H ∈ S := ⟨hHface, hFG.trans hGH.1, hHproper⟩
    have hGeqH : G = H := hmax H hHS hGH.1
    exact hGH.2 (by rw [hGeqH])
  exact ⟨G, ⟨hGface, hGne, heq⟩, hFG⟩

end Uniform5.Composition
