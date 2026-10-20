import Uniform5.Propagation
import Mathlib.Analysis.Convex.Intrinsic

/-!
# Convex faces of finite hulls are exposed

In a finite-dimensional real inner-product space, every convex extreme face
of a finite convex hull is exposed. The proof separates the affine span of
the face from the compact hull of the generators outside it. Relative
interiority and extremality establish the required disjointness.
-/

noncomputable section
namespace Uniform5
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Every convex extreme face of a finite convex hull is exposed, including
empty and improper faces. No full-dimensionality or metric normalization is
required. -/
theorem finite_convexFace_isExposed (V : Finset E) {F : Set E}
    (hF : IsConvexFace (convexHull ℝ (V : Set E)) F) :
    IsExposed ℝ (convexHull ℝ (V : Set E)) F := by
  classical
  intro hne
  let P := convexHull ℝ (V : Set E)
  let B : Set E := (V : Set E) \ F
  let A := affineSpan ℝ F
  obtain ⟨c, hc⟩ := (intrinsicInterior_nonempty hF.1).mpr hne
  have hcF : c ∈ F := intrinsicInterior_subset hc
  have hcA : c ∈ A := subset_affineSpan ℝ F hcF
  have hBP : convexHull ℝ B ⊆ P \ F :=
    convexHull_min (fun x hx => ⟨subset_convexHull ℝ _ hx.1, hx.2⟩)
      (hF.2.convex_diff (convex_convexHull ℝ _))
  have hdisj : Disjoint (convexHull ℝ B) (A : Set E) := by
    rw [Set.disjoint_left]
    intro x hx hxA
    obtain ⟨c', hc', hc'c⟩ := hc
    letI : Nonempty A := ⟨⟨c, hcA⟩⟩
    let x' : A := ⟨x, hxA⟩
    have hcont : Continuous (AffineMap.lineMap x' c' : ℝ → A) := by
      change Continuous (fun t : ℝ => t • (c' -ᵥ x') +ᵥ x')
      fun_prop
    obtain ⟨t, ht1, ht⟩ :=
      hcont.tendsto' _ _ (AffineMap.lineMap_apply_one (k := ℝ) x' c') |>.eventually_mem
        (mem_interior_iff_mem_nhds.1 hc') |>.exists_gt
    have ht0 : 0 < t := lt_trans zero_lt_one ht1
    have heq : ((AffineMap.lineMap x' c' t : A) : E) =
        AffineMap.lineMap x c t := by
      simp [AffineMap.lineMap_apply, AffineSubspace.coe_vadd,
        AffineSubspace.coe_vsub, x', hc'c]
    change ((AffineMap.lineMap x' c' t : A) : E) ∈ F at ht
    rw [heq] at ht
    have hcseg : c ∈ openSegment ℝ x (AffineMap.lineMap x c t) := by
      rw [openSegment_eq_image_lineMap]
      refine ⟨t⁻¹, ⟨inv_pos.mpr ht0, ?_⟩, ?_⟩
      · nlinarith [inv_mul_cancel₀ ht0.ne']
      · rw [AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ ht0.ne',
          AffineMap.lineMap_apply_one]
    exact (hBP hx).2 (hF.2.2 (hBP hx).1 (hF.2.1 ht) hcF hcseg).1
  obtain ⟨L, a, b, hB, hab, hA⟩ := geometric_hahn_banach_compact_closed
    (convex_convexHull ℝ B) ((V.finite_toSet.subset (fun _ hx => hx.1)).isCompact_convexHull)
    A.convex A.closed_of_finiteDimensional hdisj
  have hLc : b < L c := hA c hcA
  have hconstant : ∀ x ∈ A, L x = L c := by
    intro x hx
    by_contra hn
    have hd : L x - L c ≠ 0 := sub_ne_zero.mpr hn
    have h := hA (AffineMap.lineMap c x ((b - L c) / (L x - L c)))
      (AffineMap.lineMap_mem _ hcA hx)
    rw [AffineMap.lineMap_apply_module, map_add, map_smul, map_smul] at h
    simp only [smul_eq_mul] at h
    have he : (1 - (b - L c) / (L x - L c)) * L c +
        ((b - L c) / (L x - L c)) * L x = b := by field_simp [hd]; ring
    exact (ne_of_gt h) he
  have hstrict : ∀ x ∈ (V : Set E), x ∉ F → L x < L c := by
    intro x hx hxF
    exact lt_trans (hB x (subset_convexHull ℝ B ⟨hx, hxF⟩)) (lt_trans hab hLc)
  have hbound : ∀ x ∈ P, L x ≤ L c := by
    apply convexHull_min _ (convex_halfSpace_le L.toLinearMap.isLinear (L c))
    intro x hx
    by_cases hxF : x ∈ F
    · exact le_of_eq (hconstant x (subset_affineSpan ℝ F hxF))
    · exact le_of_lt (hstrict x hx hxF)
  let T := L.toExposed P
  have hT : IsExposed ℝ P T := fun _ => ⟨L, rfl⟩
  have hTface : IsConvexFace P T :=
    ⟨hT.convex (convex_convexHull ℝ _), hT.isExtreme⟩
  have hinter : (V : Set E) ∩ T = (V : Set E) ∩ F := by
    ext x
    constructor
    · rintro ⟨hxV, hxT⟩
      refine ⟨hxV, ?_⟩
      by_contra hxF
      exact (hstrict x hxV hxF).not_le (hxT.2 c (hF.2.1 hcF))
    · rintro ⟨hxV, hxF⟩
      refine ⟨hxV, subset_convexHull ℝ _ hxV, ?_⟩
      intro y hy
      rw [hconstant x (subset_affineSpan ℝ F hxF)]
      exact hbound y hy
  have heq : T = F := by
    rw [← face_eq_convexHull_inter (V : Set E) hTface,
      ← face_eq_convexHull_inter (V : Set E) hF, hinter]
  exact ⟨L, heq.symm⟩

/-- The finite-polytope convex-face/exposed-face bridge is a theorem in every
finite-dimensional real inner-product space. -/
theorem polytope_faces_exposed (V : Finset E) : PolytopeFacesExposed V :=
  fun _ hF => finite_convexFace_isExposed V hF

/-- On a finite hull, the convex-extreme and exposed notions of face agree. -/
theorem isConvexFace_iff_isExposed (V : Finset E) {F : Set E} :
    IsConvexFace (convexHull ℝ (V : Set E)) F ↔
      IsExposed ℝ (convexHull ℝ (V : Set E)) F :=
  ⟨finite_convexFace_isExposed V,
    fun h => ⟨h.convex (convex_convexHull ℝ _), h.isExtreme⟩⟩

end Uniform5
