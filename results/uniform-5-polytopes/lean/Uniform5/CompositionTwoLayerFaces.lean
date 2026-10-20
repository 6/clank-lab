import Uniform5.CompositionAntiprismLayers
import Uniform5.CompositionCaseBProductSlices

/-! A polygon with at least five vertices in a two-layer polyhedron is a layer. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A proper face of a two-dimensional finite polytope has at most two
vertices, including the empty and singleton cases. -/
theorem polygon_proper_face_ncard_le_two {P F : Set E}
    (hP : FinitePolytope P) (hd : affineDimension P = 2)
    (hF : IsConvexFace P F) (hne : F ≠ P) : (F.extremePoints ℝ).ncard ≤ 2 := by
  by_cases hFn : F.Nonempty
  · have hdim := face_affineDimension_lt hF hFn hne
    rw [hd] at hdim
    by_cases hz : affineDimension F = 0
    · obtain ⟨x, rfl⟩ := nonempty_affineDimension_zero_singleton hFn hz
      simp
    · have hff := finitePolytope_face hP hF hFn
      rw [← coe_vertices F hff, Set.ncard_coe_Finset,
        finitePolytope_dim_one_vertices_card hff (by omega)]
  · rw [Set.not_nonempty_iff_eq_empty.mp hFn]
    simp

/-- If two polygon faces cover the vertices, every other polygon face has
at most four vertices: at most two from each layer. -/
theorem two_layer_polygon_ncard_le_four {P A B F : Set E}
    (hP : FinitePolytope P) (hA : IsConvexFace P A) (hB : IsConvexFace P B)
    (hAn : A.Nonempty) (hBn : B.Nonempty) (hdA : affineDimension A = 2)
    (hdB : affineDimension B = 2) (hcov : P.extremePoints ℝ ⊆ A ∪ B)
    (hF : IsConvexFace P F) (hFn : F.Nonempty) (hdF : affineDimension F = 2)
    (hFA : F ≠ A) (hFB : F ≠ B) : (F.extremePoints ℝ).ncard ≤ 4 := by
  have hPfinite : (P.extremePoints ℝ).Finite := by
    rw [← coe_vertices P hP]
    exact (vertices P hP).finite_toSet
  have hbound (C : Set E) (hC : IsConvexFace P C) (hCn : C.Nonempty)
      (hdC : affineDimension C = 2) (hFC : F ≠ C) :
      ((C ∩ F).extremePoints ℝ).ncard ≤ 2 := by
    have hI : IsConvexFace P (C ∩ F) := ⟨hC.1.inter hF.1, hC.2.inter hF.2⟩
    have hIC := face_restrict hI hC.2.1 inter_subset_left
    apply polygon_proper_face_ncard_le_two (finitePolytope_face hP hC hCn) hdC hIC
    intro he
    have hCF : C ⊆ F := by rw [← he]; exact inter_subset_right
    exact hFC (convexFace_eq_of_dimension_eq (face_restrict hC hF.2.1 hCF)
      hCn (hdC.trans hdF.symm)).symm
  have hIA : IsConvexFace P (A ∩ F) := ⟨hA.1.inter hF.1, hA.2.inter hF.2⟩
  have hIB : IsConvexFace P (B ∩ F) := ⟨hB.1.inter hF.1, hB.2.inter hF.2⟩
  have hAf := hPfinite.subset hIA.2.extremePoints_subset_extremePoints
  have hBf := hPfinite.subset hIB.2.extremePoints_subset_extremePoints
  have hsub : F.extremePoints ℝ ⊆ (A ∩ F).extremePoints ℝ ∪ (B ∩ F).extremePoints ℝ := by
    intro x hx
    have hxP := hF.2.extremePoints_subset_extremePoints hx
    rcases hcov hxP with hxA | hxB
    · left; rw [face_extremePoints_eq hIA]; exact ⟨⟨hxA, hx.1⟩, hxP⟩
    · right; rw [face_extremePoints_eq hIB]; exact ⟨⟨hxB, hx.1⟩, hxP⟩
  have hle := Set.ncard_le_ncard hsub (hAf.union hBf)
  have huni := Set.ncard_union_le ((A ∩ F).extremePoints ℝ) ((B ∩ F).extremePoints ℝ)
  have ha := hbound A hA hAn hdA hFA
  have hb := hbound B hB hBn hdB hFB
  omega

/-- Every actual antiprism polygon with at least five vertices is one of
the two concrete regular-polygon layers. -/
theorem antiprism_polygon_is_layer {n k : ℕ} (hn : 3 ≤ n) (hk : 5 ≤ k)
    {G : Set (Space 3)} (hG : PolygonFace (antiprismModel n) G k) :
    G = antiprismLayer n false ∨ G = antiprismLayer n true := by
  by_contra h
  push_neg at h
  have hA := antiprism_layer_polygonFace hn false
  have hB := antiprism_layer_polygonFace hn true
  have hcov : (antiprismModel n).extremePoints ℝ ⊆ antiprismLayer n false ∪ antiprismLayer n true := by
    rw [antiprism_extremePoints]
    rintro x ⟨⟨b, i⟩, rfl⟩
    cases b
    · exact Or.inl (subset_convexHull ℝ _ ⟨i, rfl⟩)
    · exact Or.inr (subset_convexHull ℝ _ ⟨i, rfl⟩)
  have hc := two_layer_polygon_ncard_le_four (antiprismModel_finitePolytope (by omega))
    hA.1 hB.1 (polygonFace_nonempty hA) (polygonFace_nonempty hB) hA.2.1 hB.2.1
    hcov hG.1 (polygonFace_nonempty hG) hG.2.1 h.1 h.2
  rw [polygonFace_extremePoints_ncard hG] at hc
  omega

end Uniform5.Composition
