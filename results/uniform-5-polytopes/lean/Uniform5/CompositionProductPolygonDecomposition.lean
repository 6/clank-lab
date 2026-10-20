import Uniform5.CompositionProductFaceDimension

/-! A polygon face of an orthogonal product with a side count other than
four is an actual polygon factor face at an actual factor vertex. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical

theorem product_extremePoints {a b : ℕ} (P : Set (Space a)) (Q : Set (Space b)) :
    (product P Q).extremePoints ℝ = product (P.extremePoints ℝ) (Q.extremePoints ℝ) := by
  calc
    _ = ((productJoinEquiv a b) '' (P ×ˢ Q)).extremePoints ℝ := by
      rw [product_eq_join_image]
      rfl
    _ = (productJoinEquiv a b) '' (P.extremePoints ℝ ×ˢ Q.extremePoints ℝ) := by
      rw [← image_extremePoints, extremePoints_prod]
    _ = _ := (product_eq_join_image _ _).symm

theorem product_extremePoints_ncard {a b : ℕ} (P : Set (Space a)) (Q : Set (Space b)) :
    ((product P Q).extremePoints ℝ).ncard =
      (P.extremePoints ℝ).ncard * (Q.extremePoints ℝ).ncard := by
  rw [product_extremePoints, product_eq_join_image]
  change (((productJoinEquiv a b) '' (P.extremePoints ℝ ×ˢ Q.extremePoints ℝ))).ncard = _
  rw [Set.ncard_image_of_injOn (productJoinEquiv a b).injective.injOn]
  rw [← Set.Nat.card_coe_set_eq, Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod,
    Set.Nat.card_coe_set_eq, Set.Nat.card_coe_set_eq]

theorem finitePolytope_dim_one_extremePoints_ncard {a : ℕ} {P : Set (Space a)}
    (hP : FinitePolytope P) (hd : affineDimension P = 1) :
    (P.extremePoints ℝ).ncard = 2 := by
  rw [← coe_vertices P hP, Set.ncard_coe_Finset]
  exact finitePolytope_dim_one_vertices_card hP hd

/-- Unlike an abstract product label, the conclusion identifies the original
polygon set and its actual factor vertex. -/
theorem product_polygonFace_nonquadrilateral {a b n : ℕ}
    {P : Set (Space a)} {Q : Set (Space b)}
    (hP : FinitePolytope P) (hQ : FinitePolytope Q)
    {G : Set (EuclideanSpace ℝ (Fin a ⊕ Fin b))}
    (hG : PolygonFace (product P Q) G n) (hn : n ≠ 4) :
    (∃ A : Set (Space a), ∃ y : Space b,
      PolygonFace P A n ∧ y ∈ Q.extremePoints ℝ ∧ G = product A {y}) ∨
    (∃ x : Space a, ∃ B : Set (Space b),
      x ∈ P.extremePoints ℝ ∧ PolygonFace Q B n ∧ G = product {x} B) := by
  obtain ⟨A, B, hA, hB, hAn, hBn, heq, hd⟩ :=
    product_face_decomposition_dimension hG.1 (polygonFace_nonempty hG)
  have hAf := finitePolytope_face hP hA hAn
  have hBf := finitePolytope_face hQ hB hBn
  have hdim : affineDimension A + affineDimension B = 2 := hd.symm.trans hG.2.1
  have hcard : (A.extremePoints ℝ).ncard * (B.extremePoints ℝ).ncard = n := by
    rw [← product_extremePoints_ncard, ← heq]
    exact polygonFace_extremePoints_ncard hG
  by_cases hAz : affineDimension A = 0
  · obtain ⟨x, rfl⟩ := nonempty_affineDimension_zero_singleton hAn hAz
    have hdn : affineDimension B = 2 := by omega
    have hcn : (vertices B hBf).card = n := by
      simpa only [extremePoints_singleton, Set.ncard_singleton, one_mul,
        ← coe_vertices B hBf, Set.ncard_coe_Finset] using hcard
    exact Or.inr ⟨x, B, hA.2.mem_extremePoints,
      ⟨hB, hdn, vertices B hBf, coe_vertices B hBf, hcn⟩, heq⟩
  by_cases hBz : affineDimension B = 0
  · obtain ⟨y, rfl⟩ := nonempty_affineDimension_zero_singleton hBn hBz
    have hdn : affineDimension A = 2 := by omega
    have hcn : (vertices A hAf).card = n := by
      simpa only [extremePoints_singleton, Set.ncard_singleton, mul_one,
        ← coe_vertices A hAf, Set.ncard_coe_Finset] using hcard
    exact Or.inl ⟨A, y, ⟨hA, hdn, vertices A hAf, coe_vertices A hAf, hcn⟩,
      hB.2.mem_extremePoints, heq⟩
  have hdA : affineDimension A = 1 := by omega
  have hdB : affineDimension B = 1 := by omega
  rw [finitePolytope_dim_one_extremePoints_ncard hAf hdA,
    finitePolytope_dim_one_extremePoints_ncard hBf hdB] at hcard
  exact (hn (by omega)).elim

end Uniform5.Composition
