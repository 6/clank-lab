import Uniform5.CompositionProductPolygonDecomposition

/-! Actual nonquadrilateral polygon occurrences in the Case B product
families, with their literal coordinate slices and original side counts. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem affineDimension_mono_of_subset {P Q : Set E} (h : P ⊆ Q) :
    affineDimension P ≤ affineDimension Q :=
  Submodule.finrank_mono (AffineSubspace.direction_le (affineSpan_mono ℝ h))

theorem convexFace_eq_of_dimension_eq {P F : Set E}
    (hF : IsConvexFace P F) (hne : F.Nonempty)
    (hd : affineDimension F = affineDimension P) : F = P := by
  by_contra hn
  have hh := face_affineDimension_lt hF hne hn
  omega

theorem productPoint_mem_iff {a b : ℕ} {P : Set (Space a)} {Q : Set (Space b)}
    (x : Space a) (y : Space b) : productPoint x y ∈ product P Q ↔ x ∈ P ∧ y ∈ Q := by
  constructor
  · rintro ⟨u, hu, v, hv, h⟩
    have hx := congrArg productLeftProjection h
    have hy := congrArg productRightProjection h
    simp only [productLeftProjection_point, productRightProjection_point] at hx hy
    exact ⟨hx.symm ▸ hu, hy.symm ▸ hv⟩
  · rintro ⟨hx, hy⟩
    exact ⟨x, hx, y, hy, rfl⟩

theorem product_subset_factors {a b : ℕ} {A P : Set (Space a)} {B Q : Set (Space b)}
    (hA : A.Nonempty) (hB : B.Nonempty) (h : product A B ⊆ product P Q) :
    A ⊆ P ∧ B ⊆ Q := by
  obtain ⟨x, hx⟩ := hA
  obtain ⟨y, hy⟩ := hB
  exact ⟨fun z hz => ((productPoint_mem_iff z y).mp (h ⟨z, hz, y, hy, rfl⟩)).1,
    fun z hz => ((productPoint_mem_iff x z).mp (h ⟨x, hx, z, hz, rfl⟩)).2⟩

theorem unitInterval_affineDimension : affineDimension unitInterval = 1 := by
  apply affineDimension_segment
  intro h
  have hh := congrArg (fun z : Space 1 => z 0) h
  norm_num at hh

/-- The two possible polygon factors are identified, including the equality
of the observed side count with the selected factor's parameter. -/
theorem duoprism_nonquadrilateral_polygon_slices {p q n : ℕ}
    (hp : 3 ≤ p) (hq : 3 ≤ q)
    {G : Set (EuclideanSpace ℝ (Fin 2 ⊕ Fin 2))}
    (hG : PolygonFace (duoprismModel p q) G n) (hn : n ≠ 4) :
    (n = p ∧ ∃ y ∈ (unitPolygon q).extremePoints ℝ, G = product (unitPolygon p) {y}) ∨
    (n = q ∧ ∃ x ∈ (unitPolygon p).extremePoints ℝ, G = product {x} (unitPolygon q)) := by
  rcases product_polygonFace_nonquadrilateral (unitPolygon_finitePolytope hp)
    (unitPolygon_finitePolytope hq) hG hn with ⟨A, y, hA, hy, he⟩ | ⟨x, B, hx, hB, he⟩
  · have ha : A = unitPolygon p := convexFace_eq_of_dimension_eq hA.1 (polygonFace_nonempty hA)
      (hA.2.1.trans (unitPolygon_self_polygonFace hp).2.1.symm)
    subst A
    have hc := polygonFace_extremePoints_ncard hA
    rw [unitPolygon_extremePoints_ncard hp] at hc
    exact Or.inl ⟨hc.symm, y, hy, he⟩
  · have hb : B = unitPolygon q := convexFace_eq_of_dimension_eq hB.1 (polygonFace_nonempty hB)
      (hB.2.1.trans (unitPolygon_self_polygonFace hq).2.1.symm)
    subst B
    have hc := polygonFace_extremePoints_ncard hB
    rw [unitPolygon_extremePoints_ncard hq] at hc
    exact Or.inr ⟨hc.symm, x, hx, he⟩

/-- Any nonquadrilateral polygon of a prism is a base-polygon endpoint
slice. This needs no enumeration of the base's faces. -/
theorem polyhedralPrism_nonquadrilateral_polygon_slice {P : Set (Space 3)}
    (hP : FinitePolytope P) {n : ℕ}
    {G : Set (EuclideanSpace ℝ (Fin 3 ⊕ Fin 1))}
    (hG : PolygonFace (polyhedralPrismModel P) G n) (hn : n ≠ 4) :
    ∃ A : Set (Space 3), ∃ y : Space 1,
      PolygonFace P A n ∧ y ∈ unitInterval.extremePoints ℝ ∧ G = product A {y} := by
  rcases product_polygonFace_nonquadrilateral hP unitInterval_finitePolytope hG hn with h | ⟨x, B, hx, hB, he⟩
  · exact h
  · have hd := affineDimension_mono_of_subset hB.1.2.1
    rw [hB.2.1, unitInterval_affineDimension] at hd
    omega

/-- At a prism's base-polygon slice, every incident three-face is precisely
the base endpoint slice or the polygon's unit-height prism. -/
theorem polyhedralPrism_cells_at_polygon_slice {P A : Set (Space 3)} {n : ℕ}
    (hdP : affineDimension P = 3) (hA : PolygonFace P A n)
    {y : Space 1} {C : Set (EuclideanSpace ℝ (Fin 3 ⊕ Fin 1))}
    (hC : IsConvexFace (polyhedralPrismModel P) C) (hne : C.Nonempty)
    (hdC : affineDimension C = 3) (hAC : product A {y} ⊆ C) :
    C = product P {y} ∨ C = product A unitInterval := by
  obtain ⟨U, V, hU, hV, hUn, hVn, he, hd⟩ := product_face_decomposition_dimension hC hne
  have hsub := product_subset_factors (polygonFace_nonempty hA) (singleton_nonempty y) (he ▸ hAC)
  have hdV := affineDimension_mono_of_subset hV.2.1
  rw [unitInterval_affineDimension] at hdV
  by_cases hVz : affineDimension V = 0
  · have hdU : affineDimension U = 3 := by omega
    have hUP := convexFace_eq_of_dimension_eq hU hUn (hdU.trans hdP.symm)
    obtain ⟨z, hz⟩ := nonempty_affineDimension_zero_singleton hVn hVz
    have hyz : y = z := by simpa only [hz, singleton_subset_iff, mem_singleton_iff] using hsub.2
    exact Or.inl (by simpa only [hUP, hz, ← hyz] using he)
  · have hdV1 : affineDimension V = 1 := by omega
    have hVI := convexFace_eq_of_dimension_eq hV hVn (hdV1.trans unitInterval_affineDimension.symm)
    have hdU : affineDimension U = 2 := by omega
    have hAU := convexFace_eq_of_dimension_eq (face_restrict hA.1 hU.2.1 hsub.1)
      (polygonFace_nonempty hA) (hA.2.1.trans hdU.symm)
    exact Or.inr (by simpa only [hVI, ← hAU] using he)

/-- In a duoprism, an incident three-cell at a first-factor polygon is
that same entire polygon times an actual one-dimensional face of the other factor. -/
theorem product_three_cell_at_left_polygon {a b : ℕ}
    {P : Set (Space a)} {Q : Set (Space b)} (hP : P.Nonempty)
    (hdP : affineDimension P = 2) {y : Space b}
    {C : Set (EuclideanSpace ℝ (Fin a ⊕ Fin b))}
    (hC : IsConvexFace (product P Q) C) (hne : C.Nonempty)
    (hdC : affineDimension C = 3) (hPC : product P {y} ⊆ C) :
    ∃ B : Set (Space b), IsConvexFace Q B ∧ B.Nonempty ∧
      affineDimension B = 1 ∧ y ∈ B ∧ C = product P B := by
  obtain ⟨U, V, hU, hV, hUn, hVn, he, hd⟩ := product_face_decomposition_dimension hC hne
  have hs := product_subset_factors hP (singleton_nonempty y) (he ▸ hPC)
  have hUP : U = P := Subset.antisymm hU.2.1 hs.1
  have hdV : affineDimension V = 1 := by rw [hUP, hdP] at hd; omega
  exact ⟨V, hV, hVn, hdV, hs.2 rfl, by simpa only [hUP] using he⟩

/-- The symmetric statement keeps the actual second-factor polygon. -/
theorem product_three_cell_at_right_polygon {a b : ℕ}
    {P : Set (Space a)} {Q : Set (Space b)} (hQ : Q.Nonempty)
    (hdQ : affineDimension Q = 2) {x : Space a}
    {C : Set (EuclideanSpace ℝ (Fin a ⊕ Fin b))}
    (hC : IsConvexFace (product P Q) C) (hne : C.Nonempty)
    (hdC : affineDimension C = 3) (hQC : product {x} Q ⊆ C) :
    ∃ A : Set (Space a), IsConvexFace P A ∧ A.Nonempty ∧
      affineDimension A = 1 ∧ x ∈ A ∧ C = product A Q := by
  obtain ⟨U, V, hU, hV, hUn, hVn, he, hd⟩ := product_face_decomposition_dimension hC hne
  have hs := product_subset_factors (singleton_nonempty x) hQ (he ▸ hQC)
  have hVQ : V = Q := Subset.antisymm hV.2.1 hs.2
  have hdU : affineDimension U = 1 := by rw [hVQ, hdQ] at hd; omega
  exact ⟨U, hU, hUn, hdU, hs.1 rfl, by simpa only [hVQ] using he⟩

end Uniform5.Composition
