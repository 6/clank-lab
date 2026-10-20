import Uniform5.CompositionCaseBProductSlices
import Uniform5.CompositionCaseBModelRadii

/-! The actual incident cells in the Case B product models, identified up
to Euclidean congruence from proved product-face incidence. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def unitSegmentEmbedding (a b : E) (h : dist a b = 1) : Space 1 →ᵃⁱ[ℝ] E where
  toFun z := a + z 0 • (b - a)
  linear := {
    toFun z := z 0 • (b - a)
    map_add' := by intros; simp [add_smul]
    map_smul' := by intros; simp [mul_smul] }
  map_vadd' := by intros; simp [vadd_eq_add, add_smul]; abel
  norm_map z := by
    have hn : ‖b - a‖ = 1 := by rw [← dist_eq_norm, dist_comm, h]
    change ‖z 0 • (b - a)‖ = ‖z‖
    rw [norm_smul, hn, mul_one]
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_succ, Real.norm_eq_abs,
      Real.sqrt_sq_eq_abs]

theorem congruent_unit_segment {a b : E} (h : dist a b = 1) :
    Congruent (segment ℝ a b) unitInterval := by
  let f := unitSegmentEmbedding a b h
  have he : f '' unitInterval = segment ℝ a b := by
    change f.toAffineMap '' segment ℝ 0 (!₂[1] : Space 1) = _
    rw [image_segment ℝ f.toAffineMap]
    simp [f, unitSegmentEmbedding]
  have hc := congruent_affineIsometry_image f unitInterval
  rw [he] at hc
  exact congruent_symm hc

variable [FiniteDimensional ℝ E]

theorem finitePolytope_unitEdges_dim_one_congruent {P : Set E}
    (hP : FinitePolytope P) (hU : UnitEdges P) (hd : affineDimension P = 1) :
    Congruent P unitInterval := by
  obtain ⟨a, b, hab, he, hv⟩ := finitePolytope_dim_one_segment hP hd
  have hE : Edge P a b := by
    refine ⟨?_, ?_, hab, ?_⟩
    · rw [hv]; simp
    · rw [hv]; simp
    · rw [← he]
  rw [he]
  exact congruent_unit_segment (hU a b hE)

theorem product_singleton_right_image {a b : ℕ} (P : Set (Space a)) (y : Space b) :
    product P {y} = productLeftSlice y '' P := by
  ext z
  constructor
  · rintro ⟨x, hx, y', hy, rfl⟩
    have hy' : y' = y := hy
    subst y'
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, y, rfl, rfl⟩

/-- Every actual cell at the selected polygon of a duoprism is the prism
on that very polygon size, including when both factor sizes agree. -/
theorem duoprism_cell_at_nonquadrilateral_polygon {n q : ℕ}
    (hn : 3 ≤ n) (hq : 3 ≤ q) (hn4 : n ≠ 4)
    {G C : Set (EuclideanSpace ℝ (Fin 2 ⊕ Fin 2))}
    (hG : PolygonFace (duoprismModel n q) G n)
    (hC : IsConvexFace (duoprismModel n q) C)
    (hdC : affineDimension C = 3) (hGC : G ⊆ C) :
    Congruent C (polygonPrismModel n) := by
  have hCn := (polygonFace_nonempty hG).mono hGC
  rcases duoprism_nonquadrilateral_polygon_slices hn hq hG hn4 with
    ⟨_, y, hy, he⟩ | ⟨heq, x, hx, he⟩
  · obtain ⟨B, hB, hBn, hdB, _, hCB⟩ := product_three_cell_at_left_polygon
      (finitePolytope_nonempty (unitPolygon_finitePolytope hn))
      (unitPolygon_self_polygonFace hn).2.1 hC hCn hdC (he ▸ hGC)
    have hb := finitePolytope_unitEdges_dim_one_congruent
      (finitePolytope_face (unitPolygon_finitePolytope hq) hB hBn)
      (unitEdges_face (unitPolygon_finitePolytope hq) hB (unitEdges_unitPolygon hq)) hdB
    rw [hCB]
    exact congruent_product (congruent_refl _) hb
  · obtain ⟨A, hA, hAn, hdA, _, hCA⟩ := product_three_cell_at_right_polygon
      (finitePolytope_nonempty (unitPolygon_finitePolytope hq))
      (unitPolygon_self_polygonFace hq).2.1 hC hCn hdC (he ▸ hGC)
    have ha := finitePolytope_unitEdges_dim_one_congruent
      (finitePolytope_face (unitPolygon_finitePolytope hn) hA hAn)
      (unitEdges_face (unitPolygon_finitePolytope hn) hA (unitEdges_unitPolygon hn)) hdA
    rw [hCA, heq]
    exact congruent_trans (congruent_product ha (congruent_refl _))
      (congruent_product_swap unitInterval (unitPolygon q))

/-- A base polygon of the antiprism-prism has exactly its antiprism slice
and its polygon-prism as incident three-cell types. -/
theorem antiprismPrism_cell_at_nonquadrilateral_polygon {n : ℕ}
    (hn : 3 ≤ n) (hn4 : n ≠ 4)
    (hM : UnitUniform 4 (antiprismPrismModel n))
    {G C : Set (EuclideanSpace ℝ (Fin 3 ⊕ Fin 1))}
    (hG : PolygonFace (antiprismPrismModel n) G n)
    (hC : IsConvexFace (antiprismPrismModel n) C)
    (hdC : affineDimension C = 3) (hGC : G ⊆ C) :
    Congruent C (antiprismModel n) ∨ Congruent C (polygonPrismModel n) := by
  have hAnti := antiprismModel_finitePolytope (by omega : 0 < n)
  obtain ⟨A, y, hA, hy, he⟩ := polyhedralPrism_nonquadrilateral_polygon_slice hAnti hG hn4
  have hdAnti : affineDimension (antiprismModel n) = 3 := by
    have hd := uniform_dimension hM.1
    change affineDimension (product (antiprismModel n) unitInterval) = 4 at hd
    rw [affineDimension_product (finitePolytope_nonempty hAnti)
      (finitePolytope_nonempty unitInterval_finitePolytope), unitInterval_affineDimension] at hd
    omega
  have hs := polyhedralPrism_cells_at_polygon_slice hdAnti hA hC
    ((polygonFace_nonempty hG).mono hGC) hdC (he ▸ hGC)
  rcases hs with hs | hs
  · rw [hs, product_singleton_right_image]
    exact Or.inl (congruent_symm (congruent_affineIsometry_image (productLeftSlice y) _))
  · have hGA : Congruent G A := by
      rw [he, product_singleton_right_image]
      exact congruent_symm (congruent_affineIsometry_image (productLeftSlice y) A)
    obtain ⟨_, f, hf⟩ := polygonFace_unitPolygon hM hG
    have hg : Congruent G (unitPolygon n) := by
      rw [hf]
      exact congruent_symm (congruent_affineIsometry_image f _)
    rw [hs]
    exact Or.inr (congruent_product (congruent_trans (congruent_symm hGA) hg)
      (congruent_refl unitInterval))

end Uniform5.Composition
