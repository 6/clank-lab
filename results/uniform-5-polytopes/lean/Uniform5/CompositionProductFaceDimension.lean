import Uniform5.CompositionProductFaceDecomposition

/-! Intrinsic dimensions of actual orthogonal product faces add. -/
noncomputable section
namespace Uniform5.Composition
open Set

noncomputable def productJoinEquiv (a b : ℕ) :
    (Space a × Space b) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin a ⊕ Fin b) where
  toLinearMap := productJoinLinear
  invFun z := (productLeftProjection z, productRightProjection z)
  left_inv := by intro z; rfl
  right_inv := productPoint_projections

noncomputable def productSubmoduleEquiv {a b : ℕ}
    (S : Submodule ℝ (Space a)) (T : Submodule ℝ (Space b)) :
    S.prod T ≃ₗ[ℝ] (S × T) where
  toFun z := (⟨z.1.1, z.2.1⟩, ⟨z.1.2, z.2.2⟩)
  invFun z := ⟨(z.1.1, z.2.1), z.1.2, z.2.2⟩
  left_inv := by intro z; rfl
  right_inv := by intro z; rfl
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- When both sets contain zero, the span of their Cartesian product is
the Cartesian product of their spans. -/
theorem span_prod_eq_of_zero_mem {a b : ℕ} {S : Set (Space a)} {T : Set (Space b)}
    (hS : 0 ∈ S) (hT : 0 ∈ T) :
    Submodule.span ℝ (S ×ˢ T) = (Submodule.span ℝ S).prod (Submodule.span ℝ T) := by
  apply le_antisymm (Submodule.span_prod_le S T)
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  change x ∈ Submodule.span ℝ S at hx
  change y ∈ Submodule.span ℝ T at hy
  have hx0 : (x, (0 : Space b)) ∈ Submodule.span ℝ (S ×ˢ T) := by
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨hx, hT⟩
    | zero => exact Submodule.zero_mem _
    | add x y hx hy ihx ihy => simpa using Submodule.add_mem _ ihx ihy
    | smul t x hx ih => simpa using Submodule.smul_mem _ t ih
  have h0y : ((0 : Space a), y) ∈ Submodule.span ℝ (S ×ˢ T) := by
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨hS, hy⟩
    | zero => exact Submodule.zero_mem _
    | add x y hx hy ihx ihy => simpa using Submodule.add_mem _ ihx ihy
    | smul t y hy ih => simpa using Submodule.smul_mem _ t ih
  simpa using Submodule.add_mem _ hx0 h0y

theorem product_sub_image {a b : ℕ} (P : Set (Space a)) (Q : Set (Space b))
    (x : Space a) (y : Space b) :
    ((fun z => z - productPoint x y) '' product P Q) =
      productJoinLinear '' (((fun u => u - x) '' P) ×ˢ ((fun v => v - y) '' Q)) := by
  ext z
  constructor
  · rintro ⟨w, ⟨u, hu, v, hv, rfl⟩, rfl⟩
    refine ⟨(u - x, v - y), ⟨⟨u, hu, rfl⟩, ⟨v, hv, rfl⟩⟩, ?_⟩
    ext i
    cases i <;> simp [productJoinLinear, productPoint]
  · rintro ⟨⟨u, v⟩, ⟨⟨u', hu, rfl⟩, ⟨v', hv, rfl⟩⟩, rfl⟩
    refine ⟨productPoint u' v', ⟨u', hu, v', hv, rfl⟩, ?_⟩
    ext i
    cases i <;> simp [productJoinLinear, productPoint]

/-- This applies to arbitrary nonempty sets, not only uniform polytopes. -/
theorem affineDimension_product {a b : ℕ} {P : Set (Space a)} {Q : Set (Space b)}
    (hP : P.Nonempty) (hQ : Q.Nonempty) :
    affineDimension (product P Q) = affineDimension P + affineDimension Q := by
  obtain ⟨x, hx⟩ := hP
  obtain ⟨y, hy⟩ := hQ
  have hxy : productPoint x y ∈ product P Q := ⟨x, hx, y, hy, rfl⟩
  unfold affineDimension Uniform5.affineDimension
  rw [direction_affineSpan, direction_affineSpan, direction_affineSpan]
  rw [vectorSpan_eq_span_vsub_set_right ℝ hxy, vectorSpan_eq_span_vsub_set_right ℝ hx,
    vectorSpan_eq_span_vsub_set_right ℝ hy]
  change Module.finrank ℝ (Submodule.span ℝ ((fun z => z - productPoint x y) '' product P Q)) = _
  have hP0 : (0 : Space a) ∈ (fun u => u - x) '' P := ⟨x, hx, sub_self x⟩
  have hQ0 : (0 : Space b) ∈ (fun v => v - y) '' Q := ⟨y, hy, sub_self y⟩
  rw [product_sub_image, ← Submodule.map_span, span_prod_eq_of_zero_mem hP0 hQ0]
  change Module.finrank ℝ (Submodule.map (productJoinEquiv a b).toLinearMap _) = _
  rw [(productJoinEquiv a b).finrank_map_eq,
    (productSubmoduleEquiv _ _).finrank_eq, Module.finrank_prod]
  rfl

/-- Dimension information is a conclusion of the actual face decomposition. -/
theorem product_face_decomposition_dimension {a b : ℕ}
    {P : Set (Space a)} {Q : Set (Space b)}
    {F : Set (EuclideanSpace ℝ (Fin a ⊕ Fin b))}
    (hF : IsConvexFace (product P Q) F) (hne : F.Nonempty) :
    ∃ A : Set (Space a), ∃ B : Set (Space b),
      IsConvexFace P A ∧ IsConvexFace Q B ∧ A.Nonempty ∧ B.Nonempty ∧
        F = product A B ∧ affineDimension F = affineDimension A + affineDimension B := by
  obtain ⟨A, B, hA, hB, hAn, hBn, rfl⟩ := product_face_decomposition hF hne
  exact ⟨A, B, hA, hB, hAn, hBn, rfl, affineDimension_product hAn hBn⟩

end Uniform5.Composition
