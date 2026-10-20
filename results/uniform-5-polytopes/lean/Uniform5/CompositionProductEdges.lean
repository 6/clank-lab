import Uniform5.CompositionProductPolygonDecomposition

/-! Actual exposed edges of the orthogonal product change exactly one factor. -/
noncomputable section
namespace Uniform5.Composition
open Set

@[simp] theorem productPoint_mem_product {a b : ℕ} {P : Set (Space a)} {Q : Set (Space b)}
    {x : Space a} {y : Space b} : productPoint x y ∈ product P Q ↔ x ∈ P ∧ y ∈ Q := by
  constructor
  · rintro ⟨u, hu, v, hv, he⟩
    have hx := congrArg productLeftProjection he
    have hy := congrArg productRightProjection he
    change x = u at hx
    change y = v at hy
    exact ⟨hx.symm ▸ hu, hy.symm ▸ hv⟩
  · rintro ⟨hx, hy⟩
    exact ⟨x, hx, y, hy, rfl⟩

/-- The right-factor slice preserves its actual Euclidean metric. -/
noncomputable def productRightSlice {a b : ℕ} (x : Space a) :
    Space b →ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin a ⊕ Fin b) where
  toFun y := productPoint x y
  linear := {
    toFun y := productPoint 0 y
    map_add' := by intro y z; ext i; cases i <;> simp [productPoint]
    map_smul' := by intro t y; ext i; cases i <;> simp [productPoint] }
  map_vadd' := by intro y z; ext i; cases i <;> simp [productPoint, vadd_eq_add]
  norm_map y := by simp [productPoint, EuclideanSpace.norm_eq, Fintype.sum_sum_type]

@[simp] theorem product_left_slice_image {a b : ℕ} (P : Set (Space a)) (y : Space b) :
    productLeftSlice y '' P = product P {y} := by
  ext z
  simp only [mem_image, product, mem_setOf_eq, mem_singleton_iff, exists_eq_left]
  change (∃ x ∈ P, productPoint x y = z) ↔ _
  simp only [eq_comm]

@[simp] theorem product_right_slice_image {a b : ℕ} (Q : Set (Space b)) (x : Space a) :
    productRightSlice x '' Q = product {x} Q := by
  ext z
  simp only [mem_image, product, mem_setOf_eq, mem_singleton_iff, exists_eq_left]
  change (∃ y ∈ Q, productPoint x y = z) ↔ _
  simp only [eq_comm]

/-- A right slice at an extreme point is an actual convex face. -/
theorem product_right_slice_face {a b : ℕ} {P : Set (Space a)} {Q : Set (Space b)}
    (hQ : Convex ℝ Q) {x : Space a} (hx : x ∈ P.extremePoints ℝ) :
    IsConvexFace (product P Q) (productRightSlice x '' Q) := by
  refine ⟨hQ.affine_image (productRightSlice x).toAffineMap, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨x, hx.1, y, hy, rfl⟩
  · rintro z ⟨zx, hzx, zy, hzy, rfl⟩ w ⟨wx, hwx, wy, hwy, rfl⟩ t ⟨ty, hty, rfl⟩ hs
    obtain ⟨s, r, hs, hr, hsr, heq⟩ := hs
    have hex : s • zx + r • wx = x := by
      ext i
      have hh := congrArg (fun z : EuclideanSpace ℝ (Fin a ⊕ Fin b) => z (Sum.inl i)) heq
      simpa [productRightSlice, productPoint] using hh
    obtain ⟨hzx', hwx'⟩ := hx.2 hzx hwx ⟨s, r, hs, hr, hsr, hex⟩
    exact ⟨⟨zy, hzy, by change productPoint x zy = productPoint zx zy; rw [hzx']⟩,
      ⟨wy, hwy, by change productPoint x wy = productPoint wx wy; rw [hwx']⟩⟩

/-- Edges in either factor are exactly the product's actual edges. -/
theorem product_edge_iff {a b : ℕ} {P : Set (Space a)} {Q : Set (Space b)}
    (hP : FinitePolytope P) (hQ : FinitePolytope Q) (hPQ : FinitePolytope (product P Q))
    {x x' : Space a} {y y' : Space b} :
    Edge (product P Q) (productPoint x y) (productPoint x' y') ↔
      (y = y' ∧ y ∈ Q.extremePoints ℝ ∧ Edge P x x') ∨
      (x = x' ∧ x ∈ P.extremePoints ℝ ∧ Edge Q y y') := by
  constructor
  · intro he
    have hv := he.1
    rw [product_extremePoints, productPoint_mem_product] at hv
    have hw := he.2.1
    rw [product_extremePoints, productPoint_mem_product] at hw
    obtain ⟨A, B, hA, hB, hAn, hBn, hAB, hd⟩ :=
      product_face_decomposition_dimension (edge_isConvexFace he) ⟨_, left_mem_segment ℝ _ _⟩
    have ha : x ∈ A ∧ y ∈ B := by
      rw [← productPoint_mem_product, ← hAB]
      exact left_mem_segment ℝ _ _
    have hb : x' ∈ A ∧ y' ∈ B := by
      rw [← productPoint_mem_product, ← hAB]
      exact right_mem_segment ℝ _ _
    rw [edge_dimension he] at hd
    have hz : affineDimension A = 0 ∨ affineDimension B = 0 := by omega
    rcases hz with hz | hz
    · obtain ⟨u, hu⟩ := nonempty_affineDimension_zero_singleton hAn hz
      have hxx : x = x' := by rw [hu] at ha hb; exact ha.1.trans hb.1.symm
      subst x'
      refine Or.inr ⟨rfl, hv.1, ?_⟩
      have hf := product_right_slice_face (finitePolytope_convex hQ) hv.1
      exact embedding_edge_reflect (productRightSlice x)
        ((edge_face_iff hPQ hf ⟨y, hv.2.1, rfl⟩ ⟨y', hw.2.1, rfl⟩).mp he)
    · obtain ⟨u, hu⟩ := nonempty_affineDimension_zero_singleton hBn hz
      have hyy : y = y' := by rw [hu] at ha hb; exact ha.2.trans hb.2.symm
      subst y'
      refine Or.inl ⟨rfl, hv.2, ?_⟩
      have hf := product_left_slice_face (finitePolytope_convex hP) hv.2
      exact embedding_edge_reflect (productLeftSlice y)
        ((edge_face_iff hPQ hf ⟨x, hv.1.1, rfl⟩ ⟨x', hw.1.1, rfl⟩).mp he)
  · rintro (⟨rfl, hy, he⟩ | ⟨rfl, hx, he⟩)
    · exact (edge_face_iff hPQ (product_left_slice_face (finitePolytope_convex hP) hy)
        ⟨x, he.1.1, rfl⟩ ⟨x', he.2.1.1, rfl⟩).mpr
        (embedding_edge_image (productLeftSlice y) he)
    · exact (edge_face_iff hPQ (product_right_slice_face (finitePolytope_convex hQ) hx)
        ⟨y, he.1.1, rfl⟩ ⟨y', he.2.1.1, rfl⟩).mpr
        (embedding_edge_image (productRightSlice x) he)

end Uniform5.Composition
