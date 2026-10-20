import Uniform5.CompositionProductEdges
import Uniform5.CompositionActualCellProducts

/-! Whole coordinate slices of a product are orthogonal translates.
A single affine isometric embedding transports this full-set assertion. -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem embedding_translate (f : E →ᵃⁱ[ℝ] F) (C : Set E) (d : E) :
    f '' CaseB.translate C d = CaseB.translate (f '' C) (f.linearIsometry d) := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨f x, ⟨x, hx, rfl⟩, ?_⟩
    have h := f.map_vadd x d
    simpa [vadd_eq_add, add_comm] using h.symm
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x + d, ⟨x, hx, rfl⟩, ?_⟩
    have h := f.map_vadd x d
    simpa [vadd_eq_add, add_comm] using h

theorem embedding_mem_normals (f : E →ᵃⁱ[ℝ] F) {C : Set E} {d : E}
    (hd : d ∈ CaseB.normals C) : f.linearIsometry d ∈ CaseB.normals (f '' C) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [show f a - f b = f.linearIsometry (a - b) from (f.map_vsub a b).symm,
    f.linearIsometry.inner_map_map]
  exact hd a ha b hb

theorem product_slice_translate {a b : ℕ} (C : Set (Space a)) (y z : Space b) :
    product C {z} = CaseB.translate (product C {y}) (productPoint 0 (z - y)) := by
  ext w
  constructor
  · rintro ⟨x, hx, z', hz, rfl⟩
    have hz' : z' = z := hz
    subst z'
    refine ⟨productPoint x y, ⟨x, hx, y, rfl, rfl⟩, ?_⟩
    ext i
    cases i <;> simp [productPoint]
  · rintro ⟨_, ⟨x, hx, y', hy, rfl⟩, rfl⟩
    have hy' : y' = y := hy
    subst y'
    refine ⟨x, hx, z, rfl, ?_⟩
    ext i
    cases i <;> simp [productPoint]

theorem product_slice_offset_normal {a b : ℕ} (C : Set (Space a)) (y z : Space b) :
    productPoint 0 (z - y) ∈ CaseB.normals (product C {y}) := by
  rintro _ ⟨x, hx, y', hy, rfl⟩ _ ⟨x', hx', y'', hy', rfl⟩
  have h1 : y' = y := hy
  have h2 : y'' = y := hy'
  subst y'
  subst y''
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fintype.sum_sum_type, productPoint]

/-- A full embedded slice at a new factor vertex is an orthogonal
translate of the old slice; no reconstruction or uniformity is assumed. -/
theorem embedding_product_slice_transport {a b : ℕ}
    (f : EuclideanSpace ℝ (Fin a ⊕ Fin b) →ᵃⁱ[ℝ] E)
    (C : Set (Space a)) (y z : Space b) :
    ∃ d ∈ CaseB.normals (f '' product C {y}),
      f '' product C {z} = CaseB.translate (f '' product C {y}) d := by
  refine ⟨f.linearIsometry (productPoint 0 (z - y)),
    embedding_mem_normals f (product_slice_offset_normal C y z), ?_⟩
  rw [product_slice_translate C y z, embedding_translate]

end Uniform5.Composition
