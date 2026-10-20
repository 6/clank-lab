import Uniform5.CompositionProductModels

/-!
# Dimensions of actual orthogonal Minkowski sums

The direction of a nonempty Minkowski sum is the sum of the two direction
spaces. Normal offsets make these spaces orthogonal, so their dimensions
add. A three-cell factor in a five-dimensional uniform polytope therefore
has a two-dimensional offset factor, with no separate rank assumption.
-/

noncomputable section
namespace Uniform5.Composition
open Set
open scoped Pointwise RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The normal space used by the Case B reconstruction is precisely the
orthogonal complement of the actual cell's affine direction space. -/
theorem normals_eq_direction_orthogonal (C : Set E) :
    CaseB.normals C = (affineSpan ℝ C).directionᗮ := by
  ext d
  constructor
  · intro hd
    apply (Submodule.mem_orthogonal _ _).mpr
    intro x hx
    rw [direction_affineSpan, vectorSpan_def] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      exact hd a ha b hb
    | zero => simp
    | add x y hx hy ihx ihy => simp only [inner_add_left, ihx, ihy, add_zero]
    | smul a x hx ih => simp only [real_inner_smul_left, ih, mul_zero]
  · intro hd a ha b hb
    apply (Submodule.mem_orthogonal _ _).mp hd
    rw [direction_affineSpan]
    exact vsub_mem_vectorSpan ℝ ha hb

/-- Nonempty actual Minkowski sums have the sum of the affine directions,
without requiring convexity, finiteness, or orthogonality. -/
theorem direction_minkowski_sum {C X : Set E} (hC : C.Nonempty) (hX : X.Nonempty) :
    (affineSpan ℝ (C + X)).direction =
      (affineSpan ℝ C).direction ⊔ (affineSpan ℝ X).direction := by
  simp only [direction_affineSpan]
  apply le_antisymm
  · rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro z ⟨a, ha, b, hb, rfl⟩
    obtain ⟨c, hc, x, hx, rfl⟩ := Set.mem_add.mp ha
    obtain ⟨d, hd, y, hy, rfl⟩ := Set.mem_add.mp hb
    have hc' : c - d ∈ vectorSpan ℝ C ⊔ vectorSpan ℝ X :=
      (show vectorSpan ℝ C ≤ vectorSpan ℝ C ⊔ vectorSpan ℝ X from le_sup_left)
        (vsub_mem_vectorSpan ℝ hc hd)
    have hx' : x - y ∈ vectorSpan ℝ C ⊔ vectorSpan ℝ X :=
      (show vectorSpan ℝ X ≤ vectorSpan ℝ C ⊔ vectorSpan ℝ X from le_sup_right)
        (vsub_mem_vectorSpan ℝ hx hy)
    have heq : (c + x) - (d + y) = (c - d) + (x - y) := by abel
    change (c + x) - (d + y) ∈ _
    rw [heq]
    exact Submodule.add_mem _ hc' hx'
  · apply sup_le
    · rw [vectorSpan_def]
      apply Submodule.span_le.mpr
      rintro z ⟨c, hc, d, hd, rfl⟩
      obtain ⟨x, hx⟩ := hX
      have hh := vsub_mem_vectorSpan ℝ
        (show c + x ∈ C + X from Set.mem_add.mpr ⟨c, hc, x, hx, rfl⟩)
        (show d + x ∈ C + X from Set.mem_add.mpr ⟨d, hd, x, hx, rfl⟩)
      simpa only [vsub_eq_sub, add_sub_add_right_eq_sub] using hh
    · rw [vectorSpan_def]
      apply Submodule.span_le.mpr
      rintro z ⟨x, hx, y, hy, rfl⟩
      obtain ⟨c, hc⟩ := hC
      have hh := vsub_mem_vectorSpan ℝ
        (show c + x ∈ C + X from Set.mem_add.mpr ⟨c, hc, x, hx, rfl⟩)
        (show c + y ∈ C + X from Set.mem_add.mpr ⟨c, hc, y, hy, rfl⟩)
      simpa only [vsub_eq_sub, add_sub_add_left_eq_sub] using hh

/-- The direction of a set of normal offsets remains normal. -/
theorem normal_offsets_direction_le {C X : Set E} (hX : X ⊆ CaseB.normals C) :
    (affineSpan ℝ X).direction ≤ (affineSpan ℝ C).directionᗮ := by
  rw [← normals_eq_direction_orthogonal, direction_affineSpan, vectorSpan_def]
  apply Submodule.span_le.mpr
  rintro z ⟨x, hx, y, hy, rfl⟩
  exact (CaseB.normals C).sub_mem (hX hx) (hX hy)

/-- Orthogonal Minkowski factors have additive affine dimensions. This is
stronger than the finite-polytope case: any nonempty factors suffice. -/
theorem affineDimension_orthogonal_sum [FiniteDimensional ℝ E]
    {C X : Set E} (hC : C.Nonempty) (hV : X.Nonempty)
    (hX : X ⊆ CaseB.normals C) :
    affineDimension (C + X) = affineDimension C + affineDimension X := by
  have hd : Disjoint (affineSpan ℝ C).direction (affineSpan ℝ X).direction :=
    (affineSpan ℝ C).direction.orthogonal_disjoint.mono_right (normal_offsets_direction_le hX)
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (affineSpan ℝ C).direction (affineSpan ℝ X).direction
  rw [hd.eq_bot, finrank_bot, add_zero] at h
  unfold affineDimension Uniform5.affineDimension
  rw [direction_minkowski_sum hC hV]
  exact h

/-- A unit uniform five-dimensional sum with a unit uniform three-cell
has a genuinely two-dimensional offset factor. -/
theorem orthogonal_cell_offset_dimension [FiniteDimensional ℝ E]
    {C X : Set E} (hP : UnitUniform 5 (C + X)) (hC : UnitUniform 3 C)
    (hV : FinitePolytope X) (hX : X ⊆ CaseB.normals C) :
    affineDimension X = 2 := by
  have h := affineDimension_orthogonal_sum
    (finitePolytope_nonempty (uniform_finitePolytope hC.1)) (finitePolytope_nonempty hV) hX
  rw [uniform_dimension hP.1, uniform_dimension hC.1] at h
  omega

/-- The actual K3 product conclusion without a supplied offset dimension. -/
theorem orthogonal_cell_sum_mem_K3_of_unitUniform [FiniteDimensional ℝ E]
    {C X : Set E} (hP : UnitUniform 5 (C + X)) (hC : UnitUniform 3 C)
    (hV : FinitePolytope X) (hX : X ⊆ CaseB.normals C) : K3 (C + X) :=
  orthogonal_cell_sum_mem_K3 hP hC hV hX (orthogonal_cell_offset_dimension hP hC hV hX)

/-- The proved Case B local-to-global cell reconstruction now ends in K3
without any assumption about offset rank or offset uniformity. -/
theorem cellSystem_mem_K3 [FiniteDimensional ℝ E] (D : CaseB.CellSystem E)
    {r : E} (hr : r ∈ D.vertices)
    (hP : UnitUniform 5 (convexHull ℝ D.vertices))
    (hC : UnitUniform 3 (convexHull ℝ (D.cell r))) :
    K3 (convexHull ℝ D.vertices) := by
  classical
  have hV : FinitePolytope (convexHull ℝ (D.offsets hr)) :=
    ⟨(D.offsets_finite hr).toFinset,
      (D.offsets_finite hr).toFinset_nonempty.mpr (D.offsets_nonempty hr),
      by rw [Set.Finite.coe_toFinset]⟩
  rw [D.convexHull_eq_cell_add_offsets hr] at hP ⊢
  exact orthogonal_cell_sum_mem_K3_of_unitUniform hP hC hV
    (CaseB.convexHull_normal_subset (D.offsets_normal hr))

end Uniform5.Composition
