import Uniform5.CompositionFamilies
import Uniform5.CompositionEmbeddingReverse
import Uniform5.CompositionUniformFaces
import Uniform5.CompositionPolygonUnit
import Uniform5.CaseBProducts

/-!
# Orthogonal sums and the concrete product families

The Case B reconstruction produces an orthogonal Minkowski sum. These
lemmas identify that sum with the Euclidean product used in K2/K3, retaining
the sum-of-squares metric rather than the ordinary pair's maximum metric.
-/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped Pointwise

noncomputable def productEquiv {a b : ℕ} (P : Set (Space a)) (Q : Set (Space b)) :
    (P × Q) ≃ product P Q :=
  Equiv.ofBijective
    (fun p => ⟨productPoint p.1.val p.2.val, p.1.val, p.1.property,
      p.2.val, p.2.property, rfl⟩)
    ⟨by
      intro p q hpq
      have h := congrArg Subtype.val hpq
      apply Prod.ext
      · apply Subtype.ext
        ext i
        exact congrArg (fun z => z (Sum.inl i)) h
      · apply Subtype.ext
        ext i
        exact congrArg (fun z => z (Sum.inr i)) h,
    by
      intro z
      obtain ⟨x, hx, y, hy, hz⟩ := z.property
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), Subtype.ext hz.symm⟩⟩

/-- Swapping the orthogonal factors preserves the Euclidean product metric. -/
theorem congruent_product_swap {a b : ℕ} (U : Set (Space a)) (V : Set (Space b)) :
    Congruent (product U V) (product V U) := by
  let e : product U V ≃ product V U := (productEquiv U V).symm.trans
    ((Equiv.prodComm U V).trans (productEquiv V U))
  refine ⟨{ toEquiv := e, isometry_toFun := Isometry.of_dist_eq ?_ }⟩
  intro x y
  obtain ⟨p, rfl⟩ := (productEquiv U V).surjective x
  obtain ⟨q, rfl⟩ := (productEquiv U V).surjective y
  have he (p : U × V) : e (productEquiv U V p) = productEquiv V U (p.2, p.1) := by
    simp [e, Prod.swap]
  change dist (e (productEquiv U V p)) (e (productEquiv U V q)) = _
  rw [he, he]
  change dist (productPoint p.2.val p.1.val) (productPoint q.2.val q.1.val) =
    dist (productPoint p.1.val p.2.val) (productPoint q.1.val q.2.val)
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [productPoint_dist_sq, productPoint_dist_sq, add_comm]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The existing orthogonal-sum distance law gives whole-set congruence
with the concrete coordinate product whenever each factor has its model. -/
theorem congruent_orthogonal_sum_product {C X : Set E}
    (hX : X ⊆ CaseB.normals C) {a b : ℕ}
    {U : Set (Space a)} {V : Set (Space b)}
    (hC : Congruent C U) (hV : Congruent X V) :
    Congruent (C + X) (product U V) := by
  obtain ⟨f⟩ := hC
  obtain ⟨g⟩ := hV
  let e : product U V ≃ (C + X : Set E) :=
    (productEquiv U V).symm.trans
      ((f.symm.toEquiv.prodCongr g.symm.toEquiv).trans (CaseB.sumEquiv C X hX))
  apply congruent_symm
  refine ⟨{ toEquiv := e, isometry_toFun := Isometry.of_dist_eq ?_ }⟩
  intro x y
  obtain ⟨p, rfl⟩ := (productEquiv U V).surjective x
  obtain ⟨q, rfl⟩ := (productEquiv U V).surjective y
  have he (p : U × V) :
      (e (productEquiv U V p)).val = (f.symm p.1).val + (g.symm p.2).val := by
    simp [e, CaseB.sumEquiv]
  change dist (e (productEquiv U V p)).val (e (productEquiv U V q)).val =
    dist (productEquiv U V p).val (productEquiv U V q).val
  rw [he, he]
  apply (sq_eq_sq₀ (dist_nonneg) (dist_nonneg)).mp
  rw [CaseB.sum_dist_sq hX (f.symm p.1).property (f.symm q.1).property
    (g.symm p.2).property (g.symm q.2).property]
  change _ = dist (productPoint p.1.val p.2.val) (productPoint q.1.val q.2.val) ^ 2
  rw [productPoint_dist_sq]
  have hf := f.symm.dist_eq p.1 q.1
  have hg := g.symm.dist_eq p.2 q.2
  simp only [Subtype.dist_eq] at hf hg
  rw [hf, hg]

/-- A slice over an extreme point of one factor is an actual face of the
orthogonal sum. This uses extremity and injectivity of addition directly. -/
theorem orthogonal_sum_vertex_slice {C X : Set E}
    (hC : Convex ℝ C) (hV : Convex ℝ X) (hX : X ⊆ CaseB.normals C)
    {c : E} (hc : c ∈ C.extremePoints ℝ) :
    IsConvexFace (C + X) (({c} : Set E) + X) := by
  refine ⟨(convex_singleton c).add hV, ?_, ?_⟩
  · exact Set.add_subset_add (singleton_subset_iff.mpr hc.1) (Subset.refl X)
  · rintro a ha b hb z hz hs
    obtain ⟨aC, haC, aX, haX, rfl⟩ := Set.mem_add.mp ha
    obtain ⟨bC, hbC, bX, hbX, rfl⟩ := Set.mem_add.mp hb
    obtain ⟨c', hc', zX, hzX, rfl⟩ := Set.mem_add.mp hz
    have hc'eq : c' = c := hc'
    subst c'
    obtain ⟨s, t, hs, ht, hst, heq⟩ := hs
    have hsum : (s • aC + t • bC) + (s • aX + t • bX) = c + zX := by
      calc
        _ = s • (aC + aX) + t • (bC + bX) := by module
        _ = c + zX := heq
    have hinj := CaseB.sum_injOn hX
      (show (s • aC + t • bC, s • aX + t • bX) ∈ C ×ˢ X from
        ⟨hC haC hbC hs.le ht.le hst, hV haX hbX hs.le ht.le hst⟩)
      (show (c, zX) ∈ C ×ˢ X from ⟨hc.1, hzX⟩) hsum
    obtain ⟨haeq, hbeq⟩ := hc.2 haC hbC ⟨s, t, hs, ht, hst, congrArg Prod.fst hinj⟩
    constructor
    · exact Set.mem_add.mpr ⟨aC, haeq, aX, haX, rfl⟩
    · exact Set.mem_add.mpr ⟨bC, hbeq, bX, hbX, rfl⟩

/-- A factor slice is a translated copy of the actual factor. -/
theorem singleton_add_eq_translation (c : E) (X : Set E) :
    ({c} : Set E) + X = (AffineIsometryEquiv.constVAdd ℝ E c) '' X := by
  ext x
  constructor
  · rintro ⟨y, rfl, z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact Set.mem_add.mpr ⟨c, rfl, z, hz, rfl⟩

/-- Unit uniformity of a reconstructed factor is inherited from the parent
via an actual face. It is not supplied as a classification premise. -/
theorem unitUniform_orthogonal_factor [FiniteDimensional ℝ E]
    {n d : ℕ} {C X : Set E} (hP : UnitUniform (n + 3) (C + X))
    (hC : FinitePolytope C) (hV : FinitePolytope X)
    (hX : X ⊆ CaseB.normals C) (hd : affineDimension X = d) :
    UnitUniform d X := by
  obtain ⟨c, hc⟩ := finitePolytope_extremePoints_nonempty hC
  have hface := orthogonal_sum_vertex_slice (finitePolytope_convex hC)
    (finitePolytope_convex hV) hX hc
  have hne : (({c} : Set E) + X).Nonempty := by
    obtain ⟨x, hx⟩ := finitePolytope_nonempty hV
    exact ⟨c + x, Set.mem_add.mpr ⟨c, rfl, x, hx, rfl⟩⟩
  have hU := unitUniform_all_faces hP hface hne
  rw [singleton_add_eq_translation, affineDimension_image, hd] at hU
  have hh := unitUniform_image (AffineIsometryEquiv.constVAdd ℝ E c).symm hU
  simpa only [affineIsometry_symm_image_image] using hh

/-- Once reconstruction gives a unit polygon factor and a genuine uniform
three-dimensional factor, the conclusion is exactly the paper's K3. -/
theorem orthogonal_sum_mem_K3 [FiniteDimensional ℝ E] {C X : Set E}
    (hX : X ⊆ CaseB.normals C) (hC : UnitUniform 2 C) (hU : UnitUniform 3 X) :
    K3 (C + X) := by
  obtain ⟨n, hn, f, hf⟩ := unitUniform_two_unitPolygon hC
  obtain ⟨_, Q, _, hQX, hQ⟩ := exists_unitUniform_intrinsic_model (n := 0) hU
  have hCU : Congruent C (unitPolygon n) := by
    rw [hf]
    exact congruent_symm (congruent_affineIsometry_image f _)
  exact ⟨n, hn, Q, hQ, congruent_orthogonal_sum_product hX hCU (congruent_symm hQX)⟩

/-- The Case B cell-first order also gives K3; swapping factors is a proved
congruence, not an implicit change from the maximum to the Euclidean norm. -/
theorem orthogonal_sum_mem_K3_swapped [FiniteDimensional ℝ E] {C X : Set E}
    (hX : X ⊆ CaseB.normals C) (hC : UnitUniform 3 C) (hU : UnitUniform 2 X) :
    K3 (C + X) := by
  obtain ⟨n, hn, f, hf⟩ := unitUniform_two_unitPolygon hU
  obtain ⟨_, Q, _, hQC, hQ⟩ := exists_unitUniform_intrinsic_model (n := 0) hC
  have hXU : Congruent X (unitPolygon n) := by
    rw [hf]
    exact congruent_symm (congruent_affineIsometry_image f _)
  exact ⟨n, hn, Q, hQ, congruent_trans
    (congruent_orthogonal_sum_product hX (congruent_symm hQC) hXU)
    (congruent_product_swap Q (unitPolygon n))⟩

/-- In a five-dimensional reconstruction with a uniform three-cell and a
two-dimensional offset hull, the offset's uniformity follows from the
parent and the final conclusion is the concrete K3 family. -/
theorem orthogonal_cell_sum_mem_K3 [FiniteDimensional ℝ E] {C X : Set E}
    (hP : UnitUniform 5 (C + X)) (hC : UnitUniform 3 C)
    (hV : FinitePolytope X) (hX : X ⊆ CaseB.normals C)
    (hd : affineDimension X = 2) : K3 (C + X) :=
  orthogonal_sum_mem_K3_swapped hX hC (unitUniform_orthogonal_factor (n := 2) hP
    (uniform_finitePolytope hC.1) hV hX hd)

end Uniform5.Composition
