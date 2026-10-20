import Uniform5.CompositionProductPolygonFaces
import Mathlib.Analysis.Convex.Combination

/-! Metric congruence of Euclidean products and the square-factor identity
needed to express a prism over a polygonal prism as a duoprism. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical
open scoped RealInnerProductSpace

/-- Joining coordinates is a linear map even when its source carries the
ordinary pair norm; only its algebra is used for convex hulls. -/
noncomputable def productJoinLinear {a b : ℕ} :
    (Space a × Space b) →ₗ[ℝ] EuclideanSpace ℝ (Fin a ⊕ Fin b) where
  toFun z := productPoint z.1 z.2
  map_add' := by intro x y; ext i; cases i <;> simp [productPoint]
  map_smul' := by intro t x; ext i; cases i <;> simp [productPoint]

theorem product_eq_join_image {a b : ℕ} (P : Set (Space a)) (Q : Set (Space b)) :
    product P Q = productJoinLinear '' (P ×ˢ Q) := by
  ext z
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩

/-- Euclidean products commute with taking both finite convex hulls. -/
theorem product_convexHull {a b : ℕ} (P : Set (Space a)) (Q : Set (Space b)) :
    product (convexHull ℝ P) (convexHull ℝ Q) = convexHull ℝ (product P Q) := by
  rw [product_eq_join_image, ← convexHull_prod, product_eq_join_image]
  exact productJoinLinear.toAffineMap.image_convexHull _

/-- Factorwise whole-set congruences preserve the Euclidean product metric. -/
theorem congruent_product {a b c d : ℕ} {P : Set (Space a)} {Q : Set (Space b)}
    {P' : Set (Space c)} {Q' : Set (Space d)} (hP : Congruent P P') (hQ : Congruent Q Q') :
    Congruent (product P Q) (product P' Q') := by
  obtain ⟨f⟩ := hP
  obtain ⟨g⟩ := hQ
  let e := (productEquiv P Q).symm.trans
    ((f.toEquiv.prodCongr g.toEquiv).trans (productEquiv P' Q'))
  refine ⟨{ toEquiv := e, isometry_toFun := Isometry.of_dist_eq ?_ }⟩
  intro x y
  obtain ⟨p, rfl⟩ := (productEquiv P Q).surjective x
  obtain ⟨q, rfl⟩ := (productEquiv P Q).surjective y
  have he (p : P × Q) : e (productEquiv P Q p) = productEquiv P' Q' (f p.1, g p.2) := by
    simp [e, Prod.map]
  change dist (e (productEquiv P Q p)).val (e (productEquiv P Q q)).val =
    dist (productEquiv P Q p).val (productEquiv P Q q).val
  rw [he, he]
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  change dist (productPoint (f p.1).val (g p.2).val) (productPoint (f q.1).val (g q.2).val) ^ 2 =
    dist (productPoint p.1.val p.2.val) (productPoint q.1.val q.2.val) ^ 2
  rw [productPoint_dist_sq, productPoint_dist_sq]
  have hf := f.dist_eq p.1 q.1
  have hg := g.dist_eq p.2 q.2
  simp only [Subtype.dist_eq] at hf hg
  rw [hf, hg]

/-- The standard sum-of-finite-indices reindexing into a single Euclidean space. -/
noncomputable def flattenProduct (a b : ℕ) :
    EuclideanSpace ℝ (Fin a ⊕ Fin b) ≃ᵃⁱ[ℝ] Space (a + b) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv).toAffineIsometryEquiv

/-- Parenthesization of an orthogonal product changes no intrinsic distances. -/
theorem congruent_product_assoc {a b c : ℕ}
    (P : Set (Space a)) (Q : Set (Space b)) (R : Set (Space c)) :
    Congruent
      (product (flattenProduct a b '' product P Q) R)
      (product P (flattenProduct b c '' product Q R)) := by
  let f := flattenProduct a b
  let g := flattenProduct b c
  let ef := (productEquiv P Q).trans (Equiv.Set.image f (product P Q) f.injective)
  let eg := (productEquiv Q R).trans (Equiv.Set.image g (product Q R) g.injective)
  let el := (ef.prodCongr (Equiv.refl R)).trans (productEquiv (f '' product P Q) R)
  let er := ((Equiv.refl P).prodCongr eg).trans (productEquiv P (g '' product Q R))
  let e := el.symm.trans ((Equiv.prodAssoc P Q R).trans er)
  refine ⟨{ toEquiv := e, isometry_toFun := Isometry.of_dist_eq ?_ }⟩
  intro x y
  obtain ⟨p, rfl⟩ := el.surjective x
  obtain ⟨q, rfl⟩ := el.surjective y
  have he (p : (P × Q) × R) : e (el p) = er (p.1.1, p.1.2, p.2) := by simp [e]
  change dist (e (el p)).val (e (el q)).val = dist (el p).val (el q).val
  rw [he, he]
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  change dist (productPoint p.1.1.val (g (productPoint p.1.2.val p.2.val)))
      (productPoint q.1.1.val (g (productPoint q.1.2.val q.2.val))) ^ 2 =
    dist (productPoint (f (productPoint p.1.1.val p.1.2.val)) p.2.val)
      (productPoint (f (productPoint q.1.1.val q.1.2.val)) q.2.val) ^ 2
  rw [productPoint_dist_sq, productPoint_dist_sq, f.dist_map, g.dist_map,
    productPoint_dist_sq, productPoint_dist_sq, add_assoc]

/-- A rigidly rotated and translated unit Cartesian square. -/
noncomputable def intervalSquareMap :
    EuclideanSpace ℝ (Fin 1 ⊕ Fin 1) →ᵃⁱ[ℝ] Plane where
  toFun x := !₂[(x (Sum.inl 0) - x (Sum.inr 0)) / Real.sqrt 2,
    (x (Sum.inl 0) + x (Sum.inr 0) - 1) / Real.sqrt 2]
  linear := {
    toFun x := !₂[(x (Sum.inl 0) - x (Sum.inr 0)) / Real.sqrt 2,
      (x (Sum.inl 0) + x (Sum.inr 0)) / Real.sqrt 2]
    map_add' := by intro x y; ext i; fin_cases i <;> simp <;> ring
    map_smul' := by intro t x; ext i; fin_cases i <;> simp <;> ring }
  map_vadd' := by intro x y; ext i; fin_cases i <;> simp [vadd_eq_add] <;> ring
  norm_map x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, Fintype.sum_sum_type,
      Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, WithLp.equiv_symm_pi_apply]
    have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp
    nlinarith

theorem unitSquare_vertices :
    polygonPoint 4 (unitPolygonRadius 4) 0 = !₂[1 / Real.sqrt 2, 0] ∧
    polygonPoint 4 (unitPolygonRadius 4) 1 = !₂[0, 1 / Real.sqrt 2] ∧
    polygonPoint 4 (unitPolygonRadius 4) 2 = !₂[-(1 / Real.sqrt 2), 0] ∧
    polygonPoint 4 (unitPolygonRadius 4) 3 = !₂[0, -(1 / Real.sqrt 2)] := by
  have hr : unitPolygonRadius 4 = 1 / Real.sqrt 2 := by
    unfold unitPolygonRadius
    norm_num only [Nat.cast_ofNat]
    rw [Real.sin_pi_div_four]
    ring
  have h1 : 2 * Real.pi / 4 = Real.pi / 2 := by ring
  have h2 : 2 * Real.pi * (2 : ℝ) / 4 = Real.pi := by ring
  have h3 : 2 * Real.pi * (3 : ℝ) / 4 = Real.pi + Real.pi / 2 := by ring
  have hthree : ((3 : Fin 4) : ℕ) = 3 := rfl
  norm_num [polygonPoint, hr, h1, h2, h3, hthree, Real.sin_add, Real.cos_add]

/-- The four interval-product corners are exactly the standard square's vertices. -/
theorem intervalSquareMap_corners :
    intervalSquareMap '' product ({0, !₂[1]} : Set (Space 1)) ({0, !₂[1]} : Set (Space 1)) =
      range (polygonPoint 4 (unitPolygonRadius 4)) := by
  obtain ⟨h0, h1, h2, h3⟩ := unitSquare_vertices
  have h00 : intervalSquareMap (productPoint (0 : Space 1) (0 : Space 1)) =
      polygonPoint 4 (unitPolygonRadius 4) 3 := by
    rw [h3]
    change !₂[(0 - 0) / Real.sqrt 2, (0 + 0 - 1) / Real.sqrt 2] = _
    ext i; fin_cases i <;> simp [neg_div]
  have h01 : intervalSquareMap (productPoint (0 : Space 1) !₂[1]) =
      polygonPoint 4 (unitPolygonRadius 4) 2 := by
    rw [h2]
    change !₂[(0 - 1) / Real.sqrt 2, (0 + 1 - 1) / Real.sqrt 2] = _
    ext i; fin_cases i <;> simp [neg_div]
  have h10 : intervalSquareMap (productPoint (!₂[1] : Space 1) (0 : Space 1)) =
      polygonPoint 4 (unitPolygonRadius 4) 0 := by
    rw [h0]
    change !₂[(1 - 0) / Real.sqrt 2, (1 + 0 - 1) / Real.sqrt 2] = _
    ext i; fin_cases i <;> simp [neg_div]
  have h11 : intervalSquareMap (productPoint (!₂[1] : Space 1) !₂[1]) =
      polygonPoint 4 (unitPolygonRadius 4) 1 := by
    rw [h1]
    change !₂[(1 - 1) / Real.sqrt 2, (1 + 1 - 1) / Real.sqrt 2] = _
    ext i; fin_cases i <;> norm_num
  ext x
  constructor
  · rintro ⟨z, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact ⟨3, h00.symm⟩
    · have := mem_singleton_iff.mp hb; subst b; exact ⟨2, h01.symm⟩
    · have := mem_singleton_iff.mp ha; subst a; exact ⟨0, h10.symm⟩
    · have := mem_singleton_iff.mp ha; subst a
      have := mem_singleton_iff.mp hb; subst b
      exact ⟨1, h11.symm⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact ⟨_, ⟨!₂[1], by simp, 0, by simp, rfl⟩, h10⟩
    · exact ⟨_, ⟨!₂[1], by simp, !₂[1], by simp, rfl⟩, h11⟩
    · exact ⟨_, ⟨0, by simp, !₂[1], by simp, rfl⟩, h01⟩
    · exact ⟨_, ⟨0, by simp, 0, by simp, rfl⟩, h00⟩

/-- Cartesian products of unit intervals are congruent to the concrete unit square. -/
theorem congruent_interval_product_square :
    Congruent (product unitInterval unitInterval) (unitPolygon 4) := by
  have hI : unitInterval = convexHull ℝ ({0, !₂[1]} : Set (Space 1)) :=
    (convexHull_pair 0 !₂[1]).symm
  have himage : intervalSquareMap '' product unitInterval unitInterval = unitPolygon 4 := by
    rw [hI, product_convexHull]
    change intervalSquareMap.toAffineMap '' convexHull ℝ _ = _
    rw [intervalSquareMap.toAffineMap.image_convexHull]
    change convexHull ℝ (intervalSquareMap '' product _ _) = _
    rw [intervalSquareMap_corners]
    rfl
  rw [← himage]
  exact congruent_affineIsometry_image intervalSquareMap _

/-- A prism over a polygonal prism is the polygon-square duoprism, with
all factors interpreted as the concrete Euclidean convex bodies. -/
theorem congruent_prism_over_polygonPrism {Q : Set (Space 3)} {n : ℕ}
    (hQ : Congruent Q (polygonPrismModel n)) :
    Congruent (polyhedralPrismModel Q) (duoprismModel n 4) := by
  have hQ' : Congruent Q (flattenProduct 2 1 '' product (unitPolygon n) unitInterval) :=
    congruent_trans hQ (congruent_affineIsometry_image (flattenProduct 2 1).toAffineIsometry _)
  have hS : Congruent (flattenProduct 1 1 '' product unitInterval unitInterval)
      (unitPolygon 4) := congruent_trans
    (congruent_symm (congruent_affineIsometry_image (flattenProduct 1 1).toAffineIsometry _))
    congruent_interval_product_square
  exact congruent_trans (congruent_product hQ' (congruent_refl unitInterval))
    (congruent_trans (congruent_product_assoc (unitPolygon n) unitInterval unitInterval)
      (congruent_product (congruent_refl (unitPolygon n)) hS))

end Uniform5.Composition
