import Uniform5.CompositionModelIncidence
import Uniform5.CompositionPolyhedronModels
import Uniform5.CompositionProductModels

/-! Actual polygon occurrences in the concrete prism, antiprism, and
polygon-product models, and the resulting bounds on their parameters. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical
open scoped RealInnerProductSpace

/-- The literal isometric inclusion of one factor at a fixed point of the other. -/
noncomputable def productLeftSlice {a b : ℕ} (y : Space b) :
    Space a →ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin a ⊕ Fin b) where
  toFun x := productPoint x y
  linear := {
    toFun x := productPoint x 0
    map_add' := by intro x z; ext i; cases i <;> simp [productPoint]
    map_smul' := by intro t x; ext i; cases i <;> simp [productPoint] }
  map_vadd' := by intro x z; ext i; cases i <;> simp [productPoint, vadd_eq_add]
  norm_map x := by simp [productPoint, EuclideanSpace.norm_eq, Fintype.sum_sum_type]

/-- A factor slice over an actual extreme point is an actual geometric face. -/
theorem product_left_slice_face {a b : ℕ} {P : Set (Space a)} {Q : Set (Space b)}
    (hP : Convex ℝ P) {y : Space b} (hy : y ∈ Q.extremePoints ℝ) :
    IsConvexFace (product P Q) (productLeftSlice y '' P) := by
  refine ⟨hP.affine_image (productLeftSlice y).toAffineMap, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, y, hy.1, rfl⟩
  · rintro z ⟨zx, hzx, zy, hzy, rfl⟩ w ⟨wx, hwx, wy, hwy, rfl⟩ t ⟨tx, htx, rfl⟩ hs
    obtain ⟨s, r, hs, hr, hsr, heq⟩ := hs
    have hey : s • zy + r • wy = y := by
      ext i
      have hh := congrArg (fun z : EuclideanSpace ℝ (Fin a ⊕ Fin b) => z (Sum.inr i)) heq
      simpa [productLeftSlice, productPoint] using hh
    obtain ⟨hzy', hwy'⟩ := hy.2 hzy hwy ⟨s, r, hs, hr, hsr, hey⟩
    exact ⟨⟨zx, hzx, by change productPoint zx y = productPoint zx zy; rw [hzy']⟩,
      ⟨wx, hwx, by change productPoint wx y = productPoint wx wy; rw [hwy']⟩⟩

/-- Actual polygon faces of a factor persist in every extreme-point slice. -/
theorem product_left_polygonFace {a b k : ℕ} {P G : Set (Space a)} {Q : Set (Space b)}
    (hP : Convex ℝ P) (hG : PolygonFace P G k) {y : Space b}
    (hy : y ∈ Q.extremePoints ℝ) :
    PolygonFace (product P Q) (productLeftSlice y '' G) k := by
  have hh := embedding_polygonFace_image (productLeftSlice y) hG
  exact ⟨face_of_face (product_left_slice_face hP hy) hh.1, hh.2⟩

/-- The explicit unit polygon is a polygon face of itself with the actual
number of vertices prescribed by its integral parameter. -/
theorem unitPolygon_self_polygonFace {n : ℕ} (hn : 3 ≤ n) :
    PolygonFace (unitPolygon n) (unitPolygon n) n := by
  refine ⟨⟨convex_convexHull ℝ _, IsExtreme.refl ℝ _⟩, ?_,
    polygonVertexFinset n (unitPolygonRadius n),
    polygonVertexFinset_extremePoints n _ (unitPolygonRadius_pos hn).le,
    polygonVertexFinset_card n _ hn (unitPolygonRadius_pos hn)⟩
  unfold affineDimension Uniform5.affineDimension unitPolygon
  rw [affineSpan_polygon_eq_top n _ hn (unitPolygonRadius_pos hn), AffineSubspace.direction_top]
  simp [Space, Plane]

theorem unitPolygon_finitePolytope {n : ℕ} (hn : 3 ≤ n) : FinitePolytope (unitPolygon n) := by
  refine ⟨polygonVertexFinset n (unitPolygonRadius n), ?_, ?_⟩
  · rw [← Finset.card_pos, polygonVertexFinset_card n _ hn (unitPolygonRadius_pos hn)]
    omega
  · rw [polygonVertexFinset_coe]
    rfl

theorem unitInterval_finitePolytope : FinitePolytope unitInterval := by
  refine ⟨{0, !₂[1]}, by simp, ?_⟩
  simp only [Finset.coe_insert, Finset.coe_singleton, convexHull_pair, unitInterval]

/-- Every actual polygon of a polyhedral base occurs in its concrete prism. -/
theorem polyhedralPrism_polygonFace {Q G : Set (Space 3)} {k : ℕ}
    (hQ : Convex ℝ Q) (hG : PolygonFace Q G k) :
    ∃ F, PolygonFace (polyhedralPrismModel Q) F k := by
  obtain ⟨y, hy⟩ := finitePolytope_extremePoints_nonempty unitInterval_finitePolytope
  exact ⟨_, product_left_polygonFace hQ hG hy⟩

/-- Every concrete polygonal prism contains its actual n-gonal base. -/
theorem polygonPrism_polygonFace {n : ℕ} (hn : 3 ≤ n) :
    ∃ F, PolygonFace (polygonPrismModel n) F n := by
  obtain ⟨y, hy⟩ := finitePolytope_extremePoints_nonempty unitInterval_finitePolytope
  exact ⟨_, product_left_polygonFace (convex_convexHull ℝ _) (unitPolygon_self_polygonFace hn) hy⟩

/-- The small-face condition bounds the actual polygonal-prism parameter. -/
theorem polygonPrism_smallFaces_parameter {n : ℕ} (hn : 3 ≤ n)
    (hs : SmallFaces (polygonPrismModel n)) : n ≤ 16 := by
  obtain ⟨F, hF⟩ := polygonPrism_polygonFace hn
  exact hs F n hF

/-- The first regular-polygon factor occurs as an actual duoprism face. -/
theorem duoprism_first_polygonFace {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) :
    ∃ F, PolygonFace (duoprismModel p q) F p := by
  obtain ⟨y, hy⟩ := finitePolytope_extremePoints_nonempty (unitPolygon_finitePolytope hq)
  exact ⟨_, product_left_polygonFace (convex_convexHull ℝ _) (unitPolygon_self_polygonFace hp) hy⟩

/-- An actual horizontal isometric copy of the polygon plane. -/
noncomputable def horizontalPolygonSlice (h : ℝ) : Plane →ᵃⁱ[ℝ] Space 3 where
  toFun x := !₂[x 0, x 1, h]
  linear := {
    toFun x := !₂[x 0, x 1, 0]
    map_add' := by intro x y; ext i; fin_cases i <;> simp
    map_smul' := by intro t x; ext i; fin_cases i <;> simp }
  map_vadd' := by intro x y; ext i; fin_cases i <;> simp [vadd_eq_add]
  norm_map x := by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_succ, Fin.sum_univ_two]

@[simp] theorem horizontalPolygonSlice_polygonPoint (n : ℕ) (i : Fin n) :
    horizontalPolygonSlice (antiprismHeight n / 2) (polygonPoint n (unitPolygonRadius n) i) =
      antiprismPoint n false i := by
  change !₂[(polygonPoint n (unitPolygonRadius n) i) 0,
    (polygonPoint n (unitPolygonRadius n) i) 1, antiprismHeight n / 2] = _
  ext j
  fin_cases j <;> simp [polygonPoint, antiprismPoint]

/-- The third coordinate exposes precisely the unrotated top polygon of
the explicit antiprism. Positive layer separation excludes every bottom point. -/
theorem antiprism_top_face {n : ℕ} (hn : 3 ≤ n) :
    IsConvexFace (antiprismModel n)
      (horizontalPolygonSlice (antiprismHeight n / 2) '' unitPolygon n) := by
  let V := Set.range (fun p : Bool × Fin n => antiprismPoint n p.1 p.2)
  let L : Space 3 →L[ℝ] ℝ := EuclideanSpace.proj 2
  let h := antiprismHeight n / 2
  let T := {x ∈ antiprismModel n | L x = h}
  have hheight : 0 < antiprismHeight n := antiprismHeight_pos hn
  have hpoint (b : Bool) (i : Fin n) : L (antiprismPoint n b i) = if b then -h else h := by
    simp [L, antiprismPoint, h]
  have hbound : ∀ x ∈ antiprismModel n, L x ≤ h := by
    apply convexHull_min _ ((convex_Iic h).linear_preimage L.toLinearMap)
    rintro x ⟨⟨b, i⟩, rfl⟩
    change L (antiprismPoint n b i) ≤ h
    rw [hpoint]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, mem_setOf_eq, mem_Iic]
    · exact le_rfl
    · dsimp [h]; linarith
  let i : Fin n := ⟨0, by omega⟩
  have htop : antiprismPoint n false i ∈ antiprismModel n :=
    subset_convexHull ℝ V ⟨(false, i), rfl⟩
  have hexp : IsExposed ℝ (antiprismModel n) T := by
    intro _
    refine ⟨L, ?_⟩
    ext x
    constructor
    · rintro ⟨hx, heq⟩
      exact ⟨hx, fun y hy => heq ▸ hbound y hy⟩
    · rintro ⟨hx, hmax⟩
      refine ⟨hx, le_antisymm (hbound x hx) ?_⟩
      have hh := hmax _ htop
      simpa only [hpoint, Bool.false_eq_true, ↓reduceIte] using hh
  have hface : IsConvexFace (antiprismModel n) T :=
    ⟨hexp.convex (convex_convexHull ℝ _), hexp.isExtreme⟩
  have hinter : V ∩ T = Set.range (antiprismPoint n false) := by
    ext x
    constructor
    · rintro ⟨⟨⟨b, j⟩, rfl⟩, _, heq⟩
      rw [hpoint] at heq
      cases b
      · exact ⟨j, rfl⟩
      · simp only [↓reduceIte] at heq
        dsimp [h] at heq
        linarith
    · rintro ⟨j, rfl⟩
      exact ⟨⟨(false, j), rfl⟩, subset_convexHull ℝ V ⟨(false, j), rfl⟩,
        by simp only [hpoint, Bool.false_eq_true, ↓reduceIte]⟩
  have hT : T = horizontalPolygonSlice h '' unitPolygon n := by
    rw [face_convexHull_eq hface, hinter]
    change convexHull ℝ (Set.range (antiprismPoint n false)) =
      (horizontalPolygonSlice h).toAffineMap '' convexHull ℝ (Set.range (polygonPoint n (unitPolygonRadius n)))
    rw [(horizontalPolygonSlice h).toAffineMap.image_convexHull]
    congr 1
    ext x
    simp only [mem_range, mem_image]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨polygonPoint n (unitPolygonRadius n) j, ⟨j, rfl⟩,
        horizontalPolygonSlice_polygonPoint n j⟩
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, (horizontalPolygonSlice_polygonPoint n j).symm⟩
  rw [hT] at hface
  exact hface

/-- The top face has exactly n actual extreme points. -/
theorem antiprism_polygonFace {n : ℕ} (hn : 3 ≤ n) :
    ∃ F, PolygonFace (antiprismModel n) F n := by
  have hh := embedding_polygonFace_image (horizontalPolygonSlice (antiprismHeight n / 2))
    (unitPolygon_self_polygonFace hn)
  exact ⟨_, ⟨antiprism_top_face hn, hh.2⟩⟩

theorem antiprism_smallFaces_parameter {n : ℕ} (hn : 3 ≤ n)
    (hs : SmallFaces (antiprismModel n)) : n ≤ 16 := by
  obtain ⟨F, hF⟩ := antiprism_polygonFace hn
  exact hs F n hF

/-- The concrete antiprism prism retains its antiprism's actual n-gonal top. -/
theorem antiprismPrism_polygonFace {n : ℕ} (hn : 3 ≤ n) :
    ∃ F, PolygonFace (antiprismPrismModel n) F n := by
  obtain ⟨F, hF⟩ := antiprism_polygonFace hn
  exact polyhedralPrism_polygonFace (convex_convexHull ℝ _) hF

theorem antiprismPrism_smallFaces_parameter {n : ℕ} (hn : 3 ≤ n)
    (hs : SmallFaces (antiprismPrismModel n)) : n ≤ 16 := by
  obtain ⟨F, hF⟩ := antiprismPrism_polygonFace hn
  exact hs F n hF

/-- Coordinate swap of the two Euclidean product factors. -/
noncomputable def productSwap {a b : ℕ} :
    EuclideanSpace ℝ (Fin a ⊕ Fin b) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin b ⊕ Fin a) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.sumComm (Fin a) (Fin b))).toAffineIsometryEquiv

@[simp] theorem productSwap_productPoint {a b : ℕ} (x : Space a) (y : Space b) :
    productSwap (productPoint x y) = productPoint y x := by
  ext i
  cases i <;> rfl

theorem productSwap_image {a b : ℕ} (P : Set (Space a)) (Q : Set (Space b)) :
    productSwap '' product P Q = product Q P := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, x, hx, (productSwap_productPoint x y)⟩
  · rintro ⟨y, hy, x, hx, rfl⟩
    exact ⟨productPoint x y, ⟨x, hx, y, hy, rfl⟩, productSwap_productPoint x y⟩

/-- The second polygon factor occurs as an actual duoprism face as well. -/
theorem duoprism_second_polygonFace {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) :
    ∃ F, PolygonFace (duoprismModel p q) F q := by
  obtain ⟨F, hF⟩ := duoprism_first_polygonFace hq hp
  have hh := embedding_polygonFace_image productSwap.toAffineIsometry hF
  change PolygonFace (productSwap '' product (unitPolygon q) (unitPolygon p)) _ q at hh
  rw [productSwap_image] at hh
  exact ⟨_, hh⟩

theorem duoprism_smallFaces_parameters {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q)
    (hs : SmallFaces (duoprismModel p q)) : p ≤ 16 ∧ q ≤ 16 := by
  obtain ⟨F, hF⟩ := duoprism_first_polygonFace hp hq
  obtain ⟨G, hG⟩ := duoprism_second_polygonFace hp hq
  exact ⟨hs F p hF, hs G q hG⟩

/-- The base of a small-faced polyhedral prism has small actual faces. -/
theorem polyhedralPrism_smallFaces_base {Q : Set (Space 3)} (hQ : Convex ℝ Q)
    (hs : SmallFaces (polyhedralPrismModel Q)) : SmallFaces Q := by
  intro G k hG
  obtain ⟨F, hF⟩ := polyhedralPrism_polygonFace hQ hG
  exact hs F k hF

section Transport
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Actual polygon-size bounds are invariant under isometric embedding. -/
theorem smallFaces_embedding_iff (f : E →ᵃⁱ[ℝ] F) {P : Set E} (hP : FinitePolytope P) :
    SmallFaces (f '' P) ↔ SmallFaces P := by
  constructor
  · intro hs G k hG
    exact hs (f '' G) k (embedding_polygonFace_image f hG)
  · intro hs G k hG
    exact hs (f ⁻¹' G) k (embedding_polygonFace_preimage f hP hG)

/-- Whole-set intrinsic congruence preserves actual polygon-size bounds,
including between different Euclidean ambient dimensions. -/
theorem smallFaces_cross_congruent {P : Set E} {Q : Set F} (hP : FinitePolytope P)
    (h : Congruent P Q) (hs : SmallFaces P) : SmallFaces Q := by
  let i := euclideanInl (E := E) (F := F)
  let j := euclideanInr (E := E) (F := F)
  have hQ := (finitePolytope_cross_congruent_iff h).mp hP
  have hPi := finitePolytope_affineMap_image i.toAffineMap hP
  have hsi := (smallFaces_embedding_iff i hP).mpr hs
  obtain ⟨g, hg⟩ := (congruent_iff_affineIsometryEquiv_image (i '' P) (j '' Q)).mp
    (congruent_euclidean_sum h)
  have hsg := (smallFaces_embedding_iff g.toAffineIsometry hPi).mpr hsi
  change SmallFaces (g '' (i '' P)) at hsg
  rw [hg] at hsg
  exact (smallFaces_embedding_iff j hQ).mp hsg

end Transport

/-- Parameter bounds can be read directly from any actual congruent
small-faced polytope; no uniformity property of the model is assumed. -/
theorem congruent_polygonPrism_smallFaces_parameter
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Set E} (hP : FinitePolytope P) (hs : SmallFaces P) {n : ℕ} (hn : 3 ≤ n)
    (h : Congruent P (polygonPrismModel n)) : n ≤ 16 :=
  polygonPrism_smallFaces_parameter hn (smallFaces_cross_congruent hP h hs)

theorem congruent_antiprism_smallFaces_parameter
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Set E} (hP : FinitePolytope P) (hs : SmallFaces P) {n : ℕ} (hn : 3 ≤ n)
    (h : Congruent P (antiprismModel n)) : n ≤ 16 :=
  antiprism_smallFaces_parameter hn (smallFaces_cross_congruent hP h hs)

theorem congruent_antiprismPrism_smallFaces_parameter
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Set E} (hP : FinitePolytope P) (hs : SmallFaces P) {n : ℕ} (hn : 3 ≤ n)
    (h : Congruent P (antiprismPrismModel n)) : n ≤ 16 :=
  antiprismPrism_smallFaces_parameter hn (smallFaces_cross_congruent hP h hs)

theorem congruent_duoprism_smallFaces_parameters
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Set E} (hP : FinitePolytope P) (hs : SmallFaces P) {p q : ℕ}
    (hp : 3 ≤ p) (hq : 3 ≤ q) (h : Congruent P (duoprismModel p q)) : p ≤ 16 ∧ q ≤ 16 :=
  duoprism_smallFaces_parameters hp hq (smallFaces_cross_congruent hP h hs)

end Uniform5.Composition
