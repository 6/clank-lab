import Uniform5.Faces
import Uniform5.EuclideanPropagation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Concrete geometric vocabulary for the classification

These definitions describe finite convex hulls in Euclidean space, their
actual convex faces, ambient symmetries, regular polygons and orthogonal
products. In particular, uniformity is recursive geometric uniformity;
it does not contain a classification, a search signature, a fan, or a
local-to-global completion condition. This file does not prove the main
classification; the main theorem is in CompositionMainClassification.
-/

noncomputable section

namespace Uniform5.Composition

open Set
open scoped RealInnerProductSpace BigOperators

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Plane := Space 2

/-- Intrinsic metric congruence, including sets in different ambient spaces.
This permits the standard sum-zero realization of A5 in six coordinates. -/
noncomputable def Congruent {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    (P : Set E) (Q : Set F) : Prop := Nonempty (P ≃ᵢ Q)

theorem congruent_refl {E : Type*} [PseudoMetricSpace E] (P : Set E) :
    Congruent P P := ⟨IsometryEquiv.refl P⟩

theorem congruent_symm {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {P : Set E} {Q : Set F} (h : Congruent P Q) : Congruent Q P := by
  obtain ⟨g⟩ := h
  exact ⟨g.symm⟩

theorem congruent_trans {E F G : Type*}
    [PseudoMetricSpace E] [PseudoMetricSpace F] [PseudoMetricSpace G]
    {P : Set E} {Q : Set F} {R : Set G}
    (h : Congruent P Q) (h' : Congruent Q R) : Congruent P R := by
  obtain ⟨g⟩ := h
  obtain ⟨g'⟩ := h'
  exact ⟨g.trans g'⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A nonempty finite convex hull. The generators need not all be vertices;
vertices are always Mathlib's actual extreme points of the hull. -/
noncomputable def FinitePolytope (P : Set E) : Prop :=
  ∃ V : Finset E, V.Nonempty ∧ P = convexHull ℝ (V : Set E)

noncomputable abbrev affineDimension (P : Set E) : ℕ :=
  Uniform5.affineDimension P

/-- Facets are nonempty convex extreme subsets of codimension one. -/
noncomputable def Facet (P F : Set E) : Prop :=
  IsConvexFace P F ∧ F.Nonempty ∧ affineDimension F + 1 = affineDimension P

/-- The full ambient Euclidean symmetry group acts transitively on vertices. -/
noncomputable def VertexTransitive (P : Set E) : Prop :=
  ∀ v ∈ P.extremePoints ℝ, ∀ w ∈ P.extremePoints ℝ,
    ∃ g : E ≃ᵃⁱ[ℝ] E, g '' P = P ∧ g v = w

/-- A genuine exposed segment, with both endpoints actual vertices. -/
noncomputable def Edge (P : Set E) (v w : E) : Prop :=
  v ∈ P.extremePoints ℝ ∧ w ∈ P.extremePoints ℝ ∧ v ≠ w ∧
    IsExposed ℝ P (segment ℝ v w)

noncomputable def UnitEdges (P : Set E) : Prop := ∀ v w, Edge P v w → dist v w = 1

/-- Main's explicit circular vertices, before taking a convex hull. This
wrapper preserves the composition API's simplification behavior; it has no
independent coordinate formula. -/
noncomputable def polygonPoint (n : ℕ) (r : ℝ) (i : Fin n) : Plane :=
  Uniform5.regularPolygonVertex n r i

noncomputable def polygon (n : ℕ) (r : ℝ) : Set Plane :=
  convexHull ℝ (range (polygonPoint n r))

noncomputable def unitPolygonRadius (n : ℕ) : ℝ := 1 / (2 * Real.sin (Real.pi / n))

noncomputable def unitPolygon (n : ℕ) : Set Plane := polygon n (unitPolygonRadius n)

/-- Paper sec:intro, with explicit low-dimensional base cases. A polygon
is regular; in dimension at least three the hull is vertex-transitive and
each of its facets is uniform. Unit length is imposed separately. -/
noncomputable def Uniform : ℕ → Set E → Prop
  | 0, P => ∃ x, P = {x}
  | 1, P => ∃ x y, x ≠ y ∧ P = segment ℝ x y
  | 2, P => ∃ n : ℕ, 3 ≤ n ∧ ∃ r : ℝ, 0 < r ∧
      ∃ f : Plane →ᵃⁱ[ℝ] E, P = f '' polygon n r
  | n + 3, P => FinitePolytope P ∧ affineDimension P = n + 3 ∧
      VertexTransitive P ∧ ∀ F, Facet P F → Uniform (n + 2) F
termination_by n => n

noncomputable def UnitUniform (n : ℕ) (P : Set E) : Prop := Uniform n P ∧ UnitEdges P

/-- A two-face with exactly n vertices. No externally supplied face labels. -/
noncomputable def PolygonFace (P F : Set E) (n : ℕ) : Prop :=
  IsConvexFace P F ∧ affineDimension F = 2 ∧
    ∃ V : Finset E, (V : Set E) = F.extremePoints ℝ ∧ V.card = n

noncomputable def SmallFaces (P : Set E) : Prop := ∀ F n, PolygonFace P F n → n ≤ 16

noncomputable def LargeFace (P : Set E) : Prop := ∃ F n, PolygonFace P F n ∧ 17 ≤ n

/-- The final Case A/Case B split itself is exhaustive. This does not
assert either case's classification conclusion. -/
theorem smallFaces_or_largeFace (P : Set E) : SmallFaces P ∨ LargeFace P := by
  classical
  by_cases h : SmallFaces P
  · exact Or.inl h
  · right
    simp only [SmallFaces, not_forall] at h
    obtain ⟨F, n, h⟩ := h
    obtain ⟨hF, hn⟩ := h
    exact ⟨F, n, hF, by omega⟩

theorem finitePolytope_convex {P : Set E} (h : FinitePolytope P) : Convex ℝ P := by
  obtain ⟨V, _, rfl⟩ := h
  exact convex_convexHull ℝ _

theorem finitePolytope_nonempty {P : Set E} (h : FinitePolytope P) : P.Nonempty := by
  obtain ⟨V, ⟨v, hv⟩, rfl⟩ := h
  exact ⟨v, subset_convexHull ℝ (V : Set E) hv⟩

theorem finitePolytope_extremePoints_finite {P : Set E} (h : FinitePolytope P) :
    (P.extremePoints ℝ).Finite := by
  obtain ⟨V, _, rfl⟩ := h
  exact V.finite_toSet.subset (extremePoints_convexHull_subset (𝕜 := ℝ))

/-- Connect the set-level edge definition to the existing finite-vertex
edge definition. The equality here means V is exactly the vertex set. -/
theorem edge_iff_isEdge {V : Finset E}
    (hV : (V : Set E) = (convexHull ℝ (V : Set E)).extremePoints ℝ) (v w : E) :
    Edge (convexHull ℝ (V : Set E)) v w ↔ IsEdge V v w := by
  simp only [Edge, IsEdge, ← hV, Finset.mem_coe]

theorem unitEdges_iff {V : Finset E}
    (hV : (V : Set E) = (convexHull ℝ (V : Set E)).extremePoints ℝ) :
    UnitEdges (convexHull ℝ (V : Set E)) ↔
      ∀ v w, IsEdge V v w → dist v w = 1 := by
  simp only [UnitEdges, edge_iff_isEdge hV]

theorem uniform_finitePolytope {n : ℕ} {P : Set E} (h : Uniform (n + 3) P) :
    FinitePolytope P := by
  rw [Uniform] at h
  exact h.1

theorem uniform_dimension {n : ℕ} {P : Set E} (h : Uniform (n + 3) P) :
    affineDimension P = n + 3 := by
  rw [Uniform] at h
  exact h.2.1

theorem uniform_facets {n : ℕ} {P F : Set E} (h : Uniform (n + 3) P)
    (hF : Facet P F) : Uniform (n + 2) F := by
  rw [Uniform] at h
  exact h.2.2.2 F hF

@[simp] theorem affineDimension_singleton (x : E) : affineDimension ({x} : Set E) = 0 := by
  simp [affineDimension, direction_affineSpan]

/-- A singleton cannot slip through the dimension-five definition. -/
theorem not_uniform5_singleton (x : E) : ¬ Uniform 5 ({x} : Set E) := by
  intro h
  have hd := uniform_dimension (n := 2) h
  simp at hd

theorem uniform_point (x : E) : Uniform 0 ({x} : Set E) := by
  rw [Uniform]
  exact ⟨x, rfl⟩

theorem uniform_segment {x y : E} (h : x ≠ y) : Uniform 1 (segment ℝ x y) := by
  rw [Uniform]
  exact ⟨x, y, h, rfl⟩

theorem uniform_polygon {n : ℕ} {r : ℝ} (hn : 3 ≤ n) (hr : 0 < r) :
    Uniform 2 (polygon n r) := by
  rw [Uniform]
  refine ⟨n, hn, r, hr, AffineIsometry.id, ?_⟩
  simp

theorem unitPolygonRadius_pos {n : ℕ} (hn : 3 ≤ n) : 0 < unitPolygonRadius n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply one_div_pos.mpr
  apply mul_pos (by norm_num)
  apply Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos hn')
  exact (div_lt_self Real.pi_pos (by exact_mod_cast (show 1 < n by omega)))

theorem uniform_unitPolygon {n : ℕ} (hn : 3 ≤ n) : Uniform 2 (unitPolygon n) :=
  uniform_polygon hn (unitPolygonRadius_pos hn)

theorem polygonPoint_norm_sq (n : ℕ) (r : ℝ) (i : Fin n) :
    ‖polygonPoint n r i‖ ^ 2 = r ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp only [polygonPoint, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs,
    WithLp.equiv_symm_pi_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * (i : ℕ) / n)]

/-- A concrete four-gon has the expected first two vertices. -/
theorem square_vertices : polygonPoint 4 1 0 = !₂[1, 0] ∧
    polygonPoint 4 1 1 = !₂[0, 1] := by
  constructor
  · simp [polygonPoint]
  · have h : 2 * Real.pi / 4 = Real.pi / 2 := by ring
    simp [polygonPoint, h]

/-- Euclidean Cartesian product coordinates; using the ordinary product
metric here would incorrectly give the maximum norm. -/
noncomputable def productPoint {a b : ℕ} (x : Space a) (y : Space b) :
    EuclideanSpace ℝ (Fin a ⊕ Fin b) := (WithLp.equiv 2 _).symm (Sum.elim x y)

noncomputable def product {a b : ℕ} (P : Set (Space a)) (Q : Set (Space b)) :
    Set (EuclideanSpace ℝ (Fin a ⊕ Fin b)) :=
  {z | ∃ x ∈ P, ∃ y ∈ Q, z = productPoint x y}

theorem productPoint_dist_sq {a b : ℕ} (x x' : Space a) (y y' : Space b) :
    dist (productPoint x y) (productPoint x' y') ^ 2 =
      dist x x' ^ 2 + dist y y' ^ 2 := by
  simp only [dist_eq_norm, EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)]
  simp [productPoint, Fintype.sum_sum_type]

theorem product_nonempty {a b : ℕ} {P : Set (Space a)} {Q : Set (Space b)}
    (hP : P.Nonempty) (hQ : Q.Nonempty) : (product P Q).Nonempty := by
  obtain ⟨x, hx⟩ := hP
  obtain ⟨y, hy⟩ := hQ
  exact ⟨productPoint x y, x, hx, y, hy, rfl⟩

noncomputable def unitInterval : Set (Space 1) := segment ℝ 0 !₂[1]

/-- A length-one segment really has unit exposed edges: its extreme
points are among its two generators, so no different pair is possible. -/
theorem unitEdges_segment {x y : E} (hxy : dist x y = 1) :
    UnitEdges (segment ℝ x y) := by
  intro v w he
  have ends (z : E) (hz : z ∈ (segment ℝ x y).extremePoints ℝ) : z = x ∨ z = y := by
    rw [← convexHull_pair] at hz
    exact Set.mem_insert_iff.mp (extremePoints_convexHull_subset hz)
  obtain hv | hv := ends v he.1 <;> obtain hw | hw := ends w he.2.1
  · exact (he.2.2.1 (hv.trans hw.symm)).elim
  · simpa [hv, hw] using hxy
  · simpa [hv, hw, dist_comm] using hxy
  · exact (he.2.2.1 (hv.trans hw.symm)).elim

theorem unitUniform_interval : UnitUniform 1 unitInterval := by
  have hd : dist (0 : Space 1) (!₂[1]) = 1 := by
    norm_num [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_one]
  refine ⟨uniform_segment ?_, unitEdges_segment hd⟩
  intro he
  simp [he] at hd

/-- A product metric sanity check: opposite unit-square corners have
squared distance two, rather than one. -/
theorem unitSquare_diagonal_sq :
    dist (productPoint (!₂[0] : Space 1) (!₂[0] : Space 1))
      (productPoint (!₂[1] : Space 1) (!₂[1] : Space 1)) ^ 2 = 2 := by
  rw [productPoint_dist_sq]
  norm_num [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_one]

end Uniform5.Composition
