import Uniform5.CompositionPolygonUnit
import Uniform5.CompositionUniformFaces
import Uniform5.CompositionFaceCenters
import Mathlib.Data.Set.Card

/-!
# Actual polygon vertex counts and their regular-polygon parameter

The circular parametrization is injective. Hence its index equals the
number of actual extreme points, and the vertex-count parameter in
`PolygonFace` determines the explicit unit polygon and its circumradius.
-/

noncomputable section
namespace Uniform5.Composition
open Set

/-- Distinct indices in the explicit circular parametrization give distinct
vertices; equality of sine and cosine forces equal angles in one period. -/
theorem polygonPoint_injective (n : ℕ) (r : ℝ) (hn : 3 ≤ n) (hr : 0 < r) :
    Function.Injective (polygonPoint n r) := by
  intro i j hij
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hc := congrArg (fun x : Plane => x 0) hij
  have hs := congrArg (fun x : Plane => x 1) hij
  simp only [polygonPoint, WithLp.equiv_symm_pi_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] at hc hs
  have hc' := (mul_left_cancel₀ hr0 hc)
  have hs' := (mul_left_cancel₀ hr0 hs)
  have bounds (k : Fin n) : 0 ≤ 2 * Real.pi * (k : ℕ) / n ∧
      2 * Real.pi * (k : ℕ) / n < 2 * Real.pi := by
    constructor
    · positivity
    · apply (div_lt_iff₀ hn').mpr
      exact mul_lt_mul_of_pos_left (by exact_mod_cast k.isLt) Real.two_pi_pos
  have hdcos : Real.cos (2 * Real.pi * (i : ℕ) / n - 2 * Real.pi * (j : ℕ) / n) = 1 := by
    rw [Real.cos_sub, hc', hs']
    nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * (j : ℕ) / n)]
  have hdzero := (Real.cos_eq_one_iff_of_lt_of_lt
    (show -(2 * Real.pi) < 2 * Real.pi * (i : ℕ) / n -
      2 * Real.pi * (j : ℕ) / n by linarith [(bounds i).1, (bounds j).2])
    (show 2 * Real.pi * (i : ℕ) / n - 2 * Real.pi * (j : ℕ) / n <
      2 * Real.pi by linarith [(bounds i).2, (bounds j).1])).mp hdcos
  have hprod : 2 * Real.pi * (i : ℕ) = 2 * Real.pi * (j : ℕ) :=
    (div_left_inj' (ne_of_gt hn')).mp (sub_eq_zero.mp hdzero)
  have hcast : ((i : ℕ) : ℝ) = (j : ℕ) := mul_left_cancel₀ (ne_of_gt Real.two_pi_pos) hprod
  exact Fin.ext (Nat.cast_injective hcast)

/-- A concrete finite set of all actual polygon vertices. -/
noncomputable def polygonVertexFinset (n : ℕ) (r : ℝ) : Finset Plane :=
  Finset.univ.image (polygonPoint n r)

@[simp] theorem polygonVertexFinset_coe (n : ℕ) (r : ℝ) :
    (polygonVertexFinset n r : Set Plane) = Set.range (polygonPoint n r) := by
  classical
  simp [polygonVertexFinset]

theorem polygonVertexFinset_extremePoints (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (polygonVertexFinset n r : Set Plane) = (polygon n r).extremePoints ℝ := by
  rw [polygonVertexFinset_coe, polygon_extremePoints n r hr]

theorem polygonVertexFinset_card (n : ℕ) (r : ℝ) (hn : 3 ≤ n) (hr : 0 < r) :
    (polygonVertexFinset n r).card = n := by
  classical
  rw [polygonVertexFinset, Finset.card_image_of_injective _ (polygonPoint_injective n r hn hr)]
  simp

theorem polygon_extremePoints_ncard (n : ℕ) (r : ℝ) (hn : 3 ≤ n) (hr : 0 < r) :
    ((polygon n r).extremePoints ℝ).ncard = n := by
  rw [← polygonVertexFinset_extremePoints n r hr.le]
  rw [Set.ncard_coe_Finset]
  exact polygonVertexFinset_card n r hn hr

theorem unitPolygon_extremePoints_ncard {n : ℕ} (hn : 3 ≤ n) :
    ((unitPolygon n).extremePoints ℝ).ncard = n :=
  polygon_extremePoints_ncard n _ hn (unitPolygonRadius_pos hn)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The existing `PolygonFace` count is the count of actual extreme points. -/
theorem polygonFace_extremePoints_ncard {P F : Set E} {k : ℕ}
    (hF : PolygonFace P F k) : (F.extremePoints ℝ).ncard = k := by
  obtain ⟨V, hV, hk⟩ := hF.2.2
  rw [← hV]
  simpa using hk

/-- The actual vertex-count parameter of a polygon face is precisely its
explicit regular-polygon index, not an external combinatorial label. -/
theorem polygonFace_unitPolygon {n k : ℕ} {P F : Set E}
    (hP : UnitUniform (n + 3) P) (hF : PolygonFace P F k) :
    3 ≤ k ∧ ∃ f : Plane →ᵃⁱ[ℝ] E, F = f '' unitPolygon k := by
  obtain ⟨m, hm, f, hrep⟩ := unitUniform_two_unitPolygon (unitUniform_polygonFace hP hF)
  have hcard : (F.extremePoints ℝ).ncard = m := by
    rw [hrep, ← embedding_extremePoints,
      Set.ncard_image_of_injective _ f.injective, unitPolygon_extremePoints_ncard hm]
  have hmk : m = k := hcard.symm.trans (polygonFace_extremePoints_ncard hF)
  rw [hmk] at hm hrep
  exact ⟨hm, f, hrep⟩

/-- A polygon face has the specified intrinsic circumradius, with its center
in its own affine span. -/
theorem polygonFace_circumsphere {n k : ℕ} {P F : Set E}
    (hP : UnitUniform (n + 3) P) (hF : PolygonFace P F k) :
    ∃ c ∈ affineSpan ℝ F,
      ∀ x ∈ F.extremePoints ℝ, dist x c = unitPolygonRadius k := by
  obtain ⟨hk, f, hrep⟩ := polygonFace_unitPolygon hP hF
  refine ⟨f 0, ?_, ?_⟩
  · rw [hrep]
    change f 0 ∈ affineSpan ℝ (f.toAffineMap '' polygon k (unitPolygonRadius k))
    rw [← AffineSubspace.map_span,
      affineSpan_polygon_eq_top k _ hk (unitPolygonRadius_pos hk)]
    exact ⟨0, Set.mem_univ 0, rfl⟩
  · intro x hx
    rw [hrep, ← embedding_extremePoints, unitPolygon,
      polygon_extremePoints k _ (unitPolygonRadius_pos hk).le] at hx
    obtain ⟨y, ⟨i, rfl⟩, rfl⟩ := hx
    rw [f.dist_map, dist_zero_right]
    exact (sq_eq_sq₀ (norm_nonneg _) (unitPolygonRadius_pos hk).le).mp
      (polygonPoint_norm_sq k _ i)

omit [FiniteDimensional ℝ E] in
/-- A finite polytope's circumsphere has a unique nonnegative radius and
center when the center is required to lie in the polytope's affine span. -/
theorem finitePolytope_intrinsic_sphere_unique {P : Set E} (hP : FinitePolytope P)
    {c a : E} {R r : ℝ} (hcP : c ∈ affineSpan ℝ P) (haP : a ∈ affineSpan ℝ P)
    (hc : ∀ x ∈ P.extremePoints ℝ, dist x c = R)
    (ha : ∀ x ∈ P.extremePoints ℝ, dist x a = r) : c = a ∧ R = r := by
  have hspan : affineSpan ℝ (P.extremePoints ℝ) = affineSpan ℝ P := by
    rw [← affineSpan_convexHull (𝕜 := ℝ), ← finitePolytope_eq_convexHull_extremePoints hP]
  have ho := sphere_centers_sub_mem_orthogonal (P.extremePoints ℝ) c a R r
    (fun x hx => by rw [← dist_eq_norm, hc x hx])
    (fun x hx => by rw [← dist_eq_norm, ha x hx])
  rw [hspan] at ho
  have hd : c - a ∈ (affineSpan ℝ P).direction :=
    AffineSubspace.vsub_mem_direction hcP haP
  have hz : c - a = 0 := by
    have hh : c - a ∈ (affineSpan ℝ P).direction ⊓ (affineSpan ℝ P).directionᗮ := ⟨hd, ho⟩
    rw [Submodule.inf_orthogonal_eq_bot] at hh
    exact hh
  have heq : c = a := sub_eq_zero.mp hz
  obtain ⟨x, hx⟩ := finitePolytope_extremePoints_nonempty hP
  exact ⟨heq, (hc x hx).symm.trans (heq ▸ ha x hx)⟩

/-- In particular any intrinsic circumradius assigned to an actual polygon
face is exactly the paper's `1 / (2 sin (π/k))`. -/
theorem polygonFace_intrinsic_radius {n k : ℕ} {P F : Set E}
    (hP : UnitUniform (n + 3) P) (hF : PolygonFace P F k)
    {c : E} {r : ℝ} (hc : c ∈ affineSpan ℝ F)
    (hsphere : ∀ x ∈ F.extremePoints ℝ, dist x c = r) :
    r = unitPolygonRadius k := by
  obtain ⟨a, ha, hs⟩ := polygonFace_circumsphere hP hF
  have hk := (polygonFace_unitPolygon hP hF).1
  have hne : F.Nonempty := by
    have hh := polygonFace_extremePoints_ncard hF
    have hpos : 0 < (F.extremePoints ℝ).ncard := by omega
    obtain ⟨x, hx⟩ := (Set.ncard_pos (Set.finite_of_ncard_pos hpos)).mp hpos
    exact ⟨x, hx.1⟩
  exact (finitePolytope_intrinsic_sphere_unique
    (finitePolytope_face (uniform_finitePolytope hP.1) hF.1 hne)
    hc ha hsphere hs).2

/-- The regular-polygon parametrization's consecutive chords are genuine
edges of the original polytope, using geometric face-edge inheritance. -/
theorem polygonFace_consecutive_edges {n k : ℕ} [NeZero k] {P F : Set E}
    (hP : UnitUniform (n + 3) P) (hF : PolygonFace P F k) :
    ∃ f : Plane →ᵃⁱ[ℝ] E, F = f '' unitPolygon k ∧
      ∀ i : Fin k, Edge P (f (polygonPoint k (unitPolygonRadius k) i))
        (f (polygonPoint k (unitPolygonRadius k) (i + 1))) := by
  obtain ⟨hk, f, hrep⟩ := polygonFace_unitPolygon hP hF
  refine ⟨f, hrep, ?_⟩
  intro i
  have he := embedding_edge_image f
    (polygon_consecutive_edge (unitPolygonRadius k) hk (unitPolygonRadius_pos hk) i)
  change Edge (f '' unitPolygon k) _ _ at he
  rw [← hrep] at he
  exact (edge_face_iff (uniform_finitePolytope hP.1) hF.1 he.1.1 he.2.1.1).mpr he

end Uniform5.Composition
