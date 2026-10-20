import Uniform5.Propagation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Between
import Mathlib.Algebra.Group.Fin.Basic

/-!
# Propagation restricted to recursively regular-faced Euclidean polytopes

This module keeps the forcing quantifier inside the paper class. Regular
polygons are actual equally spaced circle vertices in an isometrically
embedded Euclidean plane. The recursive predicate stops at dimension two.
-/

namespace Uniform5
open Set

/-- Affine dimension, used only in finite-dimensional Euclidean space. -/
noncomputable abbrev affineDimension {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (S : Set E) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ S).direction

/-- A nonempty convex face with the same affine span as its parent is the
whole parent. A relative interior point of the face can be extended a small
amount opposite any parent point; extremality then puts that point in the face. -/
theorem convexFace_eq_of_affineSpan_eq {P F : Set Euclidean5}
    (hF : IsConvexFace P F) (hne : F.Nonempty)
    (hspan : affineSpan ℝ F = affineSpan ℝ P) : F = P := by
  apply Set.Subset.antisymm hF.2.1
  intro y hy
  obtain ⟨p, hp⟩ := hne.intrinsicInterior hF.1
  obtain ⟨p', hp', rfl⟩ := hp
  letI : Nonempty (affineSpan ℝ F) := ⟨p'⟩
  letI := (affineSpan ℝ F).toNormedAddTorsor
  have hpF : (p' : Euclidean5) ∈ F := (interior_subset hp' : p' ∈ Subtype.val ⁻¹' F)
  let y' : affineSpan ℝ F := ⟨y, by rw [hspan]; exact subset_affineSpan ℝ P hy⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp')
  let d := dist p' y'
  let t := ε / (2 * (d + 1))
  have hd : 0 ≤ d := dist_nonneg
  have ht : 0 < t := div_pos hε (by positivity)
  have htε : t * d < ε := by
    have hid : t * (2 * (d + 1)) = ε := by
      dsimp only [t]
      exact div_mul_cancel₀ _ (by positivity)
    nlinarith
  let w' := AffineMap.lineMap p' y' (-t)
  have hwF : (w' : Euclidean5) ∈ F := by
    apply hball
    change dist (AffineMap.lineMap p' y' (-t)) p' < ε
    rw [dist_lineMap_left, Real.norm_eq_abs, abs_neg, abs_of_pos ht]
    exact htε
  have hw : (w' : Euclidean5) = (1 + t) • (p' : Euclidean5) + (-t) • y := by
    change (affineSpan ℝ F).subtype (AffineMap.lineMap p' y' (-t)) = _
    rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module]
    change (1 - -t) • (p' : Euclidean5) + (-t) • y = _
    rw [sub_neg_eq_add]
  have ht1 : 0 < 1 + t := by linarith
  have hseg : (p' : Euclidean5) ∈ openSegment ℝ y (w' : Euclidean5) := by
    refine ⟨t / (1 + t), 1 / (1 + t), div_pos ht ht1, div_pos zero_lt_one ht1, ?_, ?_⟩
    · field_simp; ring
    · rw [hw]
      have ha : t / (1 + t) + (1 / (1 + t)) * (-t) = 0 := by ring
      have hb : (1 / (1 + t)) * (1 + t) = 1 := by
        exact div_mul_cancel₀ _ (ne_of_gt ht1)
      calc
        (t / (1 + t)) • y + (1 / (1 + t)) •
            ((1 + t) • (p' : Euclidean5) + (-t) • y) =
            (t / (1 + t) + (1 / (1 + t)) * (-t)) • y +
              ((1 / (1 + t)) * (1 + t)) • (p' : Euclidean5) := by module
        _ = (p' : Euclidean5) := by rw [ha, hb]; simp
  exact (hF.2.2 hy (hF.2.1 hwF) hpF hseg).1

/-- Proper nonempty convex faces have strictly smaller affine dimension. -/
theorem proper_convexFace_dimension_lt {P F : Set Euclidean5}
    (hF : IsConvexFace P F) (hne : F.Nonempty) (hproper : F ≠ P) :
    affineDimension F < affineDimension P := by
  have hle := affineSpan_mono ℝ hF.2.1
  have hdle := AffineSubspace.direction_le hle
  have hdimle := Submodule.finrank_mono hdle
  apply lt_of_le_of_ne hdimle
  intro heq
  have hd := Submodule.eq_of_le_of_finrank_eq hdle heq
  have hspan := AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hd
    (hne.mono (subset_affineSpan ℝ F)) hle
  exact hproper (convexFace_eq_of_affineSpan_eq hF hne hspan)

/-- A collinear set of actual extreme points has at most two points and is
vertex-transitive: a midpoint reflection swaps its two distinct members. -/
theorem collinear_extreme_set_transitive {P S : Set Euclidean5}
    (hSP : S ⊆ P) (hext : ∀ z ∈ S, z ∈ P.extremePoints ℝ)
    (hcol : Collinear ℝ S) : IsVertexTransitive S := by
  intro x hx y hy
  by_cases hxy : x = y
  · exact ⟨AffineIsometryEquiv.refl ℝ Euclidean5, by simp, hxy⟩
  have hset : S = {x, y} := by
    apply Set.Subset.antisymm
    · intro z hz
      have hthree : Collinear ℝ ({x, y, z} : Set Euclidean5) :=
        hcol.subset (by rintro _ (rfl | rfl | h); exact hx; exact hy; simpa using h ▸ hz)
      have hxext := (mem_extremePoints_iff_forall_segment.mp (hext x hx)).2
      have hyext := (mem_extremePoints_iff_forall_segment.mp (hext y hy)).2
      have hzext := (mem_extremePoints_iff_forall_segment.mp (hext z hz)).2
      rcases hthree.wbtw_or_wbtw_or_wbtw with h | h | h
      · rcases hyext x (hSP hx) z (hSP hz) h.mem_segment with hxy' | hzy
        · exact (hxy hxy').elim
        · exact Or.inr (by simpa using hzy)
      · rcases hzext y (hSP hy) x (hSP hx) h.mem_segment with hyz | hxz
        · exact Or.inr (by simpa using hyz.symm)
        · exact Or.inl hxz.symm
      · rcases hxext z (hSP hz) y (hSP hy) h.mem_segment with hzx | hyx
        · exact Or.inl hzx
        · exact (hxy hyx.symm).elim
    · exact pair_subset hx hy
  let g := AffineIsometryEquiv.pointReflection ℝ (midpoint ℝ x y)
  have hgx : g x = y := AffineIsometryEquiv.pointReflection_midpoint_left x y
  have hgy : g y = x := AffineIsometryEquiv.pointReflection_midpoint_right x y
  refine ⟨g, ?_, hgx⟩
  rw [hset, Set.image_pair, hgx, hgy, Set.pair_comm]

/-- Ambient affine isometries preserve affine dimension. -/
theorem affineDimension_isometry_image (g : Euclidean5 ≃ᵃⁱ[ℝ] Euclidean5)
    (S : Set Euclidean5) : affineDimension (g '' S) = affineDimension S := by
  unfold affineDimension
  have hspan : affineSpan ℝ (g '' S) =
      (affineSpan ℝ S).map g.toAffineEquiv.toAffineMap :=
    (AffineSubspace.map_span g.toAffineEquiv.toAffineMap S).symm
  rw [hspan, AffineSubspace.map_direction]
  exact g.linearIsometryEquiv.toLinearEquiv.finrank_map_eq _

/-- The actual Euclidean plane in which the regular polygon is parametrized. -/
abbrev PolygonPlane := EuclideanSpace ℝ (Fin 2)

/-- Equally spaced circle vertices, with cyclic index in `Fin p`. -/
noncomputable abbrev regularPolygonVertex (p : ℕ) (r : ℝ) (i : Fin p) : PolygonPlane :=
  !₂[r * Real.cos (2 * Real.pi * (i.val : ℝ) / (p : ℝ)),
     r * Real.sin (2 * Real.pi * (i.val : ℝ) / (p : ℝ))]

/-- A regular polygon is exactly the vertex range of an equally spaced
positive-radius circle in an affinely isometrically embedded Euclidean plane. -/
def RegularPolygon (S : Set Euclidean5) : Prop :=
  ∃ p : ℕ, 3 ≤ p ∧ ∃ r : ℝ, 0 < r ∧
    ∃ e : PolygonPlane →ᵃⁱ[ℝ] Euclidean5,
      S = Set.range (fun i : Fin p => e (regularPolygonVertex p r i))

/-- The concrete circle definition is invariant under ambient isometry,
by composition of the actual plane embedding. -/
theorem RegularPolygon.isometry_image {S : Set Euclidean5} (h : RegularPolygon S)
    (g : Euclidean5 ≃ᵃⁱ[ℝ] Euclidean5) : RegularPolygon (g '' S) := by
  obtain ⟨p, hp, r, hr, e, rfl⟩ := h
  refine ⟨p, hp, r, hr, g.toAffineIsometry.comp e, ?_⟩
  rw [← Set.range_comp]
  rfl

/-- The usual rotation matrix, written as a linear map on the actual plane. -/
noncomputable abbrev polygonRotationLinear (θ : ℝ) : PolygonPlane →ₗ[ℝ] PolygonPlane where
  toFun x := !₂[Real.cos θ * x 0 - Real.sin θ * x 1,
    Real.sin θ * x 0 + Real.cos θ * x 1]
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    ext i
    fin_cases i <;> simp <;> ring

/-- Trigonometric norm preservation gives an actual linear isometry. -/
noncomputable def polygonRotation (θ : ℝ) : PolygonPlane →ₗᵢ[ℝ] PolygonPlane :=
  LinearMap.isometryOfInner (polygonRotationLinear θ) (by
    intro x y
    simp [polygonRotationLinear, PiLp.inner_apply, Fin.sum_univ_two]
    linear_combination (x 0 * y 0 + x 1 * y 1) * Real.cos_sq_add_sin_sq θ)

@[simp] theorem polygonRotation_apply (θ : ℝ) (x : PolygonPlane) :
    polygonRotation θ x = !₂[Real.cos θ * x 0 - Real.sin θ * x 1,
      Real.sin θ * x 0 + Real.cos θ * x 1] := rfl

/-- A plane linear isometry extends through any actual affine-isometric
embedding to an ambient affine isometry. Surjectivity of the extension
follows from injectivity in the finite-dimensional ambient space. -/
theorem extend_polygon_plane_isometry (e : PolygonPlane →ᵃⁱ[ℝ] Euclidean5)
    (R : PolygonPlane →ₗᵢ[ℝ] PolygonPlane) :
    ∃ g : Euclidean5 ≃ᵃⁱ[ℝ] Euclidean5, ∀ x, g (e x) = e (R x) := by
  let u := e.linearIsometry
  let S := LinearMap.range u.toLinearMap
  let L : S →ₗᵢ[ℝ] Euclidean5 := u.comp (R.comp u.equivRange.symm.toLinearIsometry)
  let M := L.extend
  let M' : Euclidean5 ≃ₗᵢ[ℝ] Euclidean5 :=
    LinearIsometryEquiv.ofSurjective M (LinearMap.surjective_of_injective M.injective)
  let g := (AffineIsometryEquiv.vaddConst ℝ (e 0)).symm.trans
    (M'.toAffineIsometryEquiv.trans (AffineIsometryEquiv.vaddConst ℝ (e 0)))
  refine ⟨g, ?_⟩
  intro x
  have he (y : PolygonPlane) : e y = u y + e 0 := by
    simpa only [vadd_eq_add, add_zero] using e.map_vadd 0 y
  have hMu : M (u x) = u (R x) := by
    change L.extend ((u.equivRange x : S) : Euclidean5) = _
    rw [LinearIsometry.extend_apply]
    change u (R (u.equivRange.symm (u.equivRange x))) = _
    rw [u.equivRange.symm_apply_apply]
  change M (e x - e 0) + e 0 = e (R x)
  rw [he x, add_sub_cancel_right, hMu, he (R x)]

/-- The explicit circle parametrization is equivariant for cyclic index
addition. Reduction modulo `p` changes the angle by a whole number of turns. -/
theorem polygonRotation_vertex {p : ℕ} [NeZero p] (r : ℝ) (i k : Fin p) :
    polygonRotation (2 * Real.pi * (k.val : ℝ) / (p : ℝ)) (regularPolygonVertex p r i) =
      regularPolygonVertex p r (i + k) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hn : (((i.val + k.val) % p : ℕ) : ℝ) + (p : ℝ) *
      (((i.val + k.val) / p : ℕ) : ℝ) = (i.val : ℝ) + (k.val : ℝ) := by
    exact_mod_cast Nat.mod_add_div (i.val + k.val) p
  have hangle : 2 * Real.pi * ((i + k).val : ℝ) / (p : ℝ) =
      (2 * Real.pi * (k.val : ℝ) / (p : ℝ) +
        2 * Real.pi * (i.val : ℝ) / (p : ℝ)) -
          (((i.val + k.val) / p : ℕ) : ℝ) * (2 * Real.pi) := by
    rw [Fin.val_add]
    field_simp
    linear_combination (2 * Real.pi) * hn
  ext j
  fin_cases j <;>
    simp [polygonRotation_apply, regularPolygonVertex, hangle,
      Real.cos_sub_nat_mul_two_pi, Real.sin_sub_nat_mul_two_pi,
      Real.cos_add, Real.sin_add] <;> ring

/-- The actual regular circle polygon has a transitive ambient isometry
group. The cyclic rotation is constructed in its embedded plane and extended
as a genuine ambient isometry; no symmetry premise is assumed. -/
theorem RegularPolygon.vertex_transitive {S : Set Euclidean5}
    (h : RegularPolygon S) : IsVertexTransitive S := by
  obtain ⟨p, hp, r, hr, e, rfl⟩ := h
  letI : NeZero p := ⟨by omega⟩
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  let k : Fin p := j - i
  obtain ⟨g, hg⟩ := extend_polygon_plane_isometry e
    (polygonRotation (2 * Real.pi * (k.val : ℝ) / (p : ℝ)))
  have hact (a : Fin p) : g (e (regularPolygonVertex p r a)) =
      e (regularPolygonVertex p r (a + k)) := by
    rw [hg, polygonRotation_vertex]
  refine ⟨g, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a + k, (hact a).symm⟩
    · rintro _ ⟨a, rfl⟩
      refine ⟨e (regularPolygonVertex p r (a - k)), ⟨a - k, rfl⟩, ?_⟩
      rw [hact, sub_add_cancel]
  · rw [hact]
    have hik : i + k = j := by dsimp [k]; abel
    rw [hik]

/-- The paper recursion stops at affine dimension two, requiring an actual
regular polygon. Above dimension two it requires vertex transitivity and
recursive uniformity of the actual facets.

Polygon transitivity is derived from the concrete circle parametrization,
not supplied as a redundant constructor premise. -/
inductive PaperRecursiveUniform (V : Set Euclidean5) : Set Euclidean5 → Prop
  | polygon {P : Set Euclidean5} (dimension : affineDimension P = 2)
      (regular : RegularPolygon (V ∩ P)) : PaperRecursiveUniform V P
  | higher {P : Set Euclidean5} (dimension : 2 < affineDimension P)
      (transitive : IsVertexTransitive (V ∩ P))
      (facets : ∀ G, IsGeometricFacet P G → PaperRecursiveUniform V G) :
      PaperRecursiveUniform V P

/-- The top-level transitivity data in the recursive class. -/
theorem PaperRecursiveUniform.vertex_transitive {V P : Set Euclidean5}
    (h : PaperRecursiveUniform V P) : IsVertexTransitive (V ∩ P) := by
  cases h with
  | polygon _ hr => exact hr.vertex_transitive
  | higher _ ht _ => exact ht

/-- The paper-class recursion is closed under ambient affine isometries. -/
theorem PaperRecursiveUniform.isometry_image {V P : Set Euclidean5}
    (h : PaperRecursiveUniform V P) (g : Euclidean5 ≃ᵃⁱ[ℝ] Euclidean5) :
    PaperRecursiveUniform (g '' V) (g '' P) := by
  induction h with
  | @polygon P hd hr =>
    refine PaperRecursiveUniform.polygon ?_ ?_
    · simpa only [affineDimension_isometry_image] using hd
    · rw [← Set.image_inter g.injective]
      exact hr.isometry_image g
  | @higher P hd ht hfacets ih =>
    refine PaperRecursiveUniform.higher ?_ ?_ ?_
    · simpa only [affineDimension_isometry_image] using hd
    · rw [← Set.image_inter g.injective]
      exact vertexTransitive_isometry_image g ht
    · intro G hG
      have hback : IsGeometricFacet P (g.symm '' G) := by
        simpa only [isometry_symm_image_image] using facet_isometry_image g.symm hG
      have h := ih (g.symm '' G) hback
      simpa only [isometry_image_symm_image] using h

/-- Every face of an actual recursively uniform polytope is transitive. The
base case derives the proper-subface assertion geometrically, rather than
requiring all-face symmetry data as an extra polygon field. -/
theorem PaperRecursiveUniform.face_transitive {V : Set Euclidean5}
    (hV : V.Finite) (hext : ∀ x ∈ V, x ∈ (convexHull ℝ V).extremePoints ℝ)
    {P : Set Euclidean5} (h : PaperRecursiveUniform V P) :
    IsConvexFace (convexHull ℝ V) P →
      ∀ F, IsConvexFace P F → IsVertexTransitive (V ∩ F) := by
  induction h with
  | @polygon P hd hr =>
    have ht := hr.vertex_transitive
    intro hP F hF
    by_cases heq : F = P
    · simpa only [heq] using ht
    by_cases hne : F.Nonempty
    · have hlt := proper_convexFace_dimension_lt hF hne heq
      have hdim : affineDimension F ≤ 1 := by omega
      have hcol : Collinear ℝ F := by
        apply collinear_iff_finrank_le_one.mpr
        change Module.finrank ℝ (affineSpan ℝ F).direction ≤ 1 at hdim
        rwa [direction_affineSpan] at hdim
      apply collinear_extreme_set_transitive
        (P := convexHull ℝ V) (S := V ∩ F)
      · exact fun x hx => subset_convexHull ℝ V hx.1
      · exact fun x hx => hext x hx.1
      · exact hcol.subset inter_subset_right
    · intro x hx
      exact (hne ⟨x, hx.2⟩).elim
  | @higher P hd ht hfacets ih =>
    intro hP F hF
    by_cases hne : F.Nonempty
    · by_cases heq : F = P
      · simpa only [heq] using ht
      · have hPgen := face_eq_convexHull_inter V hP
        obtain ⟨G, hG, hFG⟩ := face_contained_in_facet
          (hV.subset inter_subset_left)
          (show IsConvexFace (convexHull ℝ (V ∩ P)) F by simpa only [hPgen] using hF)
          hne (by simpa only [hPgen] using heq)
        have hfacet : IsGeometricFacet P G := by simpa only [hPgen] using hG
        exact ih G hfacet (face_of_face hP hfacet.1) F
          (face_restrict hF hfacet.1.2.1 hFG)
    · intro x hx
      exact (hne ⟨x, hx.2⟩).elim

/-- The concrete paper class: the polygon-based recursion is a property of
the actual hull. The inherited all-face symmetry field is derivable from
this recursion using `ofVertices`, rather than an additional input. -/
structure EuclideanPaper5 extends EuclideanUniform5 where
  paper_uniform : PaperRecursiveUniform vertices (convexHull ℝ vertices)

namespace EuclideanPaper5

/-- Admit a geometric vertex model using exactly the polygon-based recursive
uniformity input, deriving the stronger facewise symmetry interface. -/
noncomputable def ofVertices (V : Set Euclidean5) (hfinite : V.Finite)
    (hspan : affineSpan ℝ V = ⊤)
    (hextreme : ∀ x ∈ V, IsConvexFace (convexHull ℝ V) {x})
    (hunit : ∀ x y, GeometricEdge V x y → dist x y = 1)
    (hrecursive : PaperRecursiveUniform V (convexHull ℝ V)) : EuclideanPaper5 where
  toEuclideanUniform5 := {
    vertices := V
    finite_vertices := hfinite
    spanning := hspan
    extreme_vertices := hextreme
    unit_edges := hunit
    uniform_faces := hrecursive.face_transitive hfinite
      (fun x hx => isExtreme_singleton.mp (hextreme x hx).2)
      ⟨convex_convexHull ℝ V, IsExtreme.refl ℝ _⟩ }
  paper_uniform := hrecursive

@[ext] theorem ext {P Q : EuclideanPaper5} (h : P.vertices = Q.vertices) : P = Q := by
  cases P with
  | mk P hP =>
    cases Q with
    | mk Q hQ =>
      have hPQ : P = Q := EuclideanUniform5.ext h
      cases hPQ
      rfl

/-- Ambient transport preserves the polygon-based recursive class. -/
noncomputable def image (g : Euclidean5 ≃ᵃⁱ[ℝ] Euclidean5)
    (P : EuclideanPaper5) : EuclideanPaper5 where
  toEuclideanUniform5 := EuclideanUniform5.image g P.toEuclideanUniform5
  paper_uniform := by
    have h := P.paper_uniform.isometry_image g
    rw [isometry_image_convexHull] at h
    exact h

@[simp] theorem image_vertices (g : Euclidean5 ≃ᵃⁱ[ℝ] Euclidean5) (P : EuclideanPaper5) :
    (image g P).vertices = g '' P.vertices := rfl

/-- Invertible action on this restricted class, not on a larger forcing domain. -/
noncomputable def imageEquiv (g : Euclidean5 ≃ᵃⁱ[ℝ] Euclidean5) :
    EuclideanPaper5 ≃ EuclideanPaper5 where
  toFun := image g
  invFun := image g.symm
  left_inv P := ext (isometry_symm_image_image g P.vertices)
  right_inv P := ext (isometry_image_symm_image g P.vertices)

/-- All abstract fields are proved for the polygon-based paper class itself. -/
noncomputable def starSystem :
    StarSystem Euclidean5 (Set (Set Euclidean5)) EuclideanPaper5 where
  vertices := fun P => P.vertices
  finite_vertices := fun P => P.finite_vertices
  star := fun P => facetStar P.vertices
  adjacent := fun P => GeometricEdge P.vertices
  adjacent_mem := fun h => ⟨h.1, h.2.1⟩
  neighbours := by
    intro P Q x _ _ h y
    exact ⟨EuclideanUniform5.neighbours_of_star_eq
        (P := P.toEuclideanUniform5) (Q := Q.toEuclideanUniform5) h,
      EuclideanUniform5.neighbours_of_star_eq
        (P := Q.toEuclideanUniform5) (Q := P.toEuclideanUniform5) h.symm⟩
  connected := by
    intro P x y hx hy
    exact P.toEuclideanUniform5.graph_connected x hx y hy
  ext := ext

/-- Every ambient affine isometry transports models within the restricted
paper class, including the inverse image of the second comparison model. -/
noncomputable def transport (g : Euclidean5 ≃ᵃⁱ[ℝ] Euclidean5) :
    StarTransport starSystem where
  point := g.toAffineEquiv.toEquiv
  stars := EuclideanUniform5.starEquiv g
  model := imageEquiv g
  vertices := fun P x => g.injective.mem_set_image
  star := fun P x => EuclideanUniform5.image_star g P.toEuclideanUniform5 x
  adjacent := by
    intro P x y
    change GeometricEdge (g '' P.vertices) (g x) (g y) ↔ GeometricEdge P.vertices x y
    refine ⟨fun h => ?_, geometricEdge_isometry_image g⟩
    have hback := geometricEdge_isometry_image g.symm h
    simpa only [isometry_symm_image_image, g.symm_apply_apply] using hback

/-- Transitivity by a symmetry of the first actual model supplies the exact
abstract transport input without enlarging the forcing quantifier. -/
theorem transport_transitive (r : Euclidean5) :
    ∀ P, r ∈ starSystem.vertices P → ∀ x ∈ starSystem.vertices P,
      ∃ t : StarTransport starSystem, t.model P = P ∧ t.point r = x := by
  intro P hr x hx
  obtain ⟨g, hg, hgr⟩ := P.toEuclideanUniform5.vertex_transitive r hr x hx
  exact ⟨transport g, ext hg, hgr⟩

/-- Paper-class local forcing: the forcing hypothesis quantifies only over
`EuclideanPaper5`, not all facewise-transitive `EuclideanUniform5` models. -/
theorem local_forcing_step (r : Euclidean5) (s : Set (Set Euclidean5))
    (forcing : ∀ A B : EuclideanPaper5, r ∈ A.vertices → r ∈ B.vertices →
      facetStar A.vertices r = s → facetStar B.vertices r = s →
      ∀ y, GeometricEdge A.vertices r y →
        facetStar A.vertices y = facetStar B.vertices y)
    {A B : EuclideanPaper5} (hrA : r ∈ A.vertices) (hsA : facetStar A.vertices r = s)
    {x y : Euclidean5} (hxA : x ∈ A.vertices) (hxB : x ∈ B.vertices)
    (hx : facetStar A.vertices x = facetStar B.vertices x)
    (hxy : GeometricEdge A.vertices x y) :
    y ∈ B.vertices ∧ facetStar A.vertices y = facetStar B.vertices y :=
  starSystem.local_forcing_step r s (transport_transitive r) forcing hrA hsA hxA hxB hx hxy

/-- Inclusion propagates within the polygon-based recursive paper class. -/
theorem local_forcing_inclusion (r : Euclidean5) (s : Set (Set Euclidean5))
    (forcing : ∀ A B : EuclideanPaper5, r ∈ A.vertices → r ∈ B.vertices →
      facetStar A.vertices r = s → facetStar B.vertices r = s →
      ∀ y, GeometricEdge A.vertices r y →
        facetStar A.vertices y = facetStar B.vertices y)
    {A B : EuclideanPaper5} (hrA : r ∈ A.vertices) (hrB : r ∈ B.vertices)
    (hsA : facetStar A.vertices r = s) (hsB : facetStar B.vertices r = s) :
    ∀ x ∈ A.vertices, x ∈ B.vertices ∧
      facetStar A.vertices x = facetStar B.vertices x :=
  starSystem.local_forcing_inclusion r s (transport_transitive r) forcing hrA hrB hsA hsB

/-- Local uniqueness with its quantifier restricted to the polygon-based
recursive paper class. All polygon symmetries, geometric fields and transport
closure are proved; forcing is required only at the fixed root and star. -/
theorem local_uniqueness_global (r : Euclidean5) (s : Set (Set Euclidean5))
    (forcing : ∀ A B : EuclideanPaper5, r ∈ A.vertices → r ∈ B.vertices →
      facetStar A.vertices r = s → facetStar B.vertices r = s →
      ∀ y, GeometricEdge A.vertices r y →
        facetStar A.vertices y = facetStar B.vertices y)
    {A B : EuclideanPaper5} (hrA : r ∈ A.vertices) (hrB : r ∈ B.vertices)
    (hsA : facetStar A.vertices r = s) (hsB : facetStar B.vertices r = s) : A = B :=
  starSystem.local_uniqueness_global r s (transport_transitive r) forcing hrA hrB hsA hsB

end EuclideanPaper5
end Uniform5
