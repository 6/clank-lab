import Uniform5.CompositionLibraryNames
import Uniform5.CompositionCaseBProductSlices

/-! Literal five-dimensional construction names. Product-factor uniformity
is inherited from the actual whole polytope, rather than attached to a name. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical

inductive KnownPolyhedronName where
  | finite (index : Fin 18)
  | prism (index : Fin 14)
  | antiprism (index : Fin 14)

noncomputable def KnownPolyhedronModel : KnownPolyhedronName → Set (Space 3) → Prop
  | .finite i, Q => NamedPolyhedronModel i Q
  | .prism i, Q => Congruent Q (polygonPrismModel (i.val + 3))
  | .antiprism i, Q => Congruent Q (antiprismModel (i.val + 3))

/-- Three rank-five diagrams, facet prisms, and polygon products; polygon
indices use the paper's bound of sixteen for Case A. -/
inductive KnownFiveName where
  | wythoff (diagram : Fin 3) (rings : Fin 31)
  | prism (facet : FacetLibraryName)
  | polygonProduct (polygon : Fin 14) (polyhedron : KnownPolyhedronName)

/-- Literal binary masks retain leading zeroes. -/
def knownRingBits (width value : ℕ) : String :=
  String.mk (List.ofFn (fun i : Fin width =>
    if value.testBit (width - 1 - i.val) then '1' else '0'))

def knownFinitePolyhedronString : Fin 18 → String :=
  !["tet", "oct", "cube", "ico", "doe", "tut", "co", "tic", "toe",
    "sirco", "girco", "id", "tid", "ti", "srid", "grid", "snic", "snid"]

def KnownPolyhedronName.sourceName : KnownPolyhedronName → String
  | .finite i => knownFinitePolyhedronString i
  | .prism i => "P" ++ toString (i.val + 3)
  | .antiprism i => "A" ++ toString (i.val + 3)

/-- The exact source spellings used by the stage-three input and report. -/
def facetLibrarySourceName : FacetLibraryName → String
  | .wythoff d m => !["A4", "B4", "D4", "F4", "H4"] d ++ knownRingBits 4 (m.val + 1)
  | .exceptional i => !["sadi", "gap"] i
  | .polyhedronPrism i => "pr-" ++ knownFinitePolyhedronString i
  | .antiprismPrism i => "antiprism-prism-" ++ toString (i.val + 3)
  | .duoprism p => "duoprism-" ++ toString (p.val.1.val + 3) ++ "-" ++ toString (p.val.2.val + 3)

def KnownFiveName.sourceName : KnownFiveName → String
  | .wythoff d m => !["A5", "B5", "D5"] d ++ knownRingBits 5 (m.val + 1)
  | .prism n => "prism-" ++ facetLibrarySourceName n
  | .polygonProduct n i => "{" ++ toString (n.val + 3) ++ "}x" ++ i.sourceName

theorem knownFiveName_source_sanity :
    KnownFiveName.sourceName (.wythoff 1 0) = "B500001" ∧
    KnownFiveName.sourceName (.prism (.polyhedronPrism 0)) = "prism-pr-tet" ∧
    KnownFiveName.sourceName (.polygonProduct 0 (.antiprism 2)) = "{3}xA5" := by decide

/-- Node zero is the most significant bit in the five-bit nonzero mask. -/
noncomputable def knownFiveRingSet (m : Fin 31) : Finset (Fin 5) :=
  Finset.univ.filter (fun i => (m.val + 1).testBit (4 - i.val))

theorem knownFiveRingSet_nonempty (m : Fin 31) : (knownFiveRingSet m).Nonempty := by
  revert m
  decide

/-- Actual coordinate constructions, with no uniformity or classification
assertion among the fields. Type A uses its sum-zero representative in R6. -/
noncomputable def KnownFiveModel : KnownFiveName → Set (Space 5) → Prop
  | .wythoff d m, P =>
      ![ (∃ x : Space 6, (∑ i, x i) = 0 ∧ WythoffSeed rootsA5 (knownFiveRingSet m) x ∧
            Congruent P (WythoffHull rootsA5 x)),
         (∃ x : Space 5, WythoffSeed rootsB5 (knownFiveRingSet m) x ∧
            Congruent P (WythoffHull rootsB5 x)),
         (∃ x : Space 5, WythoffSeed rootsD5 (knownFiveRingSet m) x ∧
            Congruent P (WythoffHull rootsD5 x)) ] d
  | .prism n, P => ∃ Q : Set (Space 4), FacetLibraryModel n Q ∧
      Congruent P (product Q unitInterval)
  | .polygonProduct n i, P => ∃ Q : Set (Space 3), KnownPolyhedronModel i Q ∧
      Congruent P (product (unitPolygon (n.val + 3)) Q)

theorem product_nonempty_factors {a b : ℕ} {P : Set (Space a)} {Q : Set (Space b)}
    (h : (product P Q).Nonempty) : P.Nonempty ∧ Q.Nonempty := by
  obtain ⟨z, x, hx, y, hy, hz⟩ := h
  exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩

theorem product_left_projection_image {a b : ℕ} (P : Set (Space a))
    {Q : Set (Space b)} (hQ : Q.Nonempty) :
    productLeftProjection '' product P Q = P := by
  ext x
  constructor
  · rintro ⟨z, ⟨u, hu, v, hv, rfl⟩, rfl⟩
    exact hu
  · intro hx
    obtain ⟨y, hy⟩ := hQ
    exact ⟨productPoint x y, ⟨x, hx, y, hy, rfl⟩, rfl⟩

/-- Every factor of an actual unit uniform product is unit uniform in
its intrinsic dimension, via an extreme-point face slice. -/
theorem unitUniform_product_left_factor {a b n : ℕ}
    {P : Set (Space a)} {Q : Set (Space b)} (h : UnitUniform (n + 3) (product P Q)) :
    UnitUniform (affineDimension P) P := by
  have hfin := uniform_finitePolytope h.1
  obtain ⟨hPn, hQn⟩ := product_nonempty_factors (finitePolytope_nonempty hfin)
  have hPfin : FinitePolytope P := by
    rw [← product_left_projection_image P hQn]
    exact finitePolytope_affineMap_image productLeftProjection.toAffineMap hfin
  have hQfin : FinitePolytope Q := by
    have hs : FinitePolytope (product Q P) := by
      rw [← productSwap_image]
      exact finitePolytope_affineMap_image productSwap.toAffineMap hfin
    rw [← product_left_projection_image Q hPn]
    exact finitePolytope_affineMap_image productLeftProjection.toAffineMap hs
  obtain ⟨y, hy⟩ := finitePolytope_extremePoints_nonempty hQfin
  have hf := product_left_slice_face (finitePolytope_convex hPfin) hy
  have hu := unitUniform_all_faces h hf (hPn.image (productLeftSlice y))
  rw [affineDimension_affineIsometry_image] at hu
  exact embedding_unitUniform_reflect (productLeftSlice y) hu

theorem unitUniform_prism_base {Q : Set (Space 4)}
    (h : UnitUniform 5 (product Q unitInterval)) : UnitUniform 4 Q := by
  have hn := product_nonempty_factors (finitePolytope_nonempty (uniform_finitePolytope h.1))
  have hd := uniform_dimension h.1
  rw [affineDimension_product hn.1 hn.2, unitInterval_affineDimension] at hd
  have he : affineDimension Q = 4 := by omega
  simpa only [he] using unitUniform_product_left_factor h

theorem unitUniform_polygon_product_factor {n : ℕ} (hn : 3 ≤ n) {Q : Set (Space 3)}
    (h : UnitUniform 5 (product (unitPolygon n) Q)) : UnitUniform 3 Q := by
  have hnz := product_nonempty_factors (finitePolytope_nonempty (uniform_finitePolytope h.1))
  have hd := uniform_dimension h.1
  rw [affineDimension_product hnz.1 hnz.2, (unitPolygon_self_polygonFace hn).2.1] at hd
  have he : affineDimension Q = 3 := by omega
  have hs := (unitUniform_cross_congruent_iff (congruent_product_swap (unitPolygon n) Q) 5).mp h
  simpa only [he] using unitUniform_product_left_factor hs

/-- An actual unit uniform polytope with a literal listed construction
belongs to K1--K3. No classification or computed input is used. -/
theorem knownFiveModel_known {n : KnownFiveName} {P : Set (Space 5)}
    (hP : UnitUniform 5 P) (hm : KnownFiveModel n P) : Known P := by
  cases n with
  | wythoff d m =>
    fin_cases d
    · obtain ⟨x, hx, hs, hc⟩ := hm
      exact Or.inl (Or.inl ⟨knownFiveRingSet m, x, knownFiveRingSet_nonempty m, hx, hs, hc⟩)
    · obtain ⟨x, hs, hc⟩ := hm
      exact Or.inl (Or.inr (Or.inl ⟨knownFiveRingSet m, x, knownFiveRingSet_nonempty m, hs, hc⟩))
    · obtain ⟨x, hs, hc⟩ := hm
      exact Or.inl (Or.inr (Or.inr ⟨knownFiveRingSet m, x, knownFiveRingSet_nonempty m, hs, hc⟩))
  | prism n =>
    obtain ⟨Q, _, hc⟩ := hm
    have hu := (unitUniform_cross_congruent_iff hc 5).mp hP
    exact Or.inr (Or.inl ⟨Q, unitUniform_prism_base hu, hc⟩)
  | polygonProduct n i =>
    obtain ⟨Q, _, hc⟩ := hm
    have hu := (unitUniform_cross_congruent_iff hc 5).mp hP
    exact Or.inr (Or.inr ⟨n.val + 3, by omega, Q,
      unitUniform_polygon_product_factor (by omega) hu, hc⟩)

/-- The unit five-cube realizes the literal B500001 interpretation. -/
theorem cubeCorner_knownFiveModel :
    KnownFiveModel (.wythoff 1 0) (WythoffHull rootsB5 cubeCorner) := by
  change ∃ x, WythoffSeed rootsB5 (knownFiveRingSet 0) x ∧ _
  have hr : knownFiveRingSet 0 = {4} := by decide
  rw [hr]
  exact ⟨cubeCorner, cubeCorner_seed, congruent_refl _⟩

end Uniform5.Composition
