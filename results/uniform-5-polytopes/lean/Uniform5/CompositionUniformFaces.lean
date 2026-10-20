import Uniform5.CompositionEdgeFaces
import Uniform5.CompositionRidges

/-!
# Recursive uniformity descends to actual faces

Facet containment and strict dimension decrease turn the recursive facet
definition into uniformity of every face of dimension at least two.
-/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A nonempty face of dimension at least two of a recursively uniform
polytope is uniform in its actual affine dimension. -/
theorem uniform_face {n : ℕ} {P F : Set E} (hP : Uniform (n + 3) P)
    (hF : IsConvexFace P F) (hne : F.Nonempty) (hd : 2 ≤ affineDimension F) :
    Uniform (affineDimension F) F := by
  induction n generalizing P with
  | zero =>
    by_cases heq : F = P
    · subst F
      simpa only [uniform_dimension hP] using hP
    obtain ⟨G, hG, hFG⟩ := finitePolytope_face_subset_facet
      (uniform_finitePolytope hP) hF hne heq
    have hdimG : affineDimension G = 2 := by
      have hh := hG.2.2
      rw [uniform_dimension hP] at hh
      omega
    have hFGface := face_restrict hF hG.1.2.1 hFG
    have heqFG : F = G := by
      by_contra hneFG
      have hh := face_affineDimension_lt hFGface hne hneFG
      omega
    subst F
    rw [hdimG]
    exact uniform_facets hP hG
  | succ n ih =>
    by_cases heq : F = P
    · subst F
      simpa only [uniform_dimension hP] using hP
    obtain ⟨G, hG, hFG⟩ := finitePolytope_face_subset_facet
      (uniform_finitePolytope hP) hF hne heq
    exact ih (uniform_facets hP hG) (face_restrict hF hG.1.2.1 hFG)

/-- Unit normalization also descends; its proof uses genuine exposed-edge
inheritance rather than an edge-label compatibility premise. -/
theorem unitUniform_face {n : ℕ} {P F : Set E} (hP : UnitUniform (n + 3) P)
    (hF : IsConvexFace P F) (hne : F.Nonempty) (hd : 2 ≤ affineDimension F) :
    UnitUniform (affineDimension F) F :=
  ⟨uniform_face hP.1 hF hne hd,
    unitEdges_face (uniform_finitePolytope hP.1) hF hP.2⟩

/-- Every actual polygon face of a unit uniform polytope is a unit uniform
regular polygon in the recursive geometric definition. -/
theorem unitUniform_polygonFace {n k : ℕ} {P F : Set E}
    (hP : UnitUniform (n + 3) P) (hF : PolygonFace P F k) :
    UnitUniform 2 F := by
  have hne : F.Nonempty := by
    by_contra hh
    have he : F = ∅ := Set.not_nonempty_iff_eq_empty.mp hh
    have hd := hF.2.1
    rw [he] at hd
    unfold affineDimension Uniform5.affineDimension at hd
    rw [AffineSubspace.span_empty, AffineSubspace.direction_bot, finrank_bot] at hd
    omega
  have hh := unitUniform_face hP hF.1 hne (by rw [hF.2.1])
  rwa [hF.2.1] at hh

/-- Recursive uniformity holds for every nonempty face, including point
and segment faces. Their base cases follow from actual affine dimension. -/
theorem uniform_all_faces {n : ℕ} {P F : Set E} (hP : Uniform (n + 3) P)
    (hF : IsConvexFace P F) (hne : F.Nonempty) : Uniform (affineDimension F) F := by
  by_cases hd : 2 ≤ affineDimension F
  · exact uniform_face hP hF hne hd
  by_cases hz : affineDimension F = 0
  · rw [hz, Uniform]
    exact nonempty_affineDimension_zero_singleton hne hz
  · have ho : affineDimension F = 1 := by omega
    rw [ho, Uniform]
    obtain ⟨a, b, hab, hseg, _⟩ := finitePolytope_dim_one_segment
      (finitePolytope_face (uniform_finitePolytope hP) hF hne) ho
    exact ⟨a, b, hab, hseg⟩

/-- Both recursive uniformity and actual unit edges descend to every
nonempty face, with no lower-dimensional exceptions or extra hypotheses. -/
theorem unitUniform_all_faces {n : ℕ} {P F : Set E} (hP : UnitUniform (n + 3) P)
    (hF : IsConvexFace P F) (hne : F.Nonempty) : UnitUniform (affineDimension F) F :=
  ⟨uniform_all_faces hP.1 hF hne,
    unitEdges_face (uniform_finitePolytope hP.1) hF hP.2⟩

end Uniform5.Composition
