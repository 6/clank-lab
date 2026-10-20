import Uniform5.CompositionProductAssociativity
import Uniform5.CompositionLibraryNames

/-! The cited lower-dimensional classifications and actual polygon-size
bounds imply membership in the explicit 214-name facet catalogue. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical

/-- Sorting the two bounded polygon sizes produces a literal catalogue name. -/
theorem bounded_duoprism_in_catalogue
    {E : Type*} [PseudoMetricSpace E] {P : Set E} {p q : ℕ}
    (hp : 3 ≤ p) (hq : 3 ≤ q) (hp' : p ≤ 16) (hq' : q ≤ 16)
    (h : Congruent P (duoprismModel p q)) :
    ∃ n : FacetLibraryName, FacetLibraryModel n P := by
  by_cases hpq : p ≤ q
  · let i : Fin 14 := ⟨p - 3, by omega⟩
    let j : Fin 14 := ⟨q - 3, by omega⟩
    refine ⟨.duoprism ⟨(i, j), by change p - 3 ≤ q - 3; omega⟩, ?_⟩
    change Congruent P (duoprismModel (p - 3 + 3) (q - 3 + 3))
    simpa only [Nat.sub_add_cancel hp, Nat.sub_add_cancel hq] using h
  · let i : Fin 14 := ⟨q - 3, by omega⟩
    let j : Fin 14 := ⟨p - 3, by omega⟩
    refine ⟨.duoprism ⟨(i, j), by change q - 3 ≤ p - 3; omega⟩, ?_⟩
    change Congruent P (duoprismModel (q - 3 + 3) (p - 3 + 3))
    simp only [Nat.sub_add_cancel hp, Nat.sub_add_cancel hq]
    exact congruent_trans h (congruent_product_swap (unitPolygon p) (unitPolygon q))

/-- Every actual small-faced unit-uniform four-polytope has one of the
214 concrete names. Only the two precisely stated cited classifications
are premises; neither model uniformity nor catalogue completeness is assumed. -/
theorem unitUniform4_smallFaces_catalogue
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    {P : Set (Space 4)} (hP : UnitUniform 4 P) (hs : SmallFaces P) :
    ∃ n : FacetLibraryName, FacetLibraryModel n P := by
  have hPf := uniform_finitePolytope hP.1
  rcases classification4D.exhaustive P hP with ⟨i, hi⟩ | h | h | ⟨Q, hQ, hPQ⟩ |
    ⟨p, q, hp, hq, hpq⟩
  · change Wythoff4Model i P at hi
    have hw : IsWythoff4 P := by
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr (Or.inl hi)
      · exact Or.inr (Or.inr (Or.inl hi))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hi)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hi)))
    obtain ⟨d, m, hm⟩ := isWythoff4_iff_named.mp hw
    exact ⟨.wythoff d m, hm⟩
  · exact ⟨.exceptional 0, h⟩
  · exact ⟨.exceptional 1, h⟩
  · change UnitUniform 3 Q at hQ
    change Congruent P (polyhedralPrismModel Q) at hPQ
    have hQf := uniform_finitePolytope hQ.1
    have hsQ : SmallFaces Q := polyhedralPrism_smallFaces_base
      (finitePolytope_convex hQf) (smallFaces_cross_congruent hPf hPQ hs)
    rcases classification3D.exhaustive Q hQ with h | h | ⟨q, hq, hQq⟩ | ⟨q, hq, hQq⟩
    · obtain ⟨i, hi⟩ := (namedPolyhedronModel_coverage Q).mpr (Or.inl h)
      exact ⟨.polyhedronPrism i, Q, hi, hPQ⟩
    · obtain ⟨i, hi⟩ := (namedPolyhedronModel_coverage Q).mpr (Or.inr h)
      exact ⟨.polyhedronPrism i, Q, hi, hPQ⟩
    · have hb := congruent_polygonPrism_smallFaces_parameter hQf hsQ hq hQq
      exact bounded_duoprism_in_catalogue hq (by decide) hb (by decide)
        (congruent_trans hPQ (congruent_prism_over_polygonPrism hQq))
    · have hq3 : 3 ≤ q := by omega
      have hb := congruent_antiprism_smallFaces_parameter hQf hsQ hq3 hQq
      let i : Fin 14 := ⟨q - 3, by omega⟩
      refine ⟨.antiprismPrism i, ?_⟩
      change Congruent P (antiprismPrismModel (q - 3 + 3))
      rw [Nat.sub_add_cancel hq3]
      exact congruent_trans hPQ (congruent_product hQq (congruent_refl unitInterval))
  · have hb := congruent_duoprism_smallFaces_parameters hPf hs hp hq hpq
    exact bounded_duoprism_in_catalogue hp hq hb.1 hb.2 hpq

/-- The same catalogue applies to actual four-dimensional faces in any
finite-dimensional Euclidean ambient space, via an intrinsic coordinate model. -/
theorem unitUniform4_smallFaces_intrinsic_catalogue
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    {P : Set E} (hP : UnitUniform 4 P) (hs : SmallFaces P) :
    ∃ Q : Set (Space 4), ∃ n : FacetLibraryName,
      UnitUniform 4 Q ∧ SmallFaces Q ∧ FacetLibraryModel n Q ∧ Congruent P Q := by
  obtain ⟨f, Q, him, hc, hQ⟩ := exists_unitUniform_intrinsic_model (n := 1) hP
  have hPQ := congruent_symm hc
  have hsQ := smallFaces_cross_congruent (uniform_finitePolytope hP.1) hPQ hs
  obtain ⟨n, hn⟩ := unitUniform4_smallFaces_catalogue classification3D classification4D hQ hsQ
  exact ⟨Q, n, hQ, hsQ, hn, hPQ⟩

end Uniform5.Composition
