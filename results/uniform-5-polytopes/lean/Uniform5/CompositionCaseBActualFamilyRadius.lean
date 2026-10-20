import Uniform5.CompositionFaceOrbits
import Uniform5.CompositionCaseBSpecifiedDuoprism
import Uniform5.CompositionCaseBTypeIIRadius
import Uniform5.CompositionCaseBP1Application
import Uniform5.CompositionProductModelIncidence
import Uniform5.CompositionProductPolygonFaces

/-! Actual other-factor polygons supply the radius alternatives in P1.
No exclusion of actual fans is supplied as a premise. -/
noncomputable section
namespace Uniform5.Composition
open Set

namespace ActualPolygonCycle
variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

theorem typeII_specified_duoprism_radius {k n : ℕ} (hP : UnitUniform 5 P)
    (hG : PolygonFace P G k) (hk : k ≠ 4) (hn : 17 ≤ n)
    (hII : D.CaseBTypeII k) (s : Fin D.length)
    (hN : Congruent (D.facet s) (duoprismModel k n)) :
    intrinsicRadius P ^ 2 = CaseB.antiprismRadiusSq k + CaseB.polygonRadius n ^ 2 := by
  obtain ⟨hlen, a, i, q, hq, ha, hi, _, hanti, hduo⟩ := hII
  have hs : s ∈ D.slotsAwayFrom a := by
    by_contra hs
    exact D.large_duoprism_slot_not_antiprism hP hG hk hn s hN (hanti s hs)
  rw [hi, Finset.mem_singleton] at hs
  subst s
  have he : q = n := D.duoprism_slot_parameter hP hG hk hq (by omega) i hduo hN
  subst q
  exact D.typeII_indexed_radius_data hP hG hk hlen a i n hq ha hi hanti hduo

/-- The precise two radius alternatives at a specified large second factor. -/
theorem specified_large_duoprism_radius (classification4D : CitedClassification4D)
    {k n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G k)
    (hk : ¬ CaseB.ExceptionalPolygon k) (hn : 17 ≤ n)
    (geometry : D.Stage1Geometry k) (s : Fin D.length)
    (hN : Congruent (D.facet s) (duoprismModel k n)) :
    (∃ tail : List ℕ, CaseB.PartnerTail n tail ∧
      CaseB.AngleCondition ((n : ℝ) :: CaseB.realConfig tail) ∧
      CaseB.Closable ((n : ℝ) :: CaseB.realConfig tail) ∧
      intrinsicRadius P ^ 2 = CaseB.polygonRadius k ^ 2 +
        CaseB.polygonRadius n ^ 2 + CaseB.delta tail n) ∨
    intrinsicRadius P ^ 2 = CaseB.antiprismRadiusSq k + CaseB.polygonRadius n ^ 2 := by
  have hk4 : k ≠ 4 := by
    intro he
    exact hk (by simp [CaseB.ExceptionalPolygon, he])
  rcases D.large_duoprism_cycle_types classification4D hP hG hk hn s hN with hI | hII
  · exact Or.inl (D.typeI_specified_duoprism_radius hP hG hk4 hn geometry hI s hN)
  · exact Or.inr (D.typeII_specified_duoprism_radius hP hG hk4 hn hII s hN)
end ActualPolygonCycle

/-- The actual congruent duoprism contains a polygon of its other factor's
size. Its face relation and side count are transported together. -/
theorem unitUniform4_duoprism_other_polygon {K : Set (Space 5)} {n q : ℕ}
    (hK : UnitUniform 4 K) (hn : 3 ≤ n) (hq : 3 ≤ q)
    (hmodel : Congruent K (duoprismModel n q)) :
    ∃ H, PolygonFace K H q := by
  have hKN := congruent_trans hmodel
    (congruent_affineIsometry_image (flattenProduct 2 2).toAffineIsometry _)
  obtain ⟨f, hf⟩ := exists_embedding_of_congruent_model (uniform_finitePolytope hK.1)
    (uniform_dimension hK.1) hKN
  let j := f.comp (flattenProduct 2 2).toAffineIsometry
  have hj : j '' duoprismModel n q = K := by
    change (f ∘ flattenProduct 2 2) '' duoprismModel n q = K
    rw [Set.image_comp]
    exact hf
  obtain ⟨H, hH⟩ := duoprism_second_polygonFace hn hq
  exact ⟨j '' H, hj ▸ embedding_polygonFace_image j hH⟩

/-- The actual other polygon has its own complete incidence cycle, and
that cycle contains the original duoprism. -/
theorem actual_duoprism_other_polygon_radius (classification4D : CitedClassification4D)
    {P K : Set (Space 5)} (hP : UnitUniform 5 P) (hK : Facet P K) {n q : ℕ}
    (hn : 17 ≤ n) (hq : 3 ≤ q) (hqN : ¬ CaseB.ExceptionalPolygon q)
    (hmodel : Congruent K (duoprismModel n q)) :
    (∃ tail : List ℕ, CaseB.PartnerTail n tail ∧
      CaseB.AngleCondition ((n : ℝ) :: CaseB.realConfig tail) ∧
      CaseB.Closable ((n : ℝ) :: CaseB.realConfig tail) ∧
      intrinsicRadius P ^ 2 = CaseB.polygonRadius q ^ 2 +
        CaseB.polygonRadius n ^ 2 + CaseB.delta tail n) ∨
    intrinsicRadius P ^ 2 = CaseB.antiprismRadiusSq q + CaseB.polygonRadius n ^ 2 := by
  obtain ⟨H, hH⟩ := unitUniform4_duoprism_other_polygon (unitUniform_facet hP hK)
    (by omega) hq hmodel
  have hHP := polygonFace_trans hK.1 hH
  obtain ⟨D, hD⟩ := unitUniform5_stage1_geometry hP hHP
  obtain ⟨s, hs⟩ := (D.facet_coverage K).mp ⟨hK, hH.1.2.1⟩
  have hswap : Congruent (D.facet s) (duoprismModel q n) := by
    rw [hs]
    exact congruent_trans hmodel (congruent_product_swap (unitPolygon n) (unitPolygon q))
  exact D.specified_large_duoprism_radius classification4D hP hHP hqN hn hD s hswap

end Uniform5.Composition
