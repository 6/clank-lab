import Uniform5.CompositionLibraryBalls

/-! Actual cycles pass the certified angle test once their facets have
genuine canonical model matches. This is a proved geometric bridge. -/
noncomputable section
namespace Uniform5.Composition
open Set

namespace CycleModelLabels
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G}
  (L : CycleModelLabels D CellType CanonicalFacetName) (N : LibraryNumericalData)

noncomputable def certifiedLowerAngle (k i : ℕ) : ℝ :=
  if hi : i < D.length then
    (N.angleBall (L.facetLabel ⟨i, hi⟩) k (L.cellLabel i) (L.cellLabel (i + 1))).lower
  else 0

theorem certifiedLowerAngle_le (hLIB : LIB N)
    (hC : L.cellModel = cellTypeModel) (hF : L.facetModel = N.model)
    (hP : UnitUniform 5 P) {k : ℕ} (hG : PolygonFace P G k)
    {i : ℕ} (hi : i < D.length) : L.certifiedLowerAngle N k i ≤ L.angle k i := by
  have hword := L.word_occurs hP hG ⟨i, hi⟩
  rw [hC, hF] at hword
  have hmatch := L.facet_matches ⟨i, hi⟩
  rw [hF] at hmatch
  have hK := (unitUniform_cross_congruent_iff hmatch 4).mp (D.facet_unitUniform hP ⟨i, hi⟩)
  simpa only [certifiedLowerAngle, angle, dif_pos hi, hC, hF] using
    hLIB.lower_word_angle hK hword

theorem certifiedLowerAngle_sum_lt (hLIB : LIB N)
    (hC : L.cellModel = cellTypeModel) (hF : L.facetModel = N.model)
    (hP : UnitUniform 5 P) {k : ℕ} (hG : PolygonFace P G k)
    (hD : D.Stage1Geometry k) :
    (∑ i ∈ Finset.range D.length, L.certifiedLowerAngle N k i) < 2 * Real.pi :=
  L.lower_angle_sum_lt hD _ (fun _ hi => L.certifiedLowerAngle_le N hLIB hC hF hP hG hi)

end CycleModelLabels

/-- The actual polygon supplies a closed semantic word, exact closure root
and strict certified lower-angle test. The sole catalogue premise is
genuine facet congruence; none of these conclusions is assumed by LIB. -/
theorem unitUniform5_library_cycle {P G : Set (Space 5)} (hP : UnitUniform 5 P)
    {k : ℕ} (hG : PolygonFace P G k) (N : LibraryNumericalData) (hLIB : LIB N)
    (hcoverage : ∀ K, Facet P K → ∃ n, Congruent K (N.model n)) :
    ∃ D : ActualPolygonCycle P G, ∃ L : CycleModelLabels D CellType CanonicalFacetName,
      D.Stage1Geometry k ∧ L.cellModel = cellTypeModel ∧ L.facetModel = N.model ∧
      L.cellLabel D.length = L.cellLabel 0 ∧
      L.cyclicWord.Valid (fun f a b => ModelPolygonWord (N.model f) k
        (cellTypeModel a) (cellTypeModel b)) ∧
      L.cyclicWord.closure k (intrinsicRadius ∘ N.model)
        (intrinsicRadius ∘ cellTypeModel) (1 / intrinsicRadius P) = 0 ∧
      (∑ i ∈ Finset.range D.length, L.certifiedLowerAngle N k i) < 2 * Real.pi := by
  obtain ⟨D, hD⟩ := unitUniform5_stage1_geometry hP hG
  obtain ⟨L, hC, hF, hclosed⟩ := actual_cycle_exists_type_labels D hP hG N.model
    (fun i => hcoverage (D.facet i) (D.facet_incidence i).1)
  refine ⟨D, L, hD, hC, hF, hclosed, ?_, ?_,
    L.certifiedLowerAngle_sum_lt N hLIB hC hF hP hG hD⟩
  · simpa only [hC, hF] using L.cyclicWord_valid hclosed hP hG
  · simpa only [hC, hF] using L.cyclicWord_actual_root hclosed hD

end Uniform5.Composition
