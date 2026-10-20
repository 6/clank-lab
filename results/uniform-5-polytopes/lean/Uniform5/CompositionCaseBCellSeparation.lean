import Uniform5.CompositionCaseBCycleAngles

/-! The two concrete Case B cell families have different intrinsic radii. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem antiprismHeight_sq_lt_one {n : ℕ} (hn : 3 ≤ n) :
    antiprismHeight n ^ 2 < 1 := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have ht : 0 < Real.pi / (2 * (n : ℝ)) := div_pos Real.pi_pos (by positivity)
  have ht2 : Real.pi / (2 * (n : ℝ)) < Real.pi / 2 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
    nlinarith [Real.pi_pos]
  have hc : 0 < Real.cos (Real.pi / (2 * (n : ℝ))) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ht2⟩
  rw [antiprismHeight_sq_caseB hn]
  unfold CaseB.antiprismHeightSq
  have hh : 0 < 1 / (4 * Real.cos (Real.pi / (2 * (n : ℝ))) ^ 2) := by positivity
  linarith

/-- Actual unit uniform cells cannot belong to both families, even when their
models are placed in different ambient spaces. -/
theorem unitUniform3_prism_antiprism_disjoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {C : Set E} {n : ℕ} (hn : 3 ≤ n) (hC : UnitUniform 3 C)
    (hp : Congruent C (polygonPrismModel n)) (ha : Congruent C (antiprismModel n)) : False := by
  have hrp := congruent_polygonPrism_intrinsicRadius_sq hC hp
  have hra := congruent_antiprism_intrinsicRadius_sq hC hn ha
  rw [CaseB.antiprismRadiusSq, ← antiprismHeight_sq_caseB hn] at hra
  have hh := antiprismHeight_sq_lt_one hn
  change intrinsicRadius C ^ 2 = unitPolygonRadius n ^ 2 + antiprismHeight n ^ 2 / 4 at hra
  change intrinsicRadius C ^ 2 = unitPolygonRadius n ^ 2 + 1 / 4 at hrp
  linarith

namespace ActualPolygonCycle
variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

/-- A prism ray is exactly a ray that is not an antiprism, once the cited
classification has supplied the actual cell families. -/
theorem nonexceptional_cell_prism_iff (classification3D : CitedClassification3D)
    {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : ¬ CaseB.ExceptionalPolygon n) (i : ℕ) :
    Congruent (D.cell i) (polygonPrismModel n) ↔
      ¬ Congruent (D.cell i) (antiprismModel n) := by
  constructor
  · intro hp ha
    exact unitUniform3_prism_antiprism_disjoint (polygonFace_unitPolygon hP hG).1
      (D.cell_unitUniform hP hG i) hp ha
  · intro ha
    exact (unitUniform_three_face_polygon_family classification3D hP hG
      (D.cell_face i) (D.cell_contains i) (D.cell_dimension i) hn).resolve_right ha

end ActualPolygonCycle
end Uniform5.Composition
