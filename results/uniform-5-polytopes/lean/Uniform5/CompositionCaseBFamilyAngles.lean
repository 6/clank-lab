import Uniform5.CompositionCaseBAdjacentModels

/-! Exact tangent-cone face angles of the two Case B facet families,
derived from actual adjacent-cell incidence and exact intrinsic radii. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- Complementary nonnegative squared coordinates give complementary
principal inverse-cosine angles. -/
theorem arccos_sqrt_complementary (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : 0 < s + t) :
    Real.arccos (Real.sqrt (s / (s + t))) +
      Real.arccos (Real.sqrt (t / (s + t))) = Real.pi / 2 := by
  have hu := Real.sq_sqrt (div_nonneg hs hst.le)
  have hv := Real.sq_sqrt (div_nonneg ht hst.le)
  have he : 1 - Real.sqrt (s / (s + t)) ^ 2 = Real.sqrt (t / (s + t)) ^ 2 := by
    rw [hu, hv]
    field_simp
  rw [Real.arccos_eq_arcsin (Real.sqrt_nonneg _), he,
    Real.sqrt_sq (Real.sqrt_nonneg _), Real.arccos_eq_pi_div_two_sub_arcsin]
  ring

theorem arccos_half_polygon_radius {q : ℕ} (hq : 3 ≤ q) :
    2 * Real.arccos (Real.sqrt ((1 / 4) / (unitPolygonRadius q) ^ 2)) =
      Real.pi * (1 - 2 / (q : ℝ)) := by
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have ht : 0 < Real.pi / (q : ℝ) := div_pos Real.pi_pos (by positivity)
  have ht2 : Real.pi / (q : ℝ) < Real.pi / 2 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < q)).mpr
    nlinarith [Real.pi_pos]
  have hs : 0 < Real.sin (Real.pi / (q : ℝ)) :=
    Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_pos])
  have he : (1 / 4 : ℝ) / (unitPolygonRadius q) ^ 2 = Real.sin (Real.pi / (q : ℝ)) ^ 2 := by
    unfold unitPolygonRadius
    field_simp
    <;> ring
  rw [he, Real.sqrt_sq hs.le, ← Real.cos_pi_div_two_sub,
    Real.arccos_cos (by linarith) (by linarith [Real.pi_pos])]
  ring

/-- The analytic substitution used after actual duoprism cell identification. -/
theorem facetWordAngle_duoprism_radii {n q : ℕ} {R A B : ℝ} (hq : 3 ≤ q)
    (hR : R ^ 2 = unitPolygonRadius n ^ 2 + unitPolygonRadius q ^ 2)
    (hA : A ^ 2 = unitPolygonRadius n ^ 2 + 1 / 4)
    (hB : B ^ 2 = unitPolygonRadius n ^ 2 + 1 / 4) :
    facetWordAngle n R A B = Real.pi * (1 - 2 / (q : ℝ)) := by
  unfold facetWordAngle
  rw [hR, hA, hB]
  simp only [add_sub_cancel_left]
  rw [← two_mul]
  exact arccos_half_polygon_radius hq

/-- The antiprism-prism corner is a right angle, for its two actual cell types. -/
theorem facetWordAngle_antiprismPrism_radii {n : ℕ} {R A B h : ℝ}
    (hR : R ^ 2 = unitPolygonRadius n ^ 2 + h ^ 2 / 4 + 1 / 4)
    (hA : A ^ 2 = unitPolygonRadius n ^ 2 + h ^ 2 / 4)
    (hB : B ^ 2 = unitPolygonRadius n ^ 2 + 1 / 4) :
    facetWordAngle n R A B = Real.pi / 2 := by
  have he : unitPolygonRadius n ^ 2 + h ^ 2 / 4 + 1 / 4 - unitPolygonRadius n ^ 2 =
      h ^ 2 / 4 + 1 / 4 := by ring
  unfold facetWordAngle
  rw [hR, hA, hB, he]
  simp only [add_sub_cancel_left]
  exact arccos_sqrt_complementary _ _ (by positivity) (by norm_num) (by positivity)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Fact F3's duoprism angle for an actual facet and its actual adjacent cells. -/
theorem unitUniform4_duoprism_word_angle {n q : ℕ}
    (hn : 3 ≤ n) (hq : 3 ≤ q) (hn4 : n ≠ 4)
    {K G A B : Set E} (hK : UnitUniform 4 K) (hG : PolygonFace K G n)
    (hA : Facet K A) (hB : Facet K B) (hGA : G ⊆ A) (hGB : G ⊆ B) (hAB : A ≠ B)
    (hKM : Congruent K (duoprismModel n q)) :
    facetWordAngle n (intrinsicRadius K) (intrinsicRadius A) (intrinsicRadius B) =
      Real.pi * (1 - 2 / (q : ℝ)) := by
  obtain ⟨hAM, hBM⟩ := unitUniform4_duoprism_word_cells hn hq hn4 hK hG hA hB hGA hGB hAB hKM
  exact facetWordAngle_duoprism_radii hq
    (congruent_duoprism_intrinsicRadius_sq hK hKM)
    (congruent_polygonPrism_intrinsicRadius_sq (unitUniform_facet hK hA) hAM)
    (congruent_polygonPrism_intrinsicRadius_sq (unitUniform_facet hK hB) hBM)

/-- Fact F3's antiprism-prism angle, with the two possible orders handled. -/
theorem unitUniform4_antiprismPrism_word_angle {n : ℕ}
    (hn : 3 ≤ n) (hn4 : n ≠ 4)
    {K G A B : Set E} (hK : UnitUniform 4 K) (hG : PolygonFace K G n)
    (hA : Facet K A) (hB : Facet K B) (hGA : G ⊆ A) (hGB : G ⊆ B) (hAB : A ≠ B)
    (hKM : Congruent K (antiprismPrismModel n)) :
    facetWordAngle n (intrinsicRadius K) (intrinsicRadius A) (intrinsicRadius B) = Real.pi / 2 := by
  have hrK := congruent_antiprismPrism_intrinsicRadius_sq hK hn hKM
  rw [CaseB.antiprismRadiusSq, ← antiprismHeight_sq_caseB hn] at hrK
  rcases unitUniform4_antiprismPrism_word_cells hn hn4 hK hG hA hB hGA hGB hAB hKM with
    ⟨hAM, hBM⟩ | ⟨hAM, hBM⟩
  · have hrA := congruent_antiprism_intrinsicRadius_sq (unitUniform_facet hK hA) hn hAM
    rw [CaseB.antiprismRadiusSq, ← antiprismHeight_sq_caseB hn] at hrA
    exact facetWordAngle_antiprismPrism_radii hrK hrA
      (congruent_polygonPrism_intrinsicRadius_sq (unitUniform_facet hK hB) hBM)
  · have hrB := congruent_antiprism_intrinsicRadius_sq (unitUniform_facet hK hB) hn hBM
    rw [CaseB.antiprismRadiusSq, ← antiprismHeight_sq_caseB hn] at hrB
    have hh := facetWordAngle_antiprismPrism_radii hrK hrB
      (congruent_polygonPrism_intrinsicRadius_sq (unitUniform_facet hK hA) hAM)
    simpa only [facetWordAngle, add_comm] using hh

end Uniform5.Composition
