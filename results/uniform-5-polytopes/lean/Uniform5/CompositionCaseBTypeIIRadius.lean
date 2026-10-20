import Uniform5.CompositionThreeRaySpan

/-! Radius and B2 for actual Case B(ii) incidence cycles. -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace

/-- The three-slot indexing fact is a finite computation checked in Lean. -/
theorem finRotate_three_other {m : ℕ} (hm : m = 3) (a i : Fin m)
    (hi : i ≠ a) (hj : finRotate m i ≠ a) :
    finRotate m a = i ∧ finRotate m (finRotate m i) = a := by
  subst m
  revert a i
  decide

namespace ActualPolygonCycle
variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

/-- Actual normalized rays carry the same cyclic indexing as the cells. -/
theorem normalizedCellRay_rotate (hP : UnitUniform 5 P) {n : ℕ}
    (hG : PolygonFace P G n) (i : Fin D.length) :
    D.normalizedCellRay hP hG (finRotate D.length i) =
      D.normalizedCellRay hP hG (i.val + 1) :=
  cycle_apply_finRotate (by have := D.length_ge; omega) _
    (D.normalizedCellRay_closed hP hG) i

/-- The normal complement of the actual polygon has dimension three. -/
theorem polygon_normal_finrank {n : ℕ} (hG : PolygonFace P G n) :
    Module.finrank ℝ (affineSpan ℝ G).directionᗮ = 3 := by
  have hh := (affineSpan ℝ G).direction.finrank_add_finrank_orthogonal
  have hd := hG.2.1
  change Module.finrank ℝ (affineSpan ℝ G).direction = 2 at hd
  have ha : Module.finrank ℝ (Space 5) = 5 := by simp [Space]
  omega

/-- The radius formula of type (ii) follows from the actual three cells,
without supplying a metric realization or a normal-space spanning premise. -/
theorem typeII_indexed_radius_data {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn4 : n ≠ 4) (hlen : D.length = 3) (a i : Fin D.length) (q : ℕ)
    (hq : 3 ≤ q) (ha : Congruent (D.cell a) (antiprismModel n))
    (hi : D.slotsAwayFrom a = {i})
    (hanti : ∀ j, j ∉ D.slotsAwayFrom a →
      Congruent (D.facet j) (antiprismPrismModel n))
    (hduo : Congruent (D.facet i) (duoprismModel n q)) :
    intrinsicRadius P ^ 2 = CaseB.antiprismRadiusSq n + CaseB.polygonRadius q ^ 2 := by
  have hia : i ∈ D.slotsAwayFrom a := by rw [hi]; simp
  have hne := (D.slotsAwayFrom_mem a i).mp hia
  obtain ⟨hai, hiaa⟩ := finRotate_three_other hlen a i hne.1 hne.2
  let z := fun j : Fin D.length => D.normalizedCellRay hP hG j
  have hanti' (j : Fin D.length) (hj : j ∉ D.slotsAwayFrom a) :
      ⟪z j, z (finRotate D.length j)⟫ = 0 := by
    dsimp [z]
    rw [D.normalizedCellRay_rotate hP hG]
    exact D.antiprismPrism_normalizedCellRay_inner hP hG hn4 j (hanti j hj)
  have h₁ : ⟪z a, z i⟫ = 0 := by
    have ht := hanti' a (by simp [slotsAwayFrom])
    rwa [hai] at ht
  have h₂ : ⟪z a, z (finRotate D.length i)⟫ = 0 := by
    have hnot : finRotate D.length i ∉ D.slotsAwayFrom a := by
      rw [D.slotsAwayFrom_mem, hiaa]
      simp
    have ht := hanti' _ hnot
    rw [hiaa] at ht
    exact (real_inner_comm _ _).trans ht
  obtain ⟨hm₁, hm₂, hgram⟩ := D.duoprism_normalizedCellRay_metrics hP hG hn4 hq i hduo
  rw [← D.normalizedCellRay_rotate hP hG i] at hm₂ hgram
  have hcos : Real.cos (Real.pi * (1 - 2 / (q : ℝ))) ≠ 1 ∧
      Real.cos (Real.pi * (1 - 2 / (q : ℝ))) ≠ -1 := by
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hlo := CaseB.polygon_angle_lower hq
    have htheta : 0 < Real.pi * (1 - 2 / (q : ℝ)) := by nlinarith [Real.pi_pos]
    have htheta' : Real.pi * (1 - 2 / (q : ℝ)) < Real.pi := by
      have hh := div_pos (by norm_num : (0 : ℝ) < 2) hq0
      nlinarith [Real.pi_pos]
    have hleft := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) htheta'.le htheta
    have hright := Real.cos_lt_cos_of_nonneg_of_le_pi htheta.le (le_refl Real.pi) htheta'
    rw [Real.cos_zero] at hleft
    rw [Real.cos_pi] at hright
    exact ⟨ne_of_lt hleft, ne_of_gt hright⟩
  have ham := D.antiprism_normalizedCellRay hP hG a ha
  obtain ⟨w, hw, hw₁, hw₂, hhw, hW⟩ := three_ray_decomposition
    (affineSpan ℝ G).directionᗮ (polygon_normal_finrank hG)
    (D.normalizedCellRay_mem_orthogonal hP hG a).2
    (D.normalizedCellRay_mem_orthogonal hP hG i).2
    (D.normalizedCellRay_mem_orthogonal hP hG (finRotate D.length i)).2
    (D.normalizedCellRay_mem_orthogonal hP hG a).1
    ham.1 hm₁.1 hm₂.1 h₁ h₂
    (by rw [hgram]; exact hcos.1) (by rw [hgram]; exact hcos.2)
    ham.2 hm₁.2 hm₂.2
  refine CaseB.type_ii_radius (by exact_mod_cast hq)
    hm₁.1 hm₂.1 hgram hw hw₁ hw₂ ham.1 hhw hW
    (antiprismHeight_sq_caseB (polygonFace_unitPolygon hP hG).1) ?_
  have he := polygonParentOffset_norm_sq hP hG
  change intrinsicRadius P ^ 2 = unitPolygonRadius n ^ 2 + ‖polygonParentOffset hP hG‖ ^ 2
  linarith

/-- The existential Type II radius statement follows from the parameter-preserving identity. -/
theorem typeII_radius_data {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn4 : n ≠ 4) (hII : D.CaseBTypeII n) :
    ∃ q : ℕ, 3 ≤ q ∧ intrinsicRadius P ^ 2 =
      CaseB.antiprismRadiusSq n + CaseB.polygonRadius q ^ 2 := by
  obtain ⟨hlen, a, i, q, hq, ha, hi, _, hanti, hduo⟩ := hII
  exact ⟨q, hq, D.typeII_indexed_radius_data hP hG hn4 hlen a i q hq ha hi hanti hduo⟩

/-- The named B2 input excludes the actual type-(ii) parent radius. -/
theorem typeII_B2_exclusion {Ω : Set ℝ} (b2 : CaseB.B2 Ω)
    {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hII : D.CaseBTypeII n) : intrinsicRadius P ∉ Ω := by
  obtain ⟨q, hq, hr⟩ := D.typeII_radius_data hP hG (by omega) hII
  have he : intrinsicRadius P = Real.sqrt
      (CaseB.antiprismRadiusSq n + CaseB.polygonRadius q ^ 2) := by
    rw [← hr, Real.sqrt_sq (uniform_intrinsicRadius_pos hP.1).le]
  rw [he]
  exact b2.type_ii n q hn hq

end ActualPolygonCycle

/-- Actual cycle construction, F5, and the first two B2 exclusions compose
using only the named four-dimensional classification and B2. -/
theorem unitUniform5_caseB_cycle_with_typeI_typeII_exclusion {Ω : Set ℝ}
    (classification4D : CitedClassification4D) (b2 : CaseB.B2 Ω)
    {P G : Set (Space 5)} (hP : UnitUniform 5 P) {n : ℕ}
    (hG : PolygonFace P G n) (hn : 17 ≤ n) :
    ∃ D : ActualPolygonCycle P G, D.Stage1Geometry n ∧
      (D.CaseBTypeI n ∨ D.CaseBTypeII n ∨ D.CaseBTypeIII n) ∧
      ((D.CaseBTypeI n ∨ D.CaseBTypeII n) → intrinsicRadius P ∉ Ω) := by
  obtain ⟨D, hD⟩ := unitUniform5_stage1_geometry hP hG
  refine ⟨D, hD, D.nonexceptional_cycle_types classification4D hP hG
    (large_polygon_nonexceptional hn), ?_⟩
  rintro (hI | hII)
  · exact D.typeI_B2_exclusion b2 hP hG hn hD hI
  · exact D.typeII_B2_exclusion b2 hP hG hn hII

end Uniform5.Composition
