import Uniform5.CompositionPrismRaySeparation
import Uniform5.CompositionTypeIIIAlgebra

/-! Actual type-(iii) cycles satisfy the polynomial and radius inputs of B2. -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace

/-- Exhaustive four-slot indexing is checked by the Lean kernel. -/
theorem finRotate_four_tail {m : ℕ} (hm : m = 4) (a i j : Fin m)
    (hij : i ≠ j)
    (ht : Finset.univ \ {a, (finRotate m).symm a} = {i, j}) :
    (finRotate m a = i ∧ finRotate m i = j ∧ finRotate m (finRotate m j) = a) ∨
    (finRotate m a = j ∧ finRotate m j = i ∧ finRotate m (finRotate m i) = a) := by
  subst m
  revert a i j
  decide

namespace ActualPolygonCycle
variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

/-- A cyclically ordered realization of the type-(iii) fan yields exactly
the polynomial and radius expressions appearing in the named B2 input. -/
theorem typeIII_ordered_radius {n q r : ℕ} (hP : UnitUniform 5 P)
    (hG : PolygonFace P G n) (hn4 : n ≠ 4) (hlen : D.length = 4)
    (a i j : Fin D.length) (hai : finRotate D.length a = i)
    (hij : finRotate D.length i = j) (hja : finRotate D.length (finRotate D.length j) = a)
    (hq : 3 ≤ q) (hr : 3 ≤ r)
    (ha : Congruent (D.cell a) (antiprismModel n))
    (haiK : Congruent (D.facet a) (antiprismPrismModel n))
    (hjaK : Congruent (D.facet (finRotate D.length j)) (antiprismPrismModel n))
    (hqi : Congruent (D.facet i) (duoprismModel n q))
    (hrj : Congruent (D.facet j) (duoprismModel n r)) :
    ∃ γ : ℝ, -1 < γ ∧ γ < 1 ∧ CaseB.TypeIIIPolynomial n q r γ = 0 ∧
      intrinsicRadius P ^ 2 = CaseB.antiprismRadiusSq n + 1 / (2 * (1 + γ)) := by
  let z := fun t : Fin D.length => D.normalizedCellRay hP hG t
  have hrot (t : Fin D.length) := D.normalizedCellRay_rotate hP hG t
  obtain ⟨hi, hj, hcq⟩ := D.duoprism_normalizedCellRay_metrics hP hG hn4 hq i hqi
  obtain ⟨hj', hk, hcr⟩ := D.duoprism_normalizedCellRay_metrics hP hG hn4 hr j hrj
  rw [← hrot i, hij] at hj hcq
  rw [← hrot j] at hk hcr
  have hh₁ : ⟪z a, z i⟫ = 0 := by
    have h := D.antiprismPrism_normalizedCellRay_inner hP hG hn4 a haiK
    rwa [← hrot a, hai] at h
  have hh₂ : ⟪z a, z (finRotate D.length j)⟫ = 0 := by
    have h := D.antiprismPrism_normalizedCellRay_inner hP hG hn4
      (finRotate D.length j) hjaK
    rw [← hrot _, hja] at h
    exact (real_inner_comm _ _).trans h
  have hik : i ≠ finRotate D.length j := by
    have h := (finRotate_ne_and_twice_ne D.length_ge i).2
    rw [hij] at h
    exact h.symm
  obtain ⟨hip, _, _⟩ := D.duoprism_slot hP hG hn4 hq i hqi
  obtain ⟨_, hkp, _⟩ := D.duoprism_slot hP hG hn4 hr j hrj
  have hcellrot := cycle_apply_finRotate (by have := D.length_ge; omega)
    D.cell D.cell_closed j
  rw [← hcellrot] at hkp
  obtain ⟨hlo, hup⟩ := D.prism_ray_inner_bounds hP hG i (finRotate D.length j) hik hip hkp
  let γ := ⟪z i, z (finRotate D.length j)⟫
  have hγ₁ : γ ≠ 1 := ne_of_lt hup
  have hγ₂ : γ ≠ -1 := ne_of_gt hlo
  have hm (t : Fin D.length) := (D.normalizedCellRay_mem_orthogonal hP hG t).2
  have hWm := (D.normalizedCellRay_mem_orthogonal hP hG a).1
  have han := D.antiprism_normalizedCellRay hP hG a ha
  have hpol := typeIII_gram_polynomial (affineSpan ℝ G).directionᗮ
    (polygon_normal_finrank hG) (hm a) (hm i) (hm (finRotate D.length j)) (hm j)
    han.1 hi.1 hk.1 hj.1 hh₁ hh₂ (rfl : ⟪z i, z (finRotate D.length j)⟫ = γ)
    hγ₁ hγ₂ hcq ((real_inner_comm _ _).trans hcr) han.2 hi.2 hk.2 hj.2
  obtain ⟨w, hw, hw₁, hw₂, hhw, hW⟩ := three_ray_decomposition
    (affineSpan ℝ G).directionᗮ (polygon_normal_finrank hG)
    (hm a) (hm i) (hm (finRotate D.length j)) hWm han.1 hi.1 hk.1 hh₁ hh₂
    hγ₁ hγ₂ han.2 hi.2 hk.2
  have hwNorm := (CaseB.two_ray_offset hi.1 hk.1 rfl hγ₁ hγ₂ hw hw₁ hw₂).2
  have hheight := antiprismHeight_sq_caseB (polygonFace_unitPolygon hP hG).1
  refine ⟨γ, hlo, hup, ?_, ?_⟩
  · simpa only [CaseB.TypeIIIPolynomial, ← hheight] using hpol
  · have hR := polygonParentOffset_norm_sq hP hG
    rw [hW, norm_add_sq_real, real_inner_smul_left, hhw, norm_smul,
      mul_pow, Real.norm_eq_abs, sq_abs, han.1, hwNorm] at hR
    change intrinsicRadius P ^ 2 = unitPolygonRadius n ^ 2 +
      CaseB.antiprismHeightSq n / 4 + 1 / (2 * (1 + γ))
    rw [← hheight]
    nlinarith only [hR]

/-- The F5 type-(iii) witness provides every geometric premise of the
radius calculation, including cyclic order and the complete parameter list. -/
theorem typeIII_radius_data {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn4 : n ≠ 4) (hIII : D.CaseBTypeIII n) :
    ∃ q r : ℕ, CaseB.TypeIIIPair q r ∧ ∃ γ : ℝ, -1 < γ ∧ γ < 1 ∧
      CaseB.TypeIIIPolynomial n q r γ = 0 ∧
      intrinsicRadius P ^ 2 = CaseB.antiprismRadiusSq n + 1 / (2 * (1 + γ)) := by
  obtain ⟨hlen, a, i, j, q, r, hij, hq, hr, hp, ha, ht, _, hanti, hqi, hrj⟩ := hIII
  have haiK := hanti a (by simp [slotsAwayFrom])
  have hlast (t : Fin D.length) (ht : finRotate D.length (finRotate D.length t) = a) :
      Congruent (D.facet (finRotate D.length t)) (antiprismPrismModel n) := by
    apply hanti
    rw [D.slotsAwayFrom_mem, ht]
    simp
  rcases finRotate_four_tail hlen a i j hij ht with ⟨hai, hij, hja⟩ | ⟨haj, hji, hia⟩
  · exact ⟨q, r, hp, D.typeIII_ordered_radius hP hG hn4 hlen a i j hai hij hja
      hq hr ha haiK (hlast j hja) hqi hrj⟩
  · have hp' : CaseB.TypeIIIPair r q := hp.elim Or.inr Or.inl
    exact ⟨r, q, hp', D.typeIII_ordered_radius hP hG hn4 hlen a j i haj hji hia
      hr hq ha haiK (hlast i hia) hrj hqi⟩

/-- The named all-root B2 clause applies to the actual type-(iii) radius. -/
theorem typeIII_B2_exclusion {Ω : Set ℝ} (b2 : CaseB.B2 Ω)
    {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hIII : D.CaseBTypeIII n) : intrinsicRadius P ∉ Ω := by
  obtain ⟨q, r, hp, γ, hlo, hup, hpoly, hrad⟩ := D.typeIII_radius_data hP hG (by omega) hIII
  have he : intrinsicRadius P = Real.sqrt
      (CaseB.antiprismRadiusSq n + 1 / (2 * (1 + γ))) := by
    rw [← hrad, Real.sqrt_sq (uniform_intrinsicRadius_pos hP.1).le]
  rw [he]
  exact b2.type_iii n q r hn hp γ hlo hup hpoly

end ActualPolygonCycle

/-- A polytope containing a large polygon has no radius in Ω: actual
incidence supplies the cycle, F5 supplies its case, and B2 excludes all three. -/
theorem unitUniform5_largePolygon_radius_not_mem {Ω : Set ℝ}
    (classification4D : CitedClassification4D) (b2 : CaseB.B2 Ω)
    {P G : Set (Space 5)} (hP : UnitUniform 5 P) {n : ℕ}
    (hG : PolygonFace P G n) (hn : 17 ≤ n) : intrinsicRadius P ∉ Ω := by
  obtain ⟨D, hD⟩ := unitUniform5_stage1_geometry hP hG
  rcases D.nonexceptional_cycle_types classification4D hP hG
    (large_polygon_nonexceptional hn) with hI | hII | hIII
  · exact D.typeI_B2_exclusion b2 hP hG hn hD hI
  · exact D.typeII_B2_exclusion b2 hP hG hn hII
  · exact D.typeIII_B2_exclusion b2 hP hG hn hIII

end Uniform5.Composition
