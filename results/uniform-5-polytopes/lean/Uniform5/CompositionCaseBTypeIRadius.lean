import Uniform5.CompositionCaseBTypeIAnalytic

/-! Actual all-prism cycles force the type-(i) radius used by B2. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical
open scoped BigOperators

private theorem foldr_max_lt_positive_bound (l : List ℝ) {S : ℝ} (hS : 0 < S)
    (hl : ∀ x ∈ l, x < S) : l.foldr max 0 < S := by
  induction l with
  | nil => exact hS
  | cons x l ih => exact max_lt (hl x (by simp)) (ih (fun y hy => hl y (by simp [hy])))

namespace ActualPolygonCycle
variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

/-- Specialize the already constructed actual closure equation. The domain
and facet-radius bounds establish the strict root interval internally. -/
theorem typeI_configRoot {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn4 : n ≠ 4) (geometry : D.Stage1Geometry n) (q : Fin D.length → ℕ)
    (hq : ∀ i, 3 ≤ q i)
    (hfacet : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    (hcell : ∀ i : Fin D.length, Congruent (D.cell i) (polygonPrismModel n)) :
    let S := Real.sqrt (1 - cyclePolarCosine (unitPolygonRadius n) (1 / 2)
      (1 / intrinsicRadius P) ^ 2)
    0 < S ∧ CaseB.ConfigRoot (CaseB.realConfig (List.ofFn q)) S ∧
      intrinsicRadius P ^ 2 = unitPolygonRadius n ^ 2 + CaseB.radiusFromCircle S ^ 2 := by
  let R := intrinsicRadius P
  let ρ := unitPolygonRadius n
  let p := cyclePolarCosine ρ (1 / 2) (1 / R)
  let S := Real.sqrt (1 - p ^ 2)
  have hheight (i : ℕ) (hi : i ≤ D.length) : D.height n i = 1 / 2 := by
    apply D.prism_height hP hG
    by_cases hlt : i < D.length
    · exact hcell ⟨i, hlt⟩
    · have he : i = D.length := by omega
      rw [he, D.cell_closed]
      exact hcell ⟨0, by have := D.length_ge; omega⟩
  have hangle (i : Fin D.length) :
      D.wordAngle n i = Real.pi * (1 - 2 / (q i : ℝ)) :=
    (D.duoprism_slot hP hG hn4 (hq i) i (hfacet i)).2.2
  have hS : 0 < S := by
    have hh := geometry.domain.2.1 0 (by omega)
    rw [hheight 0 (by omega)] at hh
    exact hh
  obtain ⟨_, hS1, hrad⟩ := halfHeight_circle geometry.parent_positive geometry.domain.1 hS
  change S < 1 at hS1
  change CaseB.radiusFromCircle S ^ 2 = R ^ 2 - ρ ^ 2 at hrad
  have hch (i : Fin D.length) : CaseB.polygonCos (q i) < S := by
    apply polygonCos_lt_circle_of_radius (hq i) hS.le hS1
    have hR := congruent_duoprism_intrinsicRadius_sq (D.facet_unitUniform hP i) (hfacet i)
    have hlt := geometry.facet_strict i
    have hp := geometry.facet_positive i
    rw [hrad]
    change intrinsicRadius (D.facet i) ^ 2 = ρ ^ 2 + unitPolygonRadius (q i) ^ 2 at hR
    change unitPolygonRadius (q i) ^ 2 < intrinsicRadius P ^ 2 - ρ ^ 2
    nlinarith
  have hSq : S ^ 2 = 1 - p ^ 2 := Real.sq_sqrt (Real.sqrt_pos.mp hS).le
  have hsum : (∑ i : Fin D.length, CaseB.centralArc (CaseB.polygonCos (q i)) S) =
      2 * Real.pi := by
    have hc := geometry.closure
    unfold cycleClosureFunction at hc
    have hs := sub_eq_zero.mp hc
    rw [← Fin.sum_univ_eq_sum_range] at hs
    convert hs using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hheight i i.isLt.le, hheight (i.val + 1) (by omega), hangle i]
    exact (halfHeight_summand (hq i) hS hSq (hch i)).symm
  refine ⟨hS, ⟨?_, hS1, ?_⟩, ?_⟩
  · unfold CaseB.configMax CaseB.realConfig
    rw [List.map_map, List.map_ofFn]
    apply foldr_max_lt_positive_bound _ hS
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hch i
  · simpa [CaseB.configArcSum, CaseB.realConfig, List.map_map, List.map_ofFn,
      List.sum_ofFn, CaseB.centralArc, CaseB.polygonCos, S, p, R, ρ] using hsum
  · change R ^ 2 = ρ ^ 2 + CaseB.radiusFromCircle S ^ 2
    linarith

/-- The chosen configuration radius is the actual parent-to-polygon-center
height, expressed without selecting an algebraic root. -/
theorem typeI_radius_data {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn4 : n ≠ 4) (geometry : D.Stage1Geometry n) (hI : D.CaseBTypeI n) :
    ∃ c : List ℕ, CaseB.AngleCondition (CaseB.realConfig c) ∧
      CaseB.Closable (CaseB.realConfig c) ∧
      intrinsicRadius P ^ 2 = CaseB.polygonRadius n ^ 2 + CaseB.configRadius (CaseB.realConfig c) ^ 2 := by
  obtain ⟨_, q, hq, _⟩ := hI
  obtain ⟨hS, hroot, hrad⟩ := D.typeI_configRoot hP hG hn4 geometry q
    (fun i => (hq i).1) (fun i => (hq i).2.1) (fun i => (hq i).2.2)
  let c := List.ofFn q
  have hc : ∀ t ∈ c, 3 ≤ t := by
    intro t ht
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
    exact (hq i).1
  have hreal : ∀ t ∈ CaseB.realConfig c, 3 ≤ t := by
    intro t ht
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
    exact_mod_cast hc j hj
  have hlen : 3 ≤ (CaseB.realConfig c).length := by
    simpa only [CaseB.realConfig, c, List.length_map, List.length_ofFn] using D.length_ge
  letI : NeZero c.length := ⟨by dsimp [c]; simp only [List.length_ofFn]; have := D.length_ge; omega⟩
  letI : NeZero (CaseB.realConfig c).length := ⟨by omega⟩
  refine ⟨c, configRoot_angleCondition hreal hlen hroot,
    CaseB.closable_of_ConfigRoot hreal hroot, ?_⟩
  rw [CaseB.configRadius_realConfig_eq_of_root hc hroot]
  exact hrad

/-- B2 applies directly to the actual all-prism cycle. -/
theorem typeI_B2_exclusion {Ω : Set ℝ} (b2 : CaseB.B2 Ω)
    {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (geometry : D.Stage1Geometry n) (hI : D.CaseBTypeI n) : intrinsicRadius P ∉ Ω := by
  obtain ⟨c, ha, hc, hr⟩ := D.typeI_radius_data hP hG (by omega) geometry hI
  have he : intrinsicRadius P = Real.sqrt
      (CaseB.polygonRadius n ^ 2 + CaseB.configRadius (CaseB.realConfig c) ^ 2) := by
    rw [← hr, Real.sqrt_sq (uniform_intrinsicRadius_pos hP.1).le]
  rw [he]
  exact b2.type_i n hn c ha hc

end ActualPolygonCycle

/-- Both cycle geometry and its type-(i) B2 implication are constructed from
the actual polytope. No external closure or fan chart is required. -/
theorem unitUniform5_caseB_cycle_with_typeI_exclusion {Ω : Set ℝ}
    (classification4D : CitedClassification4D) (b2 : CaseB.B2 Ω)
    {P G : Set (Space 5)} (hP : UnitUniform 5 P) {n : ℕ}
    (hG : PolygonFace P G n) (hn : 17 ≤ n) :
    ∃ D : ActualPolygonCycle P G, D.Stage1Geometry n ∧
      (D.CaseBTypeI n ∨ D.CaseBTypeII n ∨ D.CaseBTypeIII n) ∧
      (D.CaseBTypeI n → intrinsicRadius P ∉ Ω) := by
  obtain ⟨D, hD⟩ := unitUniform5_stage1_geometry hP hG
  exact ⟨D, hD, D.nonexceptional_cycle_types classification4D hP hG
    (large_polygon_nonexceptional hn), D.typeI_B2_exclusion b2 hP hG hn hD⟩

end Uniform5.Composition
