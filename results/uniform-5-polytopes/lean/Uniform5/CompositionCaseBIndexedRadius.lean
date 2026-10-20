import Uniform5.CompositionCaseBTypeIRadius
import Uniform5.CompositionCaseBPartnerConfigurations

/-! Keep the actual facet parameters in the radius identity. This is
needed when a second polygon of a specific fan facet supplies the
partner-radius comparison or the family-polygon filter. -/
noncomputable section
namespace Uniform5.Composition
open Set
namespace ActualPolygonCycle
variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

/-- The radius and closability belong to the given indexed actual facets,
not merely to some existentially selected configuration. -/
theorem typeI_indexed_radius_data {n : ℕ} (hP : UnitUniform 5 P)
    (hG : PolygonFace P G n) (hn4 : n ≠ 4) (geometry : D.Stage1Geometry n)
    (q : Fin D.length → ℕ) (hq : ∀ i, 3 ≤ q i)
    (hfacet : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    (hcell : ∀ i : Fin D.length, Congruent (D.cell i) (polygonPrismModel n)) :
    CaseB.AngleCondition (CaseB.realConfig (List.ofFn q)) ∧
      CaseB.Closable (CaseB.realConfig (List.ofFn q)) ∧
      intrinsicRadius P ^ 2 = CaseB.polygonRadius n ^ 2 +
        CaseB.configRadius (CaseB.realConfig (List.ofFn q)) ^ 2 := by
  obtain ⟨_, hroot, hrad⟩ := D.typeI_configRoot hP hG hn4 geometry q hq hfacet hcell
  have hall : ∀ t ∈ List.ofFn q, 3 ≤ t := by
    intro t ht
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
    exact hq i
  have hreal : ∀ t ∈ CaseB.realConfig (List.ofFn q), 3 ≤ t := by
    intro t ht
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
    exact_mod_cast hall j hj
  have hlen : 3 ≤ (CaseB.realConfig (List.ofFn q)).length := by
    simpa [CaseB.realConfig] using D.length_ge
  letI : NeZero (List.ofFn q).length := ⟨by simp; have := D.length_ge; omega⟩
  letI : NeZero (CaseB.realConfig (List.ofFn q)).length := ⟨by omega⟩
  refine ⟨configRoot_angleCondition hreal hlen hroot,
    CaseB.closable_of_ConfigRoot hreal hroot, ?_⟩
  rw [CaseB.configRadius_realConfig_eq_of_root hall hroot]
  exact hrad

/-- Relabelling the actual configuration preserves its angle, closure,
and radius data; it does not change or invent any facet parameter. -/
theorem typeI_permuted_radius_data {n : ℕ} (hP : UnitUniform 5 P)
    (hG : PolygonFace P G n) (hn4 : n ≠ 4) (geometry : D.Stage1Geometry n)
    (q : Fin D.length → ℕ) (hq : ∀ i, 3 ≤ q i)
    (hfacet : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    (hcell : ∀ i : Fin D.length, Congruent (D.cell i) (polygonPrismModel n))
    {c : List ℕ} (hp : (List.ofFn q).Perm c) :
    CaseB.AngleCondition (CaseB.realConfig c) ∧ CaseB.Closable (CaseB.realConfig c) ∧
      intrinsicRadius P ^ 2 = CaseB.polygonRadius n ^ 2 + CaseB.configRadius (CaseB.realConfig c) ^ 2 := by
  obtain ⟨ha, hc, hr⟩ := D.typeI_indexed_radius_data hP hG hn4 geometry q hq hfacet hcell
  exact ⟨(CaseB.angleCondition_realConfig_perm hp).mp ha,
    (CaseB.closable_perm (hp.map Nat.cast)).mp hc,
    (CaseB.configRadius_realConfig_perm hp) ▸ hr⟩

/-- A specified large duoprism factor in the actual cycle has a tail from
the exact partner list. Its radius identity has the symmetric two-polygon
form required by the computed partner filter. -/
theorem typeI_paired_radius_data {n m : ℕ} (hP : UnitUniform 5 P)
    (hG : PolygonFace P G n) (hn4 : n ≠ 4) (geometry : D.Stage1Geometry n)
    (q : Fin D.length → ℕ) (hq : ∀ i, 3 ≤ q i)
    (hfacet : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    (hcell : ∀ i : Fin D.length, Congruent (D.cell i) (polygonPrismModel n))
    (hm : 17 ≤ m) (hmem : m ∈ List.ofFn q) :
    ∃ tail : List ℕ, (List.ofFn q).Perm (m :: tail) ∧ CaseB.PartnerTail m tail ∧
      CaseB.AngleCondition ((m : ℝ) :: CaseB.realConfig tail) ∧
      CaseB.Closable ((m : ℝ) :: CaseB.realConfig tail) ∧
      intrinsicRadius P ^ 2 = CaseB.polygonRadius n ^ 2 + CaseB.polygonRadius m ^ 2 +
        CaseB.delta tail m := by
  let t := (List.ofFn q).erase m
  have hp : (List.ofFn q).Perm (m :: t) := List.perm_cons_erase hmem
  obtain ⟨ha, hc, _⟩ := D.typeI_permuted_radius_data hP hG hn4 geometry q hq hfacet hcell hp
  obtain ⟨tail, ht, htail⟩ := CaseB.partnerTail_of_angle_closable hm ha hc
  have hp' := hp.trans (List.Perm.cons m ht)
  obtain ⟨ha', hc', hr⟩ := D.typeI_permuted_radius_data hP hG hn4 geometry q hq hfacet hcell hp'
  refine ⟨tail, hp', htail, ha', hc', ?_⟩
  simp only [CaseB.realConfig, List.map_cons] at hr
  unfold CaseB.delta CaseB.realConfig
  linarith

end ActualPolygonCycle
end Uniform5.Composition
