import Uniform5.CompositionCaseBActualFamilyRadius
import Uniform5.CompositionCaseBCanonicalCycle

/-! Apply P1 to the actual cyclic parameters of an unpaired type-I fan.
The radius comparisons come from actual other-factor polygon cycles. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem familyPolygon_three_nonexceptional {q : ℕ} (hq : CaseB.FamilyPolygon q) :
    3 ≤ q ∧ ¬ CaseB.ExceptionalPolygon q := by
  simp only [CaseB.FamilyPolygon, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [CaseB.ExceptionalPolygon]

namespace ActualPolygonCycle
variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

/-- Every family parameter in the actual type-I configuration has one of
the exact radius equations compared by P1. -/
theorem typeI_actual_family_equations (classification4D : CitedClassification4D)
    {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (geometry : D.Stage1Geometry n) (q : Fin D.length → ℕ) (hq : ∀ i, 3 ≤ q i)
    (hfacet : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    (hcell : ∀ i : Fin D.length, Congruent (D.cell i) (polygonPrismModel n))
    {c : List ℕ} (hp : (List.ofFn q).Perm c) :
    ∀ k ∈ c, CaseB.FamilyPolygon k → CaseB.FamilyPolygonRadiusEquation c k := by
  obtain ⟨_, _, hr⟩ := D.typeI_permuted_radius_data hP hG (by omega)
    geometry q hq hfacet hcell hp
  intro k hk hf
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp (hp.mem_iff.mpr hk)
  obtain ⟨hk3, hkN⟩ := familyPolygon_three_nonexceptional hf
  have hmodel : Congruent (D.facet i) (duoprismModel n k) := hi ▸ hfacet i
  rcases actual_duoprism_other_polygon_radius classification4D hP (D.facet_incidence i).1
    hn hk3 hkN hmodel with ⟨tail, ht, _, _, hr'⟩ | hr'
  · exact CaseB.familyPolygonRadiusEquation_of_typeI_radii hn ht hr hr'
  · exact CaseB.familyPolygonRadiusEquation_of_typeII_radius hr hr'

/-- The computed exclusion set contains no actual type-I configuration,
proved from P1 and the cited four-dimensional classification alone. -/
theorem typeI_actual_not_p1_excluded (classification4D : CitedClassification4D)
    (p1 : CaseB.P1) {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (geometry : D.Stage1Geometry n) (q : Fin D.length → ℕ) (hq : ∀ i, 3 ≤ q i)
    (hfacet : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    (hcell : ∀ i : Fin D.length, Congruent (D.cell i) (polygonPrismModel n))
    {c : List ℕ} (hp : (List.ofFn q).Perm c) : c ∉ p1.excluded :=
  p1.not_excluded_of_family_equations
    (D.typeI_actual_family_equations classification4D hP hG hn geometry q hq hfacet hcell hp)

/-- The actual unpaired type-I fan has a dihedral canonical representative
in the precise 70-configuration domain of W. -/
theorem typeI_actual_unpaired_wListed (classification4D : CitedClassification4D)
    (p1 : CaseB.P1) {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (geometry : D.Stage1Geometry n) (q : Fin D.length → ℕ) (hq : ∀ i, 3 ≤ q i)
    (hsmall : ∀ i, q i ≤ 16)
    (hfacet : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    (hcell : ∀ i : Fin D.length, Congruent (D.cell i) (polygonPrismModel n)) :
    ∃ c : List ℕ, ((List.ofFn q).IsRotated c ∨ (List.ofFn q).reverse.IsRotated c) ∧
      CaseB.WListed p1 (some (n : ℝ)) (.unpairedI c) := by
  obtain ⟨c, hp, hd, hc⟩ := CaseB.exists_canonicalCycle_perm (List.ofFn q)
  obtain ⟨ha, hclose, _⟩ := D.typeI_permuted_radius_data hP hG (by omega)
    geometry q hq hfacet hcell hp
  have hcs : CaseB.SmallConfiguration c := ⟨hc, ha, by
    intro k hk
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (hp.mem_iff.mpr hk)
    exact hsmall i⟩
  exact ⟨c, hd, p1.unpaired_wListed hcs hclose
    (D.typeI_actual_family_equations classification4D hP hG hn geometry q hq hfacet hcell hp) _⟩

end ActualPolygonCycle
end Uniform5.Composition
