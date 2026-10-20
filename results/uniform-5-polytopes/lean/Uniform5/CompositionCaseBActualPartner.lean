import Uniform5.CompositionCaseBActualFamilyRadius

/-! The partner filter applies to the other actual polygon's radius. This
proves the integer diagonal restriction without a supplied partner equation. -/
noncomputable section
namespace Uniform5.Composition
open Set
namespace ActualPolygonCycle
variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

/-- The two actual polygon cycles produce the exact partner equation. -/
theorem typeI_actual_partnerEquation (classification4D : CitedClassification4D)
    {n m : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hm : 17 ≤ m) {tail : List ℕ}
    (hr : intrinsicRadius P ^ 2 = CaseB.polygonRadius n ^ 2 +
      CaseB.polygonRadius m ^ 2 + CaseB.delta tail m)
    (s : Fin D.length) (hM : Congruent (D.facet s) (duoprismModel n m)) :
    CaseB.PartnerEquation n m tail := by
  rcases actual_duoprism_other_polygon_radius classification4D hP (D.facet_incidence s).1
    hn (by omega) (large_polygon_nonexceptional hm) hM with
    ⟨tail', ht, ha, hc, hr'⟩ | hr'
  · exact CaseB.partnerEquation_of_typeI_radii ht ha hc hr hr'
  · exact CaseB.partnerEquation_of_typeII_radius hr hr'

/-- The actual paired type-I fan belongs to W's exact parameter domain,
including all seven exceptional integer slices restricted to n = m. -/
theorem typeI_actual_paired_wListed (classification4D : CitedClassification4D)
    (p1 : CaseB.P1) (filter : CaseB.PartnerRadiusFilter)
    {n m : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hm : 17 ≤ m) (geometry : D.Stage1Geometry n)
    (hI : D.CaseBTypeI n) (s : Fin D.length)
    (hM : Congruent (D.facet s) (duoprismModel n m)) :
    ∃ tail : List ℕ, CaseB.PartnerTail m tail ∧
      CaseB.WListed p1 (some (n : ℝ)) (.pairedI (some (m : ℝ)) tail) ∧
      (CaseB.ExceptionalPaired m tail → n = m) := by
  obtain ⟨tail, ht, _, _, hr⟩ := D.typeI_specified_duoprism_radius
    hP hG (by omega) hm geometry hI s hM
  have heq := D.typeI_actual_partnerEquation classification4D hP hG hn hm hr s hM
  exact ⟨tail, ht, CaseB.partnerTail_wListed p1 filter hn hm ht (fun _ => heq),
    fun hex => CaseB.exceptional_partner_is_diagonal filter hn hex heq⟩

end ActualPolygonCycle
end Uniform5.Composition
