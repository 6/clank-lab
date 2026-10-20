import Uniform5.CompositionCaseBActualP1
import Uniform5.CompositionCaseBActualPartner

/-! Exhaustive W parameter-domain coverage for the actual F5 cycle types.
All computed exclusions are discharged using their exact named inputs. -/
noncomputable section
namespace Uniform5.Composition.ActualPolygonCycle
open Set
variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

/-- Actual indexed type-I facets yield either an unpaired canonical cyclic
configuration or one of the partner tails in W, at the actual parameters. -/
theorem typeI_actual_wListed (classification4D : CitedClassification4D)
    (p1 : CaseB.P1) (filter : CaseB.PartnerRadiusFilter)
    {n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (geometry : D.Stage1Geometry n) (q : Fin D.length → ℕ) (hq : ∀ i, 3 ≤ q i)
    (hfacet : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    (hcell : ∀ i : Fin D.length, Congruent (D.cell i) (polygonPrismModel n)) :
    (∃ c : List ℕ, ((List.ofFn q).IsRotated c ∨ (List.ofFn q).reverse.IsRotated c) ∧
      CaseB.WListed p1 (some (n : ℝ)) (.unpairedI c)) ∨
    (∃ m : ℕ, ∃ tail : List ℕ, 17 ≤ m ∧ (List.ofFn q).Perm (m :: tail) ∧
      CaseB.WListed p1 (some (n : ℝ)) (.pairedI (some (m : ℝ)) tail) ∧
      (CaseB.ExceptionalPaired m tail → n = m)) := by
  classical
  by_cases hs : ∀ i, q i ≤ 16
  · exact Or.inl (D.typeI_actual_unpaired_wListed classification4D p1 hP hG hn
      geometry q hq hs hfacet hcell)
  · push_neg at hs
    obtain ⟨i, hi⟩ := hs
    have hm : 17 ≤ q i := by omega
    obtain ⟨tail, hp, ht, _, _, hr⟩ := D.typeI_paired_radius_data hP hG (by omega)
      geometry q hq hfacet hcell hm (List.mem_ofFn.mpr ⟨i, rfl⟩)
    have heq := D.typeI_actual_partnerEquation classification4D hP hG hn hm hr i (hfacet i)
    exact Or.inr ⟨q i, tail, hm, hp,
      CaseB.partnerTail_wListed p1 filter hn hm ht (fun _ => heq),
      fun hex => CaseB.exceptional_partner_is_diagonal filter hn hex heq⟩

/-- Type II uses the same actual parameter, and the cut at 17 is exhaustive. -/
theorem typeII_parameter_wListed (p1 : CaseB.P1) (n : CaseB.PolygonParameter)
    {q : ℕ} (hq : 3 ≤ q) :
    CaseB.WListed p1 n (.unpairedII q) ∨
      CaseB.WListed p1 n (.pairedII (some (q : ℝ))) := by
  by_cases hs : q ≤ 16
  · exact Or.inl ⟨hq, hs⟩
  · right
    change (17 : ℝ) ≤ q
    exact_mod_cast (show 17 ≤ q by omega)

/-- Every actual type-III pair is in W's exact unordered three-pair list. -/
theorem typeIII_actual_wListed (p1 : CaseB.P1) (n : CaseB.PolygonParameter)
    {q r : ℕ} (hpair : CaseB.TypeIIIPair q r) :
    CaseB.WListed p1 n (.unpairedIII q r) := hpair

end Uniform5.Composition.ActualPolygonCycle
