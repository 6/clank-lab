import Uniform5.CaseBAngles
import Uniform5.CaseBConfig

/-! Exact partner-tail reduction from the actual angle and closure data.
The three nonclosable tails are excluded analytically, not by a new
computed input. The seven exceptional W slices are handled by the named
partner filter only after their actual radius equation is supplied. -/
noncomputable section
namespace Uniform5.CaseB
open Set

theorem angleCondition_realConfig_perm {c d : List ℕ} (hp : c.Perm d) :
    AngleCondition (realConfig c) ↔ AngleCondition (realConfig d) := by
  have hr := hp.map (fun n : ℕ => (n : ℝ))
  have hs := (hr.map (fun q : ℝ => 1 - 2 / q)).sum_eq
  simp only [AngleCondition, realConfig, hr.length_eq, hs]
  constructor <;> rintro ⟨h, hl, hu, hs⟩
  · exact ⟨fun q hq => h q (hr.mem_iff.mpr hq), hl, hu, hs⟩
  · exact ⟨fun q hq => h q (hr.mem_iff.mp hq), hl, hu, hs⟩

/-- The endpoint test for a three-entry configuration gives precisely the
strict acute inequality used by the already proved angle enumeration. -/
theorem closable_three_chord_inequality {m a b : ℕ}
    (ha : 3 ≤ a) (hab : a ≤ b) (hbm : b ≤ m)
    (hc : Closable (realConfig [m, a, b])) :
    chord m ^ 2 < chord a ^ 2 + chord b ^ 2 := by
  have hb : 3 ≤ b := ha.trans hab
  have hm : 3 ≤ m := hb.trans hbm
  have hca := polygonCos_mono ha hab
  have hcb := polygonCos_mono hb hbm
  have hbp := (polygonCos_bounds hb).1
  have hmax : configMax (realConfig [m, a, b]) = polygonCos m := by
    simp only [configMax, realConfig, List.map_cons, List.map_nil, List.foldr_cons,
      List.foldr_nil]
    change max (polygonCos m) (max (polygonCos a) (max (polygonCos b) 0)) = _
    rw [max_eq_left hbp.le, max_eq_right hca, max_eq_left hcb]
  have hsum : 2 * Real.pi < arcSum ![polygonCos a, polygonCos b, polygonCos m]
      (polygonCos m) := by
    rw [Closable, hmax] at hc
    simpa [configArcSum, realConfig, arcSum, centralArc, polygonCos,
      Fin.sum_univ_succ, add_comm, add_left_comm, add_assoc] using hc
  have hi := (triple_endpoint_criterion (polygonCos_bounds ha).1 hbp
    (hca.trans hcb) hcb).mp hsum
  change (2 * polygonCos m) ^ 2 < (2 * polygonCos a) ^ 2 + (2 * polygonCos b) ^ 2
  nlinarith

/-- Every actual paired configuration has a canonical tail from the
paper's list. This includes all integer cutoffs and proves that the three
small tails (3,3), (3,4), (3,5) cannot occur. -/
theorem partnerTail_of_angle_closable {m : ℕ} {tail : List ℕ}
    (hm : 17 ≤ m) (ha : AngleCondition (realConfig (m :: tail)))
    (hc : Closable (realConfig (m :: tail))) :
    ∃ c, tail.Perm c ∧ PartnerTail m c := by
  have ht : ∀ q ∈ tail, 3 ≤ q := by
    intro q hq
    have h := ha.1 (q : ℝ) (by simp [realConfig, hq])
    exact_mod_cast h
  have hlen : 2 ≤ tail.length := by
    have h := ha.2.1
    simp only [realConfig, List.length_map, List.length_cons] at h
    omega
  have hangle : (1 - 2 / (m : ℝ)) + angleBudget tail < 2 := by
    simpa [realConfig, List.map_map, angleBudget] using ha.2.2.2
  rcases paired_angle_cases (by exact_mod_cast hm) ht hlen hangle with htwo | hthree
  · obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp htwo
    have ha3 := ht a (by simp)
    have hb3 := ht b (by simp)
    have ordered (a b : ℕ) (ha3 : 3 ≤ a) (hab : a ≤ b)
        (hangle : (1 - 2 / (m : ℝ)) + (1 - 2 / (a : ℝ)) +
          (1 - 2 / (b : ℝ)) < 2)
        (hc : Closable (realConfig [m, a, b])) : PartnerTail m [a, b] := by
      have hcases := paired_three_angle_candidates hm ha3 hab hangle
      have hbm : b ≤ m := by rcases hcases with h | h <;> omega
      exact paired_three_partner_tail hm ha3 hab hangle
        (closable_three_chord_inequality ha3 hab hbm hc)
    by_cases hab : a ≤ b
    · refine ⟨[a, b], List.Perm.refl _, ordered a b ha3 hab ?_ hc⟩
      simpa [angleBudget, add_assoc] using hangle
    · have hp : [m, a, b].Perm [m, b, a] := List.Perm.cons m (List.Perm.swap b a [])
      refine ⟨[b, a], List.Perm.swap b a [], ordered b a hb3 (by omega) ?_ ?_⟩
      · simpa [angleBudget, add_assoc, add_comm, add_left_comm] using hangle
      · exact (closable_perm (hp.map Nat.cast)).mp hc
  · subst tail
    exact ⟨[3, 3, 3], List.Perm.refl _, Or.inl (by simp)⟩

/-- The partner-radius filter supplies exactly the diagonal parameter
restriction needed by W; no fan is declared excluded as a premise. -/
theorem partnerTail_wListed (p1 : P1) (filter : PartnerRadiusFilter)
    {n m : ℕ} {tail : List ℕ} (hn : 17 ≤ n) (hm : 17 ≤ m)
    (ht : PartnerTail m tail)
    (heq : ExceptionalPaired m tail → PartnerEquation n m tail) :
    WListed p1 (some (n : ℝ)) (.pairedI (some (m : ℝ)) tail) := by
  rcases ht with ht | ht
  · exact Or.inl ⟨by change (17 : ℝ) ≤ m; exact_mod_cast hm, ht⟩
  · refine Or.inr ⟨m, rfl, ht, ?_⟩
    intro he
    exact congrArg (fun k : ℕ => some (k : ℝ))
      (exceptional_partner_is_diagonal filter hn he (heq he))

/-- Comparing the two actual type-(i) radius identities produces the
partner equation, before any computational exclusion is used. -/
theorem partnerEquation_of_typeI_radii {n m : ℕ} {c₁ c₂ : List ℕ} {R : ℝ}
    (ht : PartnerTail n c₂) (ha : AngleCondition ((n : ℝ) :: realConfig c₂))
    (hc : Closable ((n : ℝ) :: realConfig c₂))
    (h₁ : R ^ 2 = polygonRadius n ^ 2 + polygonRadius m ^ 2 + delta c₁ m)
    (h₂ : R ^ 2 = polygonRadius m ^ 2 + polygonRadius n ^ 2 + delta c₂ n) :
    PartnerEquation n m c₁ :=
  Or.inl ⟨c₂, ht, ha, hc, partner_radius_comparison h₁ h₂⟩

/-- The type-(ii) partner gives the other literal alternative in the
paper's radius equation. -/
theorem partnerEquation_of_typeII_radius {n m : ℕ} {c₁ : List ℕ} {R : ℝ}
    (h₁ : R ^ 2 = polygonRadius n ^ 2 + polygonRadius m ^ 2 + delta c₁ m)
    (h₂ : R ^ 2 = antiprismRadiusSq m + polygonRadius n ^ 2) :
    PartnerEquation n m c₁ := by
  right
  unfold antiprismRadiusSq at h₂
  linarith

end Uniform5.CaseB
