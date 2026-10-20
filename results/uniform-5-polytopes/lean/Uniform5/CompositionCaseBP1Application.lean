import Uniform5.CompositionCaseBPartnerConfigurations

/-! Apply the numerical P1 separations to the literal two alternatives
obtained from the family polygon's own cycle. No actual fan is assumed
excluded: exclusion is deduced from its radius equations. -/
noncomputable section
namespace Uniform5.CaseB
open Set

/-- P1's computed ranges and finite comparisons cover every canonical
partner tail, including the three unbounded families. -/
theorem P1.separated_ne_partner_delta (p1 : P1) {c : List ℕ} {q n : ℕ}
    (hs : P1Separated c q) (hn : 17 ≤ n) {tail : List ℕ}
    (ht : PartnerTail n tail) :
    configRadius (realConfig c) ^ 2 - polygonRadius q ^ 2 ≠ delta tail n := by
  rcases hs with ⟨hanti, h44, h333, h36, h37, h38, h39, h45⟩
  rcases ht with ht | ⟨_, ht⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · rwa [p1.delta44 n hn]
    · intro he
      exact h333 (he ▸ p1.delta333_range n hn)
    · intro he
      exact h36 (he ▸ p1.delta36_range n hn)
  · rcases ht with ⟨rfl, hupper⟩ | ⟨rfl, hupper⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hupper⟩
    · exact h37 n hn hupper
    · exact h38 n hn hupper
    · exact h39
    · exact h45 n hn hupper

/-- Literal possible radius comparisons at a family q-gon of the fan:
the partner cycle is type (ii), or it has a canonical type-(i) tail. -/
def FamilyPolygonRadiusEquation (c : List ℕ) (q : ℕ) : Prop :=
  configRadius (realConfig c) ^ 2 - polygonRadius q ^ 2 = antiprismHeightSq q / 4 ∨
    ∃ n : ℕ, 17 ≤ n ∧ ∃ tail : List ℕ, PartnerTail n tail ∧
      configRadius (realConfig c) ^ 2 - polygonRadius q ^ 2 = delta tail n

/-- A separated configuration cannot satisfy the actual family-polygon
radius equation. -/
theorem P1.separated_no_family_equation (p1 : P1) {c : List ℕ} {q : ℕ}
    (hs : P1Separated c q) : ¬ FamilyPolygonRadiusEquation c q := by
  rintro (he | ⟨n, hn, tail, ht, he⟩)
  · exact hs.1 he
  · exact p1.separated_ne_partner_delta hs hn ht he

/-- The contradiction uses a family polygon selected by the certificate;
it does not require the caller to select the certificate's witness. -/
theorem P1.not_excluded_of_family_equations (p1 : P1) {c : List ℕ}
    (heq : ∀ q ∈ c, FamilyPolygon q → FamilyPolygonRadiusEquation c q) :
    c ∉ p1.excluded := by
  intro hc
  obtain ⟨q, hq, hf, hs⟩ := p1.separation c hc
  exact p1.separated_no_family_equation hs (heq q hq hf)

/-- Thus an actual small closable canonical configuration is in W's
unpaired type-(i) domain once its family-polygon cycles supply their
radius comparisons. -/
theorem P1.unpaired_wListed (p1 : P1) {c : List ℕ}
    (hsmall : SmallConfiguration c) (hclose : Closable (realConfig c))
    (heq : ∀ q ∈ c, FamilyPolygon q → FamilyPolygonRadiusEquation c q)
    (n : PolygonParameter) : WListed p1 n (.unpairedI c) := by
  exact ⟨(p1.closable_iff c).mpr ⟨(p1.configurations_iff c).mpr hsmall, hclose⟩,
    p1.not_excluded_of_family_equations heq⟩

/-- The family polygon's type-(i) radius identity gives the exact delta
alternative after cancellation of the common large-polygon radius. -/
theorem familyPolygonRadiusEquation_of_typeI_radii {c tail : List ℕ} {q n : ℕ} {R : ℝ}
    (hn : 17 ≤ n) (ht : PartnerTail n tail)
    (h₁ : R ^ 2 = polygonRadius n ^ 2 + configRadius (realConfig c) ^ 2)
    (h₂ : R ^ 2 = polygonRadius q ^ 2 + polygonRadius n ^ 2 + delta tail n) :
    FamilyPolygonRadiusEquation c q := by
  exact Or.inr ⟨n, hn, tail, ht, by linarith⟩

/-- The antiprism alternative has exactly h_A(q)^2/4, not h_A(q)^2/2. -/
theorem familyPolygonRadiusEquation_of_typeII_radius {c : List ℕ} {q n : ℕ} {R : ℝ}
    (h₁ : R ^ 2 = polygonRadius n ^ 2 + configRadius (realConfig c) ^ 2)
    (h₂ : R ^ 2 = antiprismRadiusSq q + polygonRadius n ^ 2) :
    FamilyPolygonRadiusEquation c q := by
  left
  unfold antiprismRadiusSq at h₂
  linarith

end Uniform5.CaseB
