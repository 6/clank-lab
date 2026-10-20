import Uniform5.CaseBMetric

/-!
The named external inputs of Case B, as propositions, not new logical
constants. `B2`, `P1`, `W`, `PartnerRadiusFilter`, `Classification3D` and
`Classification4D` must be supplied by a caller. No result in this file
asserts that the computations or the cited classifications have been proved
in Lean. The counts, exceptional families, limits, and integer-only slices
are retained in the statements.
-/

noncomputable section
open scoped BigOperators

namespace Uniform5.CaseB

noncomputable def configArcSum (c : List ℝ) (S : ℝ) : ℝ :=
  (c.map (fun q => 2 * Real.arcsin (Real.cos (Real.pi / q) / S))).sum

noncomputable def configMax (c : List ℝ) : ℝ :=
  (c.map (fun q => Real.cos (Real.pi / q))).foldr max 0

noncomputable def AngleCondition (c : List ℝ) : Prop :=
  (∀ q ∈ c, 3 ≤ q) ∧ 3 ≤ c.length ∧ c.length ≤ 5 ∧
    (c.map (fun q => 1 - 2 / q)).sum < 2

noncomputable def Closable (c : List ℝ) : Prop := 2 * Real.pi < configArcSum c (configMax c)

noncomputable def ConfigRoot (c : List ℝ) (S : ℝ) : Prop :=
  configMax c < S ∧ S < 1 ∧ configArcSum c S = 2 * Real.pi

/-- The paper's radius, defined from a root rather than a numerical oracle.
Outside the root domain its arbitrary value is zero. All uses are guarded. -/
noncomputable def configRadius (c : List ℝ) : ℝ := by
  classical
  exact if h : ∃ S, ConfigRoot c S then
    1 / (2 * Real.sqrt (1 - (Classical.choose h) ^ 2)) else 0

noncomputable def realConfig (c : List ℕ) : List ℝ := c.map Nat.cast

noncomputable def delta (tail : List ℕ) (n : ℝ) : ℝ :=
  configRadius (n :: realConfig tail) ^ 2 - polygonRadius n ^ 2

noncomputable def FamilyPolygon (q : ℕ) : Prop := q ∈ ([7, 9, 11, 12, 13, 14, 15, 16] : List ℕ)

noncomputable def ExceptionalPolygon (q : ℕ) : Prop := q ∈ ([3, 4, 5, 6, 8, 10] : List ℕ)

/-- The full polynomial, including all roots in `(-1,1)`, not only the
unsquared geometric branch. The cancelled `(3,3)` factor is nonzero there. -/
noncomputable def TypeIIIPolynomial (n : ℝ) (q₁ q₂ : ℕ) (γ : ℝ) : ℝ :=
  let c₁ := Real.cos (Real.pi * (1 - 2 / (q₁ : ℝ)))
  let c₂ := Real.cos (Real.pi * (1 - 2 / (q₂ : ℝ)))
  let N := 1 - γ ^ 2 - c₁ ^ 2 - c₂ ^ 2 + 2 * γ * c₁ * c₂
  let M := 1 + γ - c₁ - c₂
  antiprismHeightSq n * N * (1 + γ) - M ^ 2 * (1 - γ)

noncomputable def TypeIIIPair (q₁ q₂ : ℕ) : Prop :=
  (q₁ = 3 ∧ q₂ ∈ ([3, 4, 5] : List ℕ)) ∨
    (q₂ = 3 ∧ q₁ ∈ ([3, 4, 5] : List ℕ))

/-- Computation B2. `Ω` is the union of the root intervals in `def:omega`.
Polygon parameters are integers; configuration entries are at least three.
The third clause deliberately includes non-geometric polynomial roots. -/
structure B2 (Ω : Set ℝ) : Prop where
  type_i : ∀ (n : ℕ), 17 ≤ n → ∀ c : List ℕ,
    AngleCondition (realConfig c) → Closable (realConfig c) →
    Real.sqrt (polygonRadius n ^ 2 + configRadius (realConfig c) ^ 2) ∉ Ω
  type_ii : ∀ (n q : ℕ), 17 ≤ n → 3 ≤ q →
    Real.sqrt (antiprismRadiusSq n + polygonRadius q ^ 2) ∉ Ω
  type_iii : ∀ (n q₁ q₂ : ℕ), 17 ≤ n → TypeIIIPair q₁ q₂ →
    ∀ γ : ℝ, -1 < γ → γ < 1 → TypeIIIPolynomial n q₁ q₂ γ = 0 →
    Real.sqrt (antiprismRadiusSq n + 1 / (2 * (1 + γ))) ∉ Ω

/-- Canonical cyclic configurations identify rotations and reversal, as in
the computation. This definition does not identify arbitrary permutations. -/
noncomputable def CanonicalCycle (c : List ℕ) : Prop :=
  ∀ i < c.length,
    (c = c.rotate i ∨ List.Lex (· < ·) c (c.rotate i)) ∧
    (c = c.reverse.rotate i ∨ List.Lex (· < ·) c (c.reverse.rotate i))

noncomputable def SmallConfiguration (c : List ℕ) : Prop :=
  CanonicalCycle c ∧ AngleCondition (realConfig c) ∧ ∀ q ∈ c, q ≤ 16

/-- The numerical separation tested for a family polygon in (P1).
All finite comparisons retain the lower limit 17 on the large polygon. -/
noncomputable def P1Separated (c : List ℕ) (q : ℕ) : Prop :=
  let X := configRadius (realConfig c) ^ 2 - polygonRadius q ^ 2
  X ≠ antiprismHeightSq q / 4 ∧ X ≠ 1 / 4 ∧
  X ∉ Set.Icc (186963 / 1000000 : ℝ) (3 / 16) ∧
  X ∉ Set.Icc (1 / 3 : ℝ) (337262 / 1000000) ∧
  (∀ n : ℕ, 17 ≤ n → n ≤ 41 → X ≠ delta [3, 7] n) ∧
  (∀ n : ℕ, 17 ≤ n → n ≤ 23 → X ≠ delta [3, 8] n) ∧
  X ≠ delta [3, 9] 17 ∧
  (∀ n : ℕ, 17 ≤ n → n ≤ 19 → X ≠ delta [4, 5] n)

/-- Computation (P1), including the count and survivor clauses.
The finite sets are computational data; their semantic coverage is required.
The all-integer delta ranges are the ranges explicitly asserted in P1 and
checked by the closed-form part of the P1 computation. -/
structure P1 where
  configurations : Finset (List ℕ)
  closable : Finset (List ℕ)
  nonclosable : Finset (List ℕ)
  degenerate : Finset (List ℕ)
  family : Finset (List ℕ)
  excluded : Finset (List ℕ)
  configurations_iff : ∀ c, c ∈ configurations ↔ SmallConfiguration c
  closable_iff : ∀ c, c ∈ closable ↔ c ∈ configurations ∧ Closable (realConfig c)
  nonclosable_iff : ∀ c, c ∈ nonclosable ↔ c ∈ configurations ∧
    configArcSum (realConfig c) (configMax (realConfig c)) < 2 * Real.pi
  degenerate_iff : ∀ c, c ∈ degenerate ↔ c ∈ configurations ∧
    configArcSum (realConfig c) (configMax (realConfig c)) = 2 * Real.pi
  family_iff : ∀ c, c ∈ family ↔ c ∈ closable ∧ ∃ q ∈ c, FamilyPolygon q
  excluded_subset : excluded ⊆ family
  configurations_count : configurations.card = 168
  closable_count : closable.card = 137
  nonclosable_count : nonclosable.card = 28
  degenerate_count : degenerate.card = 3
  family_count : family.card = 83
  excluded_count : excluded.card = 67
  separation : ∀ c ∈ excluded, ∃ q ∈ c, FamilyPolygon q ∧ P1Separated c q
  delta44 : ∀ n : ℕ, 17 ≤ n → delta [4, 4] n = 1 / 4
  delta333_range : ∀ n : ℕ, 17 ≤ n →
    delta [3, 3, 3] n ∈ Set.Icc (186963 / 1000000 : ℝ) (3 / 16)
  delta36_range : ∀ n : ℕ, 17 ≤ n →
    delta [3, 6] n ∈ Set.Icc (1 / 3 : ℝ) (337262 / 1000000)
  survivors : ∀ c, c ∈ family ∧ c ∉ excluded ↔
    ∃ q, FamilyPolygon q ∧ (c = [4, 4, q] ∨ c = [3, 3, 3, q])

theorem p1_remaining_count (p1 : P1) : (p1.closable \ p1.excluded).card = 70 := by
  have hsub : p1.excluded ⊆ p1.closable := by
    intro c hc
    exact ((p1.family_iff c).mp (p1.excluded_subset hc)).1
  rw [Finset.card_sdiff hsub, p1.closable_count, p1.excluded_count]

/-- `none` is the limiting parameter infinity in the compact charts for W. -/
abbrev PolygonParameter := Option ℝ

noncomputable def LargeParameter : PolygonParameter → Prop
  | none => True
  | some n => 17 ≤ n

inductive WFan
  | unpairedI (c : List ℕ)
  | unpairedII (q : ℕ)
  | unpairedIII (q₁ q₂ : ℕ)
  | pairedI (m : PolygonParameter) (tail : List ℕ)
  | pairedII (m : PolygonParameter)

noncomputable def BoundedPaired (m : ℕ) (tail : List ℕ) : Prop :=
  17 ≤ m ∧ ((tail = [3, 7] ∧ m ≤ 41) ∨ (tail = [3, 8] ∧ m ≤ 23) ∨
    (tail = [3, 9] ∧ m = 17) ∨ (tail = [4, 5] ∧ m ≤ 19))

noncomputable def ExceptionalPaired (m : ℕ) (tail : List ℕ) : Prop :=
  (tail = [3, 7] ∧ 38 ≤ m ∧ m ≤ 41) ∨
  (tail = [3, 8] ∧ m = 23) ∨ (tail = [3, 9] ∧ m = 17) ∨
  (tail = [4, 5] ∧ m = 19)

/-- Canonical representatives of the possible partner tails. Reversing a
two-entry tail gives the same cyclic configuration; the paper lists it once. -/
noncomputable def PartnerTail (n : ℕ) (tail : List ℕ) : Prop :=
  tail ∈ ([[4, 4], [3, 3, 3], [3, 6]] : List (List ℕ)) ∨ BoundedPaired n tail

/-- The exact list of Computation W: the seven exceptional integer fans
are included only on the diagonal `n=m`; no real-m extension is asserted. -/
noncomputable def WListed (p1 : P1) (n : PolygonParameter) : WFan → Prop
  | .unpairedI c => c ∈ p1.closable ∧ c ∉ p1.excluded
  | .unpairedII q => 3 ≤ q ∧ q ≤ 16
  | .unpairedIII q₁ q₂ => TypeIIIPair q₁ q₂
  | .pairedII m => LargeParameter m
  | .pairedI m tail =>
      (LargeParameter m ∧ tail ∈ ([[4, 4], [3, 3, 3], [3, 6]] : List (List ℕ))) ∨
      (∃ k : ℕ, m = some (k : ℝ) ∧ BoundedPaired k tail ∧
        (ExceptionalPaired k tail → n = some (k : ℝ)))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Geometric data of one fan. The closed halfspaces are its inner sides;
`dist p v=1 ∧ dist p c=R` is exactly the paper's VF sphere description.
The special-pair relation consists of e, the partner edge if present, and
the type-(i) diagonals, as supplied by the geometric fan constructor. -/
structure WFanGeometry (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  v : E
  centre : E
  radius : ℝ
  vertices : Finset E
  ends : Finset E
  halfspaces : Set (Set E)
  specialPair : E → E → Prop

noncomputable def WFanGeometry.Admissible (F : WFanGeometry E) (p : E) : Prop :=
  dist p F.v = 1 ∧ dist p F.centre = F.radius ∧
    (∀ H ∈ F.halfspaces, p ∈ H) ∧ ∀ a ∈ F.vertices, 1 ≤ dist p a

noncomputable def WFanGeometry.Allowed (F : WFanGeometry E) (p : E) : Prop :=
  p ∈ F.vertices ∧ p ∉ F.ends

/-- Computation W, over the actual fan charts, with both its clauses. -/
structure W (p1 : P1) (chart : PolygonParameter → WFan → WFanGeometry E) : Prop where
  no_long_pair : ∀ n f, LargeParameter n → WListed p1 n f → ∀ p p',
    let F := chart n f
    (F.Admissible p ∨ F.Allowed p) → (F.Admissible p' ∨ F.Allowed p') →
    chord 17 ≤ dist p p' → p ∈ F.vertices ∧ p' ∈ F.vertices
  fan_distances : ∀ n f, LargeParameter n → WListed p1 n f → ∀ p ∈ (chart n f).vertices,
    ∀ p' ∈ (chart n f).vertices, ¬ (chart n f).specialPair p p' → dist p p' < chord 17

/-- Possible partner radius equations from the partner's type (i)/(ii).
Type (i) includes the angle and closability conditions. -/
noncomputable def PartnerEquation (n m : ℕ) (c₁ : List ℕ) : Prop :=
  (∃ c₂ : List ℕ, PartnerTail n c₂ ∧ AngleCondition ((n : ℝ) :: realConfig c₂) ∧
    Closable ((n : ℝ) :: realConfig c₂) ∧ delta c₁ m = delta c₂ n) ∨
    delta c₁ m = antiprismHeightSq m / 4

/-- The computed part of `lem:partner`, stated separately from the radius
comparison that supplies its equation. -/
structure PartnerRadiusFilter : Prop where
  exclude_ii : ∀ m c₁, ExceptionalPaired m c₁ →
    delta c₁ m ≠ antiprismHeightSq m / 4
  force_equal : ∀ (n m : ℕ) (c₁ c₂ : List ℕ), 17 ≤ n → ExceptionalPaired m c₁ →
    PartnerTail n c₂ →
    AngleCondition ((n : ℝ) :: realConfig c₂) → Closable ((n : ℝ) :: realConfig c₂) →
    delta c₁ m = delta c₂ n → c₂ = c₁ ∧ n = m

/-- The elementary partner-radius subtraction, before the computed filter. -/
theorem partner_radius_comparison {R rn rm A B : ℝ}
    (h₁ : R ^ 2 = rn ^ 2 + rm ^ 2 + A)
    (h₂ : R ^ 2 = rm ^ 2 + rn ^ 2 + B) : A = B := by linarith

theorem exceptional_partner_is_diagonal (filter : PartnerRadiusFilter)
    {n m : ℕ} {c₁ : List ℕ} (hn : 17 ≤ n) (he : ExceptionalPaired m c₁)
    (h : PartnerEquation n m c₁) : n = m := by
  rcases h with ⟨c₂, ht, ha, hc, heq⟩ | heq
  · exact (filter.force_equal n m c₁ c₂ hn he ht ha hc heq).2
  · exact (filter.exclude_ii m c₁ he heq).elim

/-- A semantic interface for the two cited classifications. Its predicates
are interpreted as congruence to the indicated actual model families. -/
structure ClassificationModels (P₃ P₄ : Type*) where
  uniform3 : P₃ → Prop
  uniform4 : P₄ → Prop
  congruent3 : P₃ → P₃ → Prop
  sameVertexConfiguration : P₃ → P₃ → Prop
  hasPolygon3 : P₃ → ℕ → Prop
  hasPolygon4 : P₄ → ℕ → Prop
  platonic : P₃ → Prop
  archimedean : Fin 13 → P₃ → Prop
  prism : ℕ → P₃ → Prop
  antiprism : ℕ → P₃ → Prop
  wythoff4 : Fin 5 → P₄ → Prop
  snub24 : P₄ → Prop
  grandAntiprism : P₄ → Prop
  polyhedronPrism : P₃ → P₄ → Prop
  duoprism : ℕ → ℕ → P₄ → Prop
  antiprismPrism : ℕ → P₄ → Prop

/-- Fact 3-D: Platonic, the 13 Archimedean solids, prisms q≥3,
antiprisms q≥4; vertex-configuration uniqueness; the family-polygon clause. -/
structure Classification3D {P₃ P₄ : Type*} (M : ClassificationModels P₃ P₄) : Prop where
  exhaustive : ∀ P, M.uniform3 P → M.platonic P ∨ (∃ i, M.archimedean i P) ∨
    (∃ q, 3 ≤ q ∧ M.prism q P) ∨ (∃ q, 4 ≤ q ∧ M.antiprism q P)
  unique_configuration : ∀ P Q, M.uniform3 P → M.uniform3 Q →
    M.sameVertexConfiguration P Q → M.congruent3 P Q
  family_polygon : ∀ P q, M.uniform3 P → M.hasPolygon3 P q → ¬ ExceptionalPolygon q →
    M.prism q P ∨ M.antiprism q P

/-- Fact 4-D. `wythoff4` indexes A4, B4, D4, F4, H4 in that order. -/
structure Classification4D {P₃ P₄ : Type*} (M : ClassificationModels P₃ P₄) : Prop where
  exhaustive : ∀ P, M.uniform4 P → (∃ i, M.wythoff4 i P) ∨ M.snub24 P ∨
    M.grandAntiprism P ∨ (∃ Q, M.uniform3 Q ∧ M.polyhedronPrism Q P) ∨
    (∃ p q, 3 ≤ p ∧ 3 ≤ q ∧ M.duoprism p q P)
  family_polygon : ∀ P q, M.uniform4 P → M.hasPolygon4 P q → ¬ ExceptionalPolygon q →
    (∃ p, 3 ≤ p ∧ M.duoprism q p P) ∨ M.antiprismPrism q P

end Uniform5.CaseB
