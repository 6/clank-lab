import Uniform5.CompositionGeometry
import Uniform5.CompositionModels

/-!
# The concrete conclusion of the main classification

The families are the actual sets in (K1)--(K3), up to intrinsic Euclidean
congruence. `MainClassification` states the endpoint proved conditionally in
CompositionMainClassification. In particular no geometric realization or
classification conclusion is included in the definition of `Uniform`.
-/

noncomputable section
namespace Uniform5.Composition

variable {E : Type*} [PseudoMetricSpace E]

/-- (K1): the explicitly rooted A5, B5 and D5 reflection-orbit hulls. -/
noncomputable def K1 (P : Set E) : Prop := IsWythoff5 P

/-- (K2): an actual unit-height Euclidean prism over a unit uniform
four-polytope. The factor is arbitrary in this geometric class, exactly
as in the paper's main theorem. -/
noncomputable def K2 (P : Set E) : Prop :=
  ∃ Q : Set (Space 4), UnitUniform 4 Q ∧ Congruent P (product Q unitInterval)

/-- (K3): an actual Euclidean product of a unit regular polygon and a
unit uniform polyhedron. The parameter is integral and at least three. -/
noncomputable def K3 (P : Set E) : Prop :=
  ∃ n : ℕ, 3 ≤ n ∧ ∃ Q : Set (Space 3),
    UnitUniform 3 Q ∧ Congruent P (product (unitPolygon n) Q)

noncomputable def Known (P : Set E) : Prop := K1 P ∨ K2 P ∨ K3 P

/-- The paper statement, proved from the individually named inputs in
CompositionMainClassification. There are no implicit model records or
geometric certificate fields in its quantifiers. -/
noncomputable def MainClassification : Prop :=
  ∀ P : Set (Space 5), UnitUniform 5 P → Known P

theorem k1_congruent {F : Type*} [PseudoMetricSpace F]
    {P : Set E} {Q : Set F} (h : Congruent P Q) (hQ : K1 Q) : K1 P := by
  rcases hQ with ⟨J, x, hJ, hx, hs, hg⟩ | ⟨J, x, hJ, hs, hg⟩ | ⟨J, x, hJ, hs, hg⟩
  · exact Or.inl ⟨J, x, hJ, hx, hs, congruent_trans h hg⟩
  · exact Or.inr (Or.inl ⟨J, x, hJ, hs, congruent_trans h hg⟩)
  · exact Or.inr (Or.inr ⟨J, x, hJ, hs, congruent_trans h hg⟩)

theorem k2_congruent {F : Type*} [PseudoMetricSpace F]
    {P : Set E} {Q : Set F} (h : Congruent P Q) (hQ : K2 Q) : K2 P := by
  obtain ⟨R, hR, hg⟩ := hQ
  exact ⟨R, hR, congruent_trans h hg⟩

theorem k3_congruent {F : Type*} [PseudoMetricSpace F]
    {P : Set E} {Q : Set F} (h : Congruent P Q) (hQ : K3 Q) : K3 P := by
  obtain ⟨n, hn, R, hR, hg⟩ := hQ
  exact ⟨n, hn, R, hR, congruent_trans h hg⟩

theorem known_congruent {F : Type*} [PseudoMetricSpace F]
    {P : Set E} {Q : Set F} (h : Congruent P Q) (hQ : Known Q) : Known P := by
  rcases hQ with hQ | hQ | hQ
  · exact Or.inl (k1_congruent h hQ)
  · exact Or.inr (Or.inl (k2_congruent h hQ))
  · exact Or.inr (Or.inr (k3_congruent h hQ))

/-- A concrete member of the conclusion, with its mirror equations
checked in CompositionModels. This is not a proof of its uniformity. -/
theorem cube_model_known : Known (WythoffHull rootsB5 cubeCorner) :=
  Or.inl cube_model_is_K1

/-- The genuine prism constructor satisfies the K2 membership predicate
as soon as its factor satisfies the paper's geometric definition. -/
theorem unit_prism_mem_K2 {Q : Set (Space 4)} (hQ : UnitUniform 4 Q) :
    K2 (product Q unitInterval) := ⟨Q, hQ, congruent_refl _⟩

theorem polygon_product_mem_K3 {n : ℕ} (hn : 3 ≤ n) {Q : Set (Space 3)}
    (hQ : UnitUniform 3 Q) : K3 (product (unitPolygon n) Q) :=
  ⟨n, hn, Q, hQ, congruent_refl _⟩

end Uniform5.Composition
