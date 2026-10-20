import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# The finite closure filter

A side records a facet type and one of its polygon orbits. A cycle survives
one round exactly when every polygon orbit required by each of its facets
has a witness among the remaining cycles. This is the iterative filter of
`lem:filter`, separated from the geometric construction of those witnesses.

The invariant below is a proved combinatorial implication, not an external
computed input. Applying it to actual polygon cycles still requires their
library interpretation and the vertex-transitivity orbit witness.
-/

noncomputable section
namespace Uniform5.CycleFilter

variable {Cycle Side Facet : Type*}

/-- Exact side occurrences and the polygon orbits required by a facet type.
No coverage or survival assertion is part of this data. -/
structure Incidence (Cycle Side Facet : Type*) where
  sides : Cycle → Set Side
  facet : Side → Facet
  required : Facet → Set Side

namespace Incidence

/-- Simultaneous deletion in one round of the paper's closure filter. -/
noncomputable def step (D : Incidence Cycle Side Facet) (S : Finset Cycle) : Finset Cycle := by
  classical
  exact S.filter fun c => ∀ s ∈ D.sides c, ∀ r ∈ D.required (D.facet s),
    ∃ d ∈ S, r ∈ D.sides d

/-- An internally supported set of cycles: every requirement has a witness
within the set itself. The actual cycles at one vertex will have this
property once the geometric orbit witness is constructed. -/
noncomputable def Supported (D : Incidence Cycle Side Facet) (T : Set Cycle) : Prop :=
  ∀ c ∈ T, ∀ s ∈ D.sides c, ∀ r ∈ D.required (D.facet s),
    ∃ d ∈ T, r ∈ D.sides d

noncomputable def rounds (D : Incidence Cycle Side Facet) (S : Finset Cycle) :
    ℕ → Finset Cycle
  | 0 => S
  | n + 1 => D.step (D.rounds S n)

theorem step_subset (D : Incidence Cycle Side Facet) (S : Finset Cycle) :
    D.step S ⊆ S := by
  classical
  exact Finset.filter_subset _ _

theorem step_mono (D : Incidence Cycle Side Facet) {S T : Finset Cycle}
    (h : S ⊆ T) : D.step S ⊆ D.step T := by
  classical
  intro c hc
  obtain ⟨hc, hw⟩ := Finset.mem_filter.mp hc
  apply Finset.mem_filter.mpr
  refine ⟨h hc, ?_⟩
  intro s hs r hr
  obtain ⟨d, hd, hdr⟩ := hw s hs r hr
  exact ⟨d, h hd, hdr⟩

theorem supported_subset_step (D : Incidence Cycle Side Facet) {T : Set Cycle}
    (hT : D.Supported T) {S : Finset Cycle} (hsub : T ⊆ (S : Set Cycle)) :
    T ⊆ (D.step S : Set Cycle) := by
  classical
  intro c hc
  apply Finset.mem_filter.mpr
  refine ⟨hsub hc, ?_⟩
  intro s hs r hr
  obtain ⟨d, hd, hdr⟩ := hT c hc s hs r hr
  exact ⟨d, hsub hd, hdr⟩

/-- Induction over all deletion rounds: an internally supported set is
never touched. This is the finite-filter argument in `lem:filter`. -/
theorem supported_subset_rounds (D : Incidence Cycle Side Facet) {T : Set Cycle}
    (hT : D.Supported T) {S : Finset Cycle} (hsub : T ⊆ (S : Set Cycle))
    (n : ℕ) : T ⊆ (D.rounds S n : Set Cycle) := by
  induction n with
  | zero => exact hsub
  | succ n ih => exact D.supported_subset_step hT ih

theorem rounds_subset (D : Incidence Cycle Side Facet) (S : Finset Cycle) (n : ℕ) :
    D.rounds S n ⊆ S := by
  induction n with
  | zero => exact Finset.Subset.refl S
  | succ n ih => exact Finset.Subset.trans (D.step_subset _) ih

/-- Either iteration has stopped or its cardinality has decreased enough
that at most the initial number of cycles can be deleted. -/
theorem rounds_stable_or_card (D : Incidence Cycle Side Facet)
    (S : Finset Cycle) (n : ℕ) :
    D.step (D.rounds S n) = D.rounds S n ∨
      (D.rounds S n).card + n ≤ S.card := by
  classical
  induction n with
  | zero => exact Or.inr (by simp [rounds])
  | succ n ih =>
    rcases ih with h | h
    · exact Or.inl (congrArg D.step h)
    · by_cases heq : D.step (D.rounds S n) = D.rounds S n
      · exact Or.inl (congrArg D.step heq)
      · have hlt : (D.step (D.rounds S n)).card < (D.rounds S n).card := by
          apply Finset.card_lt_card
          exact (D.step_subset _).ssubset_of_ne heq
        exact Or.inr (by change (D.step (D.rounds S n)).card + (n + 1) ≤ S.card; omega)

/-- The paper's instruction 'until nothing changes' terminates within the
initial number of cycles. No algorithmic termination premise is needed. -/
theorem rounds_card_stable (D : Incidence Cycle Side Facet) (S : Finset Cycle) :
    D.step (D.rounds S S.card) = D.rounds S S.card := by
  classical
  rcases D.rounds_stable_or_card S S.card with h | h
  · exact h
  · have hz : D.rounds S S.card = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [hz]
    exact Finset.filter_empty _

noncomputable def survivors (D : Incidence Cycle Side Facet) (S : Finset Cycle) :
    Finset Cycle := D.rounds S S.card

theorem survivors_fixed (D : Incidence Cycle Side Facet) (S : Finset Cycle) :
    D.step (D.survivors S) = D.survivors S := D.rounds_card_stable S

theorem survivors_supported (D : Incidence Cycle Side Facet) (S : Finset Cycle) :
    D.Supported (D.survivors S : Set Cycle) := by
  classical
  intro c hc
  have hc' : c ∈ D.step (D.survivors S) := by rwa [D.survivors_fixed S]
  exact (Finset.mem_filter.mp hc').2

/-- The terminal output contains every internally supported subset of the
input. Thus it is the greatest such subset, independent of numeric data. -/
theorem supported_subset_survivors (D : Incidence Cycle Side Facet) {T : Set Cycle}
    (hT : D.Supported T) {S : Finset Cycle} (hsub : T ⊆ (S : Set Cycle)) :
    T ⊆ (D.survivors S : Set Cycle) := D.supported_subset_rounds hT hsub _

end Incidence
end Uniform5.CycleFilter
