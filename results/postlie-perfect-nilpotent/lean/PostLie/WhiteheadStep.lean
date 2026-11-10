import PostLie.Filtration
import PostLie.Subquotient
import PostLie.Textbook

namespace PostLie

attribute [local instance] LieRing.ofAssociativeRing

variable {k s n : Type*} [Field k] [CharZero k]
  [LieRing s] [LieAlgebra k s] [FiniteDimensional k s]
  [LieAlgebra.IsSemisimple k s]
  [LieRing n] [LieAlgebra k n] [FiniteDimensional k n]

/-- Whitehead's lemma supplies one correction in the lower-central-series induction. -/
theorem whitehead_correction (L : s →ₗ⁅k⁆ LieDerivation k n n)
    (c : s →ₗ[k] n) (hC : IsCocycle L c) (i : ℕ)
    (hc : ∀ x, c x ∈ centralTerm k n i) :
    ∃ z : n, z ∈ centralTerm k n i ∧
      ∀ x, c x + L x z ∈ centralTerm k n (i + 1) := by
  let I := (centralTerm k n i).toSubmodule
  let J := (centralTerm k n (i + 1)).toSubmodule.comap I.subtype
  let ρ := (LieDerivation.toLinearMapLieHom k n).comp L
  have hI : ∀ x v, v ∈ I → ρ x v ∈ I := by
    intro x v hv
    exact derivation_mem_centralTerm (L x) i v hv
  let ρI := subspaceRepresentation ρ I hI
  have hJ : ∀ x v, v ∈ J → ρI x v ∈ J := by
    intro x v hv
    exact derivation_mem_centralTerm (L x) (i + 1) v hv
  let ρQ := quotientRepresentation ρI J hJ
  let cI : s →ₗ[k] I := c.codRestrict I hc
  let cQ : s →ₗ[k] (I ⧸ J) := J.mkQ.comp cI
  have hCQ : ∀ x y, cQ ⁅x, y⁆ = ρQ x (cQ y) - ρQ y (cQ x) := by
    intro x y
    change J.mkQ (cI ⁅x, y⁆) = J.mkQ (ρI x (cI y)) - J.mkQ (ρI y (cI x))
    rw [← map_sub]
    apply (Submodule.Quotient.eq J).mpr
    change c ⁅x, y⁆ - (L x (c y) - L y (c x)) ∈ centralTerm k n (i + 1)
    rw [hC]
    convert bracket_mem_next i (c x) (c y) (hc y) using 1
    abel
  obtain ⟨m, hm⟩ := whitehead_first k s (I ⧸ J) ρQ cQ hCQ
  obtain ⟨w, hw⟩ := J.mkQ_surjective m
  subst m
  refine ⟨-(w : n), (centralTerm k n i).neg_mem w.property, ?_⟩
  intro x
  have hh := hm x
  change J.mkQ (cI x) = J.mkQ (ρI x w) at hh
  have hh' := (Submodule.Quotient.eq J).mp hh
  change c x - L x (w : n) ∈ centralTerm k n (i + 1) at hh'
  simpa only [map_neg, sub_eq_add_neg] using hh'

end PostLie
