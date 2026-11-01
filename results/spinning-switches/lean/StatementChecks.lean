import SpinningSwitches

/-! Statement correspondence and small boundary examples. -/

open SpinningSwitches

section Statement
variable {G H Ω : Type*} [Group G] [Group H] [MulAction H Ω]

example [Finite G] [Finite H] [Finite Ω] [FaithfulSMul H Ω]
    [Nontrivial G] [Nontrivial H] :
    (∃ ks : List (Ω → G), IsSurjectiveStrategy H ks) ↔
      ∃ p : ℕ, p.Prime ∧ IsPGroup p G ∧ IsPGroup p H := classification

example (ks : List (Ω → G)) : IsSurjectiveStrategy H ks ↔
    ∀ hs : List H, hs.length = ks.length → ∀ x : Ω → G,
      ∃ j ≤ ks.length, ((List.zipWith turn ks hs).take j).prod.left = x := Iff.rfl

-- The empty sequence covers the sole configuration of trivial switches.
example [Subsingleton G] : IsSurjectiveStrategy H ([] : List (Ω → G)) := by
  intro hs _ x
  exact ⟨0, le_refl 0, Subsingleton.elim _ _⟩
end Statement

-- Two binary switches with the possible interchange are solvable.
example : ∃ ks : List (Fin 2 → Equiv.Perm (Fin 2)),
    IsSurjectiveStrategy (Equiv.Perm (Fin 2)) ks := by
  have h : IsPGroup 2 (Equiv.Perm (Fin 2)) :=
    IsPGroup.of_card (n := 1) (by simp [Nat.card_eq_fintype_card, Fintype.card_perm])
  exact sufficiency Nat.prime_two h h

-- The corresponding two switches with six permutation states are not.
example : ¬ ∃ ks : List (Fin 2 → Equiv.Perm (Fin 3)),
    IsSurjectiveStrategy (Equiv.Perm (Fin 2)) ks := S3_wr_C2_unsolvable
