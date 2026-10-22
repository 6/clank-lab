import P16c.Parameters
import P16c.Identities

namespace P16c
variable {K : Type*} [Field K] [CharP K 2]

/-- The four generators as matrix units. The proof argument affects no entries. -/
def generators (a b : K) (ha : a ≠ 0) : Fin 4 → (Mat K)ˣ :=
  ![⟨r a, r a, by simpa [pow_two] using r_sq a, by simpa [pow_two] using r_sq a⟩,
    ⟨r₁, r₁, by simpa [pow_two] using (r₁_sq (K := K)),
      by simpa [pow_two] using (r₁_sq (K := K))⟩,
    ⟨r b, r b, by simpa [pow_two] using r_sq b, by simpa [pow_two] using r_sq b⟩,
    ⟨r₃ a, r₃ a, by simpa [pow_two] using r₃_sq a ha,
      by simpa [pow_two] using r₃_sq a ha⟩]

@[simp] lemma generators_zero (a b : K) (ha : a ≠ 0) :
    ↑(generators a b ha 0) = r a := rfl
@[simp] lemma generators_one (a b : K) (ha : a ≠ 0) :
    ↑(generators a b ha 1) = (r₁ : Mat K) := rfl
@[simp] lemma generators_two (a b : K) (ha : a ≠ 0) :
    ↑(generators a b ha 2) = r b := rfl
@[simp] lemma generators_three (a b : K) (ha : a ≠ 0) :
    ↑(generators a b ha 3) = r₃ a := rfl

/-- The precise group-theoretic conclusion; expanded in Statement.lean. -/
def CoreConclusion (g : Fin 4 → (Mat K)ˣ) (s u : ℕ) : Prop :=
  (∀ i, g i ^ 2 = 1) ∧ orderOf (g 0 * g 1) = 4 ∧
    orderOf (g 1 * g 2) = 4 ∧ orderOf (g 2 * g 3) = 4 ∧
    (g 0 * g 2) ^ 2 = 1 ∧ (g 0 * g 3) ^ 2 = 1 ∧ (g 1 * g 3) ^ 2 = 1 ∧
    orderOf (g 0 * g 1 * g 2 * g 1) = s ∧ orderOf (g 1 * g 2 * g 3 * g 2) = u ∧
    Nat.card (Subgroup.closure {g 0, g 1, g 2}) = 8 * s ^ 2 ∧
    Nat.card (Subgroup.closure {g 1, g 2, g 3}) = 8 * u ^ 2 ∧
    Subgroup.closure {g 0, g 1, g 2} ⊓ Subgroup.closure {g 1, g 2, g 3} =
      Subgroup.closure {g 1, g 2}
end P16c
