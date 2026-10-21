import DS243.PruneGeneric
import DS243.Main

/-! The weakened rules planted as errors, as propositions. -/

namespace DS243.Planted

open DS243

/-- Weakened pruning: reject a partial set once some difference occurs `λ` times (not `> λ`). -/
def WeakPrune : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Fintype A] [DecidableEq A] (lam : ℕ) (D B : Finset A),
    D ⊆ B → ∀ g : A, g ≠ 0 → (∀ g : A, g ≠ 0 → diffCountA B g = lam) → lam ≤ diffCountA D g → False

/-- Weakened leaf test: accept a leaf whose differences occur at most `λ + 1` times. -/
def WeakLeaf : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Fintype A] [DecidableEq A] (k lam : ℕ) (D : Finset A),
    D.card = k → k * k = k + lam * (Fintype.card A - 1) →
    (∀ g : A, g ≠ 0 → diffCountA D g ≤ lam + 1) → ∀ g : A, g ≠ 0 → diffCountA D g = lam

end DS243.Planted

namespace DS243.Planted

open DS243

/-- Coverage with the last range dropped. -/
def DropLastRange : Prop :=
  ∀ c, c < 8 → ∀ digits : Fin 24 → Fin 3, ∃ r, r < 1037 ∧ ∃ id, 4096 * r ≤ id ∧
    id < min (4096 * (r + 1)) 4251528 ∧ ∃ tail : Fin 12 → Fin 3,
      id / 531441 = c ∧ idDigits id tail = digits

end DS243.Planted
