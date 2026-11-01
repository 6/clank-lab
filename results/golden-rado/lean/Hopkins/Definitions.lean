import Mathlib

namespace Hopkins

def Valid (N : ℕ) (c : ℕ → Bool) : Prop :=
  c 1 = false ∧ ∀ i : ℕ, 1 ≤ i → i + 1 ≤ N →
    ¬ (c i = true ∧ c (i + 1) = true)

def Mono (a b N : ℕ) (c : ℕ → Bool) : Prop :=
  ∃ x y z : ℕ, 1 ≤ x ∧ x ≤ N ∧ 1 ≤ y ∧ y ≤ N ∧
    1 ≤ z ∧ z ≤ N ∧ a * x + b * y = z ∧ c x = c y ∧ c y = c z

def Forces (a b N : ℕ) : Prop :=
  ∀ c : ℕ → Bool, Valid N c → Mono a b N c

def ForcingSet (a b : ℕ) : Set ℕ := {N | 1 ≤ N ∧ Forces a b N}

noncomputable def R0phi (a b : ℕ) : ℕ := sInf (ForcingSet a b)

def lowerColor (a ell t : ℕ) : Bool :=
  decide (a ∣ t ∧ a * (ell + 1) ≤ t)

end Hopkins
