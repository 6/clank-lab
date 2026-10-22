import Mathlib

namespace P16c.Universal

/-- The four-generator presentation Γ(s,u), with both toroid period words. -/
def rels (s u : ℕ) : Set (FreeGroup (Fin 4)) :=
  {w | (∃ i, w = FreeGroup.of i ^ 2) ∨
    w = (FreeGroup.of 0 * FreeGroup.of 1) ^ 4 ∨
    w = (FreeGroup.of 1 * FreeGroup.of 2) ^ 4 ∨
    w = (FreeGroup.of 2 * FreeGroup.of 3) ^ 4 ∨
    w = (FreeGroup.of 0 * FreeGroup.of 2) ^ 2 ∨
    w = (FreeGroup.of 0 * FreeGroup.of 3) ^ 2 ∨
    w = (FreeGroup.of 1 * FreeGroup.of 3) ^ 2 ∨
    w = (FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 2 * FreeGroup.of 1) ^ s ∨
    w = (FreeGroup.of 1 * FreeGroup.of 2 * FreeGroup.of 3 * FreeGroup.of 2) ^ u}

abbrev G (s u : ℕ) := PresentedGroup (rels s u)
def r (s u : ℕ) (i : Fin 4) : G s u := PresentedGroup.of i

end P16c.Universal

namespace P16c
abbrev Gamma (s u : ℕ) := Universal.G s u
end P16c
