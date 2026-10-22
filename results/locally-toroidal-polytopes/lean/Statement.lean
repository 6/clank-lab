import Mathlib
import P16c.Definitions

namespace P16c
variable {K : Type*} [Field K] [CharP K 2]

/-- The group-theoretic core of the P16c construction, for every admissible pair. -/
theorem p16c_core (s u : ℕ) (hs : Odd s) (hu : Odd u)
    (hs3 : 3 ≤ s) (hu3 : 3 ≤ u) (hsu : s ≠ u)
    (l m : K) (hl : orderOf l = s) (hm : orderOf m = u) :
    let g := generators (aParam l m) (bParam l m)
      (parameters s u hs3 hu3 hsu l m hl hm).2.2.1
    (∀ i, g i ^ 2 = 1) ∧ orderOf (g 0 * g 1) = 4 ∧
      orderOf (g 1 * g 2) = 4 ∧ orderOf (g 2 * g 3) = 4 ∧
      (g 0 * g 2) ^ 2 = 1 ∧ (g 0 * g 3) ^ 2 = 1 ∧ (g 1 * g 3) ^ 2 = 1 ∧
      orderOf (g 0 * g 1 * g 2 * g 1) = s ∧ orderOf (g 1 * g 2 * g 3 * g 2) = u ∧
      Nat.card (Subgroup.closure {g 0, g 1, g 2}) = 8 * s ^ 2 ∧
      Nat.card (Subgroup.closure {g 1, g 2, g 3}) = 8 * u ^ 2 ∧
      Subgroup.closure {g 0, g 1, g 2} ⊓ Subgroup.closure {g 1, g 2, g 3} =
        Subgroup.closure {g 1, g 2} :=
  core_for_parameters s u hs hu hs3 hu3 hsu l m hl hm
end P16c
