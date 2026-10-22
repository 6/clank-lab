import Mathlib
import P16c.Definitions
import P16c.ToroidBridge

namespace P16c

/-- The abstract square toroid is finite and has at most 8s² elements (all positive periods). -/
theorem toroid_group_bound (s : ℕ) (hs : 0 < s) :
    Finite (Toroid.G s) ∧ Nat.card (Toroid.G s) ≤ 8 * s ^ 2 :=
  Toroid.finite_card s hs

/-- Both matrix local groups are faithful realizations of the stated toroid presentations. -/
theorem p16c_toroid {K : Type*} [Field K] [CharP K 2]
    (s u : ℕ) (hs : Odd s) (hu : Odd u)
    (hs3 : 3 ≤ s) (hu3 : 3 ≤ u) (hsu : s ≠ u)
    (l m : K) (hl : orderOf l = s) (hm : orderOf m = u) :
    let g := generators (aParam l m) (bParam l m)
      (parameters s u hs3 hu3 hsu l m hl hm).2.2.1
    (∃ φ : Toroid.G s →* (Matrix (Fin 4) (Fin 4) K)ˣ,
      (∀ i : Fin 3, φ (Toroid.r s i) = g i.castSucc) ∧ Function.Injective φ ∧
        φ.range = Subgroup.closure {g 0, g 1, g 2}) ∧
    (∃ ψ : Toroid.G u →* (Matrix (Fin 4) (Fin 4) K)ˣ,
      (∀ i : Fin 3, ψ (Toroid.r u i) = g i.succ) ∧ Function.Injective ψ ∧
        ψ.range = Subgroup.closure {g 1, g 2, g 3}) :=
  p16c_toroid_bridge s u hs hu hs3 hu3 hsu l m hl hm
end P16c
