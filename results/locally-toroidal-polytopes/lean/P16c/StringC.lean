import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Data.Finset.Lattice.Basic

namespace P16c

/-- String relations and the intersection property, including empty subsets. -/
def IsStringCGroup {G : Type*} [Group G] {n : ℕ} (g : Fin n → G) : Prop :=
  (∀ i, g i ^ 2 = 1) ∧
  (∀ i j, i.val + 2 ≤ j.val → (g i * g j) ^ 2 = 1) ∧
  (∀ I J : Finset (Fin n),
    Subgroup.closure (g '' (I : Set (Fin n))) ⊓
      Subgroup.closure (g '' (J : Set (Fin n))) =
        Subgroup.closure (g '' ((I ∩ J : Finset (Fin n)) : Set (Fin n))))

/-- The subgroup on a specified subset of the distinguished generators. -/
def parabolic {G : Type*} [Group G] {n : ℕ} (g : Fin n → G)
    (I : Finset (Fin n)) : Subgroup G := Subgroup.closure (g '' (I : Set (Fin n)))

end P16c
