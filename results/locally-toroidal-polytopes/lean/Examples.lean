import Main
import StatementTorus

/-! Small checks of the quotient geometry, the reflection convention, and the
parameter scope. These examples are checked by the default Lake build. -/

namespace P16c

-- The renamed reflection is exactly the original coordinate permutation.
example (s : ℕ) : Torus.reflectY s =
    Function.Involutive.toPerm
      (fun p : TorusVertex s => (p.1, -p.2)) (fun p => by simp) := rfl

-- Reduction modulo the lattice works in both coordinates, including negatives.
example : torusProj 3 (4, -1) = (1, 2) := by decide
example : torusProj 9 (12, -3) = (3, 6) := by decide

-- A vertex and a square of the smallest allowed toroidal map.
example : ({(0, 0)} : Set (TorusVertex 3)) ∈ torusFaces 3 := by
  simp only [torusFaces, Set.mem_union, Set.mem_range]
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨(0, 0), rfl⟩)))

example : ({(0, 0), (1, 0), (0, 1), (1, 1)} : Set (TorusVertex 3)) ∈
    torusFaces 3 := by
  simp only [torusFaces, Set.mem_union, Set.mem_range]
  exact Or.inr ⟨(0, 0), by simp⟩

-- The first reflection moves the base vertex; the period word translates it.
example : Torus.m0 3 (0, 0) = (1, 0) := by decide
example : (Torus.gen 3 0 * Torus.gen 3 1 * Torus.gen 3 2 * Torus.gen 3 1)
    (2, 0) = (0, 0) := by decide

-- The presented generators generate the whole group, directly from its definition.
example (s u : ℕ) : Subgroup.closure (Set.range (Main.r s u)) = ⊤ :=
  PresentedGroup.closure_range_of (Main.gammaRels s u)

-- Common divisors are allowed. The pair (3,9) has gcd 3.
example : Nat.gcd 3 9 = 3 := by decide

example : Nat.card (Subgroup.closure {Main.r 3 9 0, Main.r 3 9 1, Main.r 3 9 2}) = 72 := by
  have h := Main.p16c 3 9 (by decide) (by decide) (by decide) (by decide) (by decide)
  simpa using h.2.2.2.2.2.2.2.1

example (I J : Finset (Fin 4)) :
    Subgroup.closure (Main.r 9 15 '' ↑I) ⊓ Subgroup.closure (Main.r 9 15 '' ↑J) =
      Subgroup.closure (Main.r 9 15 '' ↑(I ∩ J)) := by
  exact (Main.p16c 9 15 (by decide) (by decide) (by decide) (by decide) (by decide)).2.2.2.2.2.1 I J

-- Reversing the pair is allowed too: the vertex-figure group now has order 72.
example : Nat.card (Subgroup.closure {Main.r 9 3 1, Main.r 9 3 2, Main.r 9 3 3}) = 72 := by
  have h := Main.p16c 9 3 (by decide) (by decide) (by decide) (by decide) (by decide)
  simpa using h.2.2.2.2.2.2.2.2.2

end P16c
