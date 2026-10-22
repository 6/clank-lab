import StatementGroupForm
import P16c.MainSupport

/-! # P16c, the final statement

This file states the claim using Mathlib's definitions only (`FreeGroup`,
`PresentedGroup`, `Subgroup.closure`, `orderOf`, `Nat.card`, `MulEquiv`). It
needs no other file of this project to be read. The proof applies
`p16c_universal_stringC` (`StatementGroupForm.lean`).

McMullen–Schulte, *Abstract Regular Polytopes* (2002), Conjecture 10C7, and
Schulte–Weiss 2006, Problem 16, conjecture that the universal regular
4-polytope `{{4,4}_(s,0),{4,4}_(u,0)}` exists for all distinct odd `s, u ≥ 3`.
By ARP 2E11 and 4A2 this is equivalent to the statement below. The group `Γ(s,u)`
is a string C-group whose facet group `⟨r0,r1,r2⟩` is `[4,4]_(s,0)`, the group of the
toroidal map `{4,4}_(s,0)`, of order `8s²` (Coxeter–Moser §8.3). Its vertex-figure
group `⟨r1,r2,r3⟩` is `[4,4]_(u,0)`, of order `8u²`. That passage is itself
proved in Lean, with the geometric toroidal maps of ARP §1D, as
`p16c_polytope_geometric` (`StatementTorus.lean`). -/

namespace P16c.Main

/-- The relators of `Γ(s,u)`: `ri²`, `(r0r1)⁴`, `(r1r2)⁴`, `(r2r3)⁴`, `(r0r2)²`, `(r0r3)²`,
`(r1r3)²`, `(r0r1r2r1)^s`, `(r1r2r3r2)^u`. -/
def gammaRels (s u : ℕ) : Set (FreeGroup (Fin 4)) :=
  let x : Fin 4 → FreeGroup (Fin 4) := FreeGroup.of
  {x 0 ^ 2, x 1 ^ 2, x 2 ^ 2, x 3 ^ 2,
    (x 0 * x 1) ^ 4, (x 1 * x 2) ^ 4, (x 2 * x 3) ^ 4,
    (x 0 * x 2) ^ 2, (x 0 * x 3) ^ 2, (x 1 * x 3) ^ 2,
    (x 0 * x 1 * x 2 * x 1) ^ s, (x 1 * x 2 * x 3 * x 2) ^ u}

/-- `Γ(s,u) = ⟨r0,r1,r2,r3 | gammaRels s u⟩`. -/
abbrev Γ (s u : ℕ) := PresentedGroup (gammaRels s u)

/-- The generators `r0, r1, r2, r3` of `Γ(s,u)`. -/
def r (s u : ℕ) (i : Fin 4) : Γ s u := PresentedGroup.of i

/-- The relators of `[4,4]_(p,0)`, the group of the toroidal map `{4,4}_(p,0)`:
`yi²`, `(y0y1)⁴`, `(y1y2)⁴`, `(y0y2)²`, `(y0y1y2y1)^p` (Coxeter–Moser (8.32)). -/
def torusRels (p : ℕ) : Set (FreeGroup (Fin 3)) :=
  let y : Fin 3 → FreeGroup (Fin 3) := FreeGroup.of
  {y 0 ^ 2, y 1 ^ 2, y 2 ^ 2, (y 0 * y 1) ^ 4, (y 1 * y 2) ^ 4, (y 0 * y 2) ^ 2,
    (y 0 * y 1 * y 2 * y 1) ^ p}

/-- `[4,4]_(p,0) = ⟨y0,y1,y2 | torusRels p⟩`. -/
abbrev TorusGroup (p : ℕ) := PresentedGroup (torusRels p)

/-- **P16c.** For all distinct odd `s, u ≥ 3`, `Γ(s,u)` is a string C-group of type
`{4,4,4}`: its generators are involutions, `r0r1`, `r1r2`, `r2r3` have order exactly 4,
nonadjacent generators commute, and `⟨ri : i ∈ I⟩ ∩ ⟨rj : j ∈ J⟩ = ⟨rk : k ∈ I ∩ J⟩`
for all `I, J ⊆ {0,1,2,3}`. Its facet group `⟨r0,r1,r2⟩` is isomorphic to `[4,4]_(s,0)`
by `yi ↦ ri` and has order `8s²`. Its vertex-figure group `⟨r1,r2,r3⟩` is isomorphic
to `[4,4]_(u,0)` by `yi ↦ r(i+1)` and has order `8u²`. -/
theorem p16c (s u : ℕ) (hs : Odd s) (hu : Odd u) (hs3 : 3 ≤ s) (hu3 : 3 ≤ u)
    (hsu : s ≠ u) :
    (∀ i, r s u i ^ 2 = 1) ∧
    orderOf (r s u 0 * r s u 1) = 4 ∧ orderOf (r s u 1 * r s u 2) = 4 ∧
    orderOf (r s u 2 * r s u 3) = 4 ∧
    (∀ i j : Fin 4, i.val + 2 ≤ j.val → r s u i * r s u j = r s u j * r s u i) ∧
    (∀ I J : Finset (Fin 4),
      Subgroup.closure (r s u '' ↑I) ⊓ Subgroup.closure (r s u '' ↑J) =
        Subgroup.closure (r s u '' ↑(I ∩ J))) ∧
    (∃ e : TorusGroup s ≃* Subgroup.closure {r s u 0, r s u 1, r s u 2},
      ∀ i : Fin 3, (e (PresentedGroup.of i) : Γ s u) = r s u i.castSucc) ∧
    Nat.card (Subgroup.closure {r s u 0, r s u 1, r s u 2}) = 8 * s ^ 2 ∧
    (∃ e : TorusGroup u ≃* Subgroup.closure {r s u 1, r s u 2, r s u 3},
      ∀ i : Fin 3, (e (PresentedGroup.of i) : Γ s u) = r s u i.succ) ∧
    Nat.card (Subgroup.closure {r s u 1, r s u 2, r s u 3}) = 8 * u ^ 2 := by
  -- The displayed relator sets are those of `Universal.rels` and `Toroid.rels`.
  have hR : gammaRels s u = Universal.rels s u := by
    ext w
    simp only [gammaRels, Universal.rels, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Fin.exists_fin_succ, Fin.exists_fin_zero]
    simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    tauto
  have hT : ∀ p, torusRels p = Toroid.rels p := by
    intro p
    ext w
    simp only [torusRels, Toroid.rels, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Fin.exists_fin_succ, Fin.exists_fin_zero]
    simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    tauto
  exact p16c_of_rels s u hs hu hs3 hu3 hsu _ _ _ hR (hT s) (hT u)

end P16c.Main
