import Mathlib.Order.Preorder.Chain
import Mathlib.Data.Set.Card
import Mathlib.Logic.Relation
import Mathlib.Algebra.Order.Group.End

/-! # Abstract polytopes (McMullen–Schulte, *Abstract Regular Polytopes* (ARP), §2A–2B)

A flag is a maximal chain (Mathlib's `Flag`). Two flags are adjacent if they
differ in exactly one face. Sections are Mathlib's intervals: the facet at a
face `F` of rank `n - 1` is `Set.Iic F` (the section `F/F_{-1}`), the
vertex-figure at a vertex `v` is `Set.Ici v` (the section `F_n/v`). -/

namespace P16c

/-- Two flags are adjacent if they differ in exactly one face. -/
def FlagAdjacent {P : Type*} [PartialOrder P] (Φ Ψ : Flag P) : Prop :=
  ∃ F, (Φ : Set P) \ Ψ = {F}

/-- ARP §2A: `P` is an (abstract) polytope of rank `n`, with rank function `rank`.
The rank is the usual one: by (P2) and strict monotonicity every flag meets
each rank `-1, …, n` exactly once, so `rank F` is the number of faces below
`F` in any flag through `F`, minus one. (P3) is strong flag-connectedness in
the form of ARP §2A: any two flags `Φ`, `Ψ` are joined by a sequence of
successively adjacent flags each containing `Φ ∩ Ψ`. -/
structure IsPolytope (P : Type*) [PartialOrder P] (n : ℕ) (rank : P → ℤ) : Prop where
  rank_strictMono : StrictMono rank
  rank_mem : ∀ F, -1 ≤ rank F ∧ rank F ≤ n
  /-- (P1) a least face and a greatest face. -/
  exists_least : ∃ F : P, ∀ G, F ≤ G
  exists_greatest : ∃ F : P, ∀ G, G ≤ F
  /-- (P2) every flag has exactly `n + 2` faces. -/
  flag_ncard : ∀ Φ : Flag P, (Φ : Set P).ncard = n + 2
  /-- (P3) strong flag-connectedness. -/
  strongly_flag_connected : ∀ Φ Ψ : Flag P, Relation.ReflTransGen
    (fun A B : Flag P => FlagAdjacent A B ∧ (Φ : Set P) ∩ Ψ ⊆ B) Φ Ψ
  /-- (P4) the diamond condition. -/
  diamond : ∀ F G : P, F < G → rank G = rank F + 2 → {H | F < H ∧ H < G}.ncard = 2

/-- ARP §2B: a polytope is regular if its automorphism group (the order
automorphisms) is transitive on flags. -/
def IsRegular (P : Type*) [PartialOrder P] : Prop :=
  ∀ Φ Ψ : Flag P, ∃ σ : P ≃o P, Flag.map σ Φ = Ψ

/-- ARP §2D: a covering is a surjective rap-map: a map preserving incidence
(`F ≤ G → γ F ≤ γ G`) and rank, and mapping adjacent flags to adjacent flags
(images differing in exactly one face). -/
def IsCovering {P Q : Type*} [PartialOrder P] [PartialOrder Q] (rankP : P → ℤ)
    (rankQ : Q → ℤ) (γ : P → Q) : Prop :=
  Function.Surjective γ ∧ Monotone γ ∧ (∀ F, rankQ (γ F) = rankP F) ∧
    ∀ Φ Ψ : Flag P, FlagAdjacent Φ Ψ → ∃ F, γ '' (Φ : Set P) \ γ '' (Ψ : Set P) = {F}

end P16c
