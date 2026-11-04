import Mathlib

/-! Definitions for the Nash-Williams conjecture on Hamilton cycles in digraphs
(Kühn–Osthus survey, arXiv:1006.0590v1, §2.3, Conjecture 6), and the graphs `G6`, `G7`, `F u`. -/

namespace NWDigraph

/-- A loopless digraph on `n` vertices; arcs in both directions between a pair are allowed. -/
structure Digraph (n : ℕ) where
  adj : Fin n → Fin n → Bool
  loopless : ∀ v, adj v v = false

variable {n : ℕ}

/-- Out-degree `#{w | v → w}`. -/
def Digraph.outdeg (G : Digraph n) (v : Fin n) : ℕ :=
  (Finset.univ.filter fun w => G.adj v w = true).card

/-- In-degree `#{u | u → v}`. -/
def Digraph.indeg (G : Digraph n) (v : Fin n) : ℕ :=
  (Finset.univ.filter fun u => G.adj u v = true).card

/-- The degrees of all vertices, sorted nondecreasingly. -/
def sortedDegrees (d : Fin n → ℕ) : List ℕ :=
  (List.ofFn d).mergeSort fun a b => decide (a ≤ b)

/-- `dplus i` (`i = 1..n`): the `i`-th smallest out-degree. -/
def Digraph.dplus (G : Digraph n) (i : ℕ) : ℕ := (sortedDegrees G.outdeg).getD (i - 1) 0

/-- `dminus i`: the `i`-th smallest in-degree. -/
def Digraph.dminus (G : Digraph n) (i : ℕ) : ℕ := (sortedDegrees G.indeg).getD (i - 1) 0

/-- The Nash-Williams degree hypothesis. -/
def NWHyp (G : Digraph n) : Prop :=
  ∀ i, 1 ≤ i → 2 * i < n →
    (G.dplus i ≥ i + 1 ∨ G.dminus (n - i) ≥ n - i) ∧
    (G.dminus i ≥ i + 1 ∨ G.dplus (n - i) ≥ n - i)

/-- Every vertex is reachable from every other along arcs. -/
def StronglyConnected (G : Digraph n) : Prop :=
  ∀ u v, Relation.ReflTransGen (fun a b => G.adj a b = true) u v

/-- A Hamilton cycle: `c k` is the `k`-th vertex; `finRotate n k` is `k + 1 mod n`. -/
def HasHamCycle (G : Digraph n) : Prop :=
  ∃ c : Fin n ≃ Fin n, ∀ k, G.adj (c k) (c (finRotate n k)) = true

/-- A cycle (closed walk with distinct vertices `c 0, …, c (m-1)`) through `a` and `b`. -/
def CycleThrough (G : Digraph n) (a b : Fin n) : Prop :=
  ∃ (m : ℕ) (c : Fin m → Fin n), Function.Injective c ∧
    (∀ i, G.adj (c i) (c (finRotate m i)) = true) ∧ (∃ i, c i = a) ∧ ∃ j, c j = b

/-- Nash-Williams' conjecture (Kühn–Osthus, Conjecture 6). -/
def NashWilliamsConjecture : Prop :=
  ∀ n ≥ 3, ∀ G : Digraph n, StronglyConnected G → NWHyp G → HasHamCycle G

/-- The hypothesis of Kühn–Osthus–Treglown's Conjecture 6 (no strong connectivity). -/
def KOTHyp (G : Digraph n) : Prop :=
  NWHyp G ∧ (n % 2 = 0 → G.dplus (n / 2) ≥ n / 2 ∨ G.dminus (n / 2) ≥ n / 2)

/-- Kühn–Osthus–Treglown, Conjecture 6 (arXiv:0807.1827v1). -/
def KOTConjecture6 : Prop :=
  ∀ n ≥ 3, ∀ G : Digraph n, KOTHyp G → HasHamCycle G

/-- Digraph from out-neighbour lists (vertex numbers as naturals). -/
def ofOut (n : ℕ) (out : Fin n → List ℕ) (h : ∀ v, v.val ∉ out v) : Digraph n where
  adj v w := decide (w.val ∈ out v)
  loopless v := by simp [h v]

/-- The 6-vertex example. -/
def G6 : Digraph 6 :=
  ofOut 6 (fun v => ([[1,2,3,4,5],[4,5],[1,5],[1,4],[0,1,3,5],[0,1,2,4]] : List (List ℕ)).getD v [])
    (by decide)

/-- The 7-vertex example. -/
def G7 : Digraph 7 :=
  ofOut 7 (fun v => ([[1,4],[3,4],[1,3,4,5,6],[0,1,2,4,5,6],[0,1,3,5],[1,3],[1,2,3,4,5]] :
      List (List ℕ)).getD v []) (by decide)

/-- Arcs of `F u` on vertices `0..u+3`: `U = {0..u-1}` (`w = 0`), `s = u`, `t = u+1`,
`r1 = u+2`, `r2 = u+3`. -/
def Fadj (u a b : ℕ) : Prop :=
  a ≠ b ∧ (a < u ∨ (a = u ∧ (b = u + 1 ∨ b = 0)) ∨
  (a = u + 1 ∧ (b = 0 ∨ b = u + 2 ∨ b = u + 3)) ∨ ((a = u + 2 ∨ a = u + 3) ∧ u + 1 ≤ b))

instance (u a b : ℕ) : Decidable (Fadj u a b) := by unfold Fadj; infer_instance

/-- Each `U` vertex has an arc to every other vertex; `{t, r1, r2}` is complete; `s → t, w`;
`t → w`; no other arcs. -/
def F (u : ℕ) : Digraph (u + 4) where
  adj a b := decide (Fadj u a.val b.val)
  loopless a := by
    show decide (Fadj u a.val a.val) = false
    rw [decide_eq_false_iff_not]; unfold Fadj; omega

end NWDigraph
