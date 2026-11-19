import GCG.Potential
import GCG.Extract
import GCG.Forest

/-!
# Monotone classes of bounded game chromatic number have bounded arboricity

Final statements. The definitions they use are in `GCG/Game.lean` (`Move`, `AliceWins`,
`AliceWinsGame`, `C4Free`) and `GCG/Forest.lean` (`ArboricityLE`).
-/

namespace GCG

open Finset

/-! ## Auxiliary lemmas -/

/-- Twice the number of edges is the degree sum (`Set.ncard` form). -/
theorem two_mul_ncard_edgeSet {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : 2 * G.edgeSet.ncard = ∑ v, G.degree v := by
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges, ← SimpleGraph.coe_edgeFinset,
    Set.ncard_coe_finset]

/-- A spanning subgraph `H1` of `H0.coe`, seen as a subgraph of `G` on the vertices of
`H0`. -/
def liftSub {V : Type*} {G : SimpleGraph V} (H0 : G.Subgraph) (H1 : SimpleGraph H0.verts)
    (h : H1 ≤ H0.coe) : G.Subgraph where
  verts := H0.verts
  Adj u v := ∃ (hu : u ∈ H0.verts) (hv : v ∈ H0.verts), H1.Adj ⟨u, hu⟩ ⟨v, hv⟩
  adj_sub := by
    rintro u v ⟨hu, hv, huv⟩
    exact H0.adj_sub (h huv)
  edge_vert := by
    rintro u v ⟨hu, hv, huv⟩
    exact hu
  symm := ⟨by
    rintro u v ⟨hu, hv, huv⟩
    exact ⟨hv, hu, huv.symm⟩⟩

theorem liftSub_coe {V : Type*} {G : SimpleGraph V} (H0 : G.Subgraph)
    (H1 : SimpleGraph H0.verts) (h : H1 ≤ H0.coe) : (liftSub H0 H1 h).coe = H1 := by
  ext ⟨u, hu⟩ ⟨v, hv⟩
  constructor
  · rintro ⟨_, _, huv⟩
    exact huv
  · intro huv
    exact ⟨hu, hv, huv⟩

/-- The graph whose edges are the pairs `a, nb a i` with `a ∈ A`. -/
def pickGraph {W : Type*} (G0 : SimpleGraph W) (A : Finset W) {K : ℕ} (nb : W → Fin K → W)
    (hnb : ∀ a ∈ A, ∀ i, G0.Adj a (nb a i)) : SimpleGraph W where
  Adj x y := (x ∈ A ∧ ∃ i, nb x i = y) ∨ (y ∈ A ∧ ∃ i, nb y i = x)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by
    rintro x (⟨hx, i, hi⟩ | ⟨hx, i, hi⟩)
    · have := hnb x hx i
      rw [hi] at this
      exact G0.loopless.irrefl x this
    · have := hnb x hx i
      rw [hi] at this
      exact G0.loopless.irrefl x this⟩

theorem pickGraph_le {W : Type*} (G0 : SimpleGraph W) (A : Finset W) {K : ℕ}
    (nb : W → Fin K → W) (hnb : ∀ a ∈ A, ∀ i, G0.Adj a (nb a i)) :
    pickGraph G0 A nb hnb ≤ G0 := by
  rintro x y (⟨hx, i, rfl⟩ | ⟨hy, i, rfl⟩)
  · exact hnb x hx i
  · exact (hnb y hy i).symm

/-- **Corollary 2** of the written proof, on the output of `extract` in a graph with no
4-cycle: Bob wins the `k`-colour game for every `k ≤ K` on the graph of the chosen edges. -/
theorem bob_wins_pickGraph {W : Type*} [Fintype W] [DecidableEq W] (G0 : SimpleGraph W)
    (hC : C4Free G0) (K : ℕ) (hK : 2 ≤ K) (A : Finset W) (cls : W → Option (Fin K))
    (nb : W → Fin K → W) (hA : ∀ a ∈ A, cls a = none)
    (hnb : ∀ a ∈ A, ∀ i, G0.Adj a (nb a i) ∧ cls (nb a i) = some i)
    (hcount : (2 ^ K + 1) * (univ.filter (fun w => cls w ≠ none)).card < A.card)
    (k : ℕ) (hk : k ≤ K) :
    ¬ AliceWinsGame (pickGraph G0 A nb (fun a ha i => (hnb a ha i).1)) k := by
  classical
  have hle := pickGraph_le G0 A nb (fun a ha i => (hnb a ha i).1)
  set H1 := pickGraph G0 A nb (fun a ha i => (hnb a ha i).1) with hH1
  have hadj : ∀ x y, H1.Adj x y ↔ (x ∈ A ∧ ∃ i, nb x i = y) ∨ (y ∈ A ∧ ∃ i, nb y i = x) :=
    fun x y => Iff.rfl
  let clsk : W → Option (Fin k) := fun w =>
    (cls w).bind (fun i => if h : i.val < k then some ⟨i.val, h⟩ else none)
  let nbk : W → Fin k → W := fun a i => nb a ⟨i.val, lt_of_lt_of_le i.isLt hk⟩
  -- facts on the restricted classes
  have h1 : ∀ w, clsk w ≠ none → cls w ≠ none := by
    intro w h h'
    simp [clsk, h'] at h
  have h2 : ∀ w (i : Fin k), clsk w = some i → ∃ j : Fin K, cls w = some j ∧ j.val = i.val := by
    intro w i h
    cases hc : cls w with
    | none => simp [clsk, hc] at h
    | some j =>
      refine ⟨j, rfl, ?_⟩
      simp only [clsk, hc, Option.bind_some] at h
      split_ifs at h with hj
      have := Option.some.inj h
      rw [← this]
  have h3 : ∀ w (j : Fin K) (hj : j.val < k), cls w = some j → clsk w = some ⟨j.val, hj⟩ := by
    intro w j hj hc
    simp [clsk, hc, hj]
  have hnotA : ∀ w, cls w ≠ none → w ∉ A := fun w hw hwA => hw (hA w hwA)
  have hne : ∀ w w' (i j : Fin K), cls w = some i → cls w' = some j → i ≠ j → w ≠ w' := by
    rintro w w' i j hi hj hij rfl
    rw [hi] at hj
    exact hij (Option.some.inj hj)
  refine bob_wins_of_structure H1 k A clsk nbk (univ.filter (fun w => cls w ≠ none)).card
    ?_ ?_ ?_ ?_ ?_ ?_
  · -- hA
    intro a ha
    simp [clsk, hA a ha]
  · -- hU
    intro w hw v hwv
    rcases (hadj w v).1 hwv with ⟨hwA, -⟩ | ⟨hvA, -⟩
    · exact absurd hwA (hnotA w (h1 w hw))
    · exact hvA
  · -- hnb
    intro a ha i
    refine ⟨(hadj _ _).2 (Or.inl ⟨ha, _, rfl⟩), ?_, ?_⟩
    · exact h3 _ ⟨i.val, lt_of_lt_of_le i.isLt hk⟩ i.isLt (hnb a ha _).2
    · intro w haw hw
      obtain ⟨j, hj, hji⟩ := h2 w i hw
      rcases (hadj a w).1 haw with ⟨-, j', rfl⟩ | ⟨hwA, -⟩
      · have hj' := (hnb a ha j').2
        rw [hj] at hj'
        have : j = j' := Option.some.inj hj'
        subst this
        have : j = ⟨i.val, lt_of_lt_of_le i.isLt hk⟩ := Fin.ext hji
        rw [this]
      · exact absurd hwA (hnotA w (by rw [hj]; simp))
  · -- hlin
    intro a _ a' _ haa' w w' _ _ haw ha'w haw' ha'w'
    by_contra hww'
    exact hC a w a' w' haa' hww' (hle haw) (hle ha'w).symm (hle ha'w') (hle haw').symm
  · -- hD
    intro w hw
    obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.1 (h1 w hw)
    obtain ⟨j, hij⟩ : ∃ j : Fin K, i ≠ j := by
      by_cases h0 : i.val = 0
      · exact ⟨⟨1, by omega⟩, fun h => by rw [h] at h0; simp at h0⟩
      · exact ⟨⟨0, by omega⟩, fun h => by rw [h] at h0; simp at h0⟩
    refine Finset.card_le_card_of_injOn (fun a => nb a j) ?_ ?_
    · intro a ha
      have haA : a ∈ A := (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).1
      refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
      rw [(hnb a haA j).2]
      simp
    · intro a ha a' ha' hEq
      have haA := (Finset.mem_filter.1 (Finset.mem_coe.1 ha))
      have ha'A := (Finset.mem_filter.1 (Finset.mem_coe.1 ha'))
      by_contra haa'
      have hEq' : nb a j = nb a' j := hEq
      have hwn : w ≠ nb a j := hne w (nb a j) i j hi (hnb a haA.1 j).2 hij
      have e1 : G0.Adj a w := hle haA.2
      have e2 : G0.Adj w a' := (hle ha'A.2).symm
      have e3 : G0.Adj a' (nb a j) := by
        rw [hEq']
        exact (hnb a' ha'A.1 j).1
      have e4 : G0.Adj (nb a j) a := (hnb a haA.1 j).1.symm
      exact hC a w a' (nb a j) haa' hwn e1 e2 e3 e4
  · -- hcount
    have hc : (univ.filter (fun w => clsk w ≠ none)).card ≤
        (univ.filter (fun w => cls w ≠ none)).card := by
      refine Finset.card_le_card (fun w hw => ?_)
      rw [Finset.mem_filter] at hw ⊢
      exact ⟨hw.1, h1 w hw.2⟩
    have hp : 2 ^ k ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hk
    have hm := Nat.mul_le_mul hp hc
    have he : (2 ^ K + 1) * (univ.filter (fun w => cls w ≠ none)).card =
        2 ^ K * (univ.filter (fun w => cls w ≠ none)).card +
          (univ.filter (fun w => cls w ≠ none)).card := by ring
    rw [he] at hcount
    have h0 : 0 ≤ 2 ^ K * (univ.filter (fun w => cls w ≠ none)).card := Nat.zero_le _
    linarith

/-- Theorem A on a fixed vertex set: a graph with no 4-cycle and average degree at least
`2 * (2 * (M + 1) * K * (K + 1))`, `M = 2 ^ K + 1`, `K ≥ 2`, has a spanning subgraph on
which Bob wins the `k`-colour game for every `k ≤ K`. -/
theorem exists_spanning_bob_wins {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (G0 : SimpleGraph W) [DecidableRel G0.Adj] (hC : C4Free G0) (K : ℕ) (hK : 2 ≤ K)
    (h : 2 * (2 * ((2 ^ K + 1) + 1) * K * (K + 1)) * Fintype.card W ≤ ∑ v, G0.degree v) :
    ∃ H1 : SimpleGraph W, H1 ≤ G0 ∧ ∀ k ≤ K, ¬ AliceWinsGame H1 k := by
  have ht : 0 < 2 * (2 * ((2 ^ K + 1) + 1) * K * (K + 1)) := by positivity
  obtain ⟨S, hSne, hS⟩ := exists_minDegree_subset G0 _ ht h
  obtain ⟨A, cls, nb, -, -, hA, hnb, hcnt⟩ :=
    extract G0 K (2 ^ K + 1) S hSne
      (fun v hv => Nat.le_of_mul_le_mul_left (hS v hv) (by norm_num))
  exact ⟨_, pickGraph_le G0 A nb (fun a ha i => (hnb a ha i).1),
    fun k hk => bob_wins_pickGraph G0 hC K hK A cls nb hA hnb hcnt k hk⟩

/-! ## The final statements -/

/-- The cited theorem (Kühn and Osthus 2004; Montgomery, Pokrovskiy and Sudakov 2021), as
a proposition: for every `t` there is `d` such that every finite graph with at least one
vertex and average degree at least `d` (`d * |V| ≤ 2 * |E|`) has a subgraph with at least
one vertex, no 4-cycle and average degree at least `t`. -/
def C4FreeSubgraphTheorem : Prop :=
  ∀ t : ℕ, ∃ d : ℕ, ∀ (V : Type) [Finite V] [Nonempty V] (G : SimpleGraph V),
    d * Nat.card V ≤ 2 * G.edgeSet.ncard →
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ C4Free H.coe ∧
      t * H.verts.ncard ≤ 2 * H.coe.edgeSet.ncard

/-- **Theorem A.** For every `K` there is `d` such that every finite graph with at least
one vertex and average degree at least `d` has a subgraph `H` on which Alice wins the
`k`-colour game for no `k ≤ K`; that is, the game chromatic number of `H` exceeds `K`. -/
theorem exists_subgraph_bob_wins (hC4 : C4FreeSubgraphTheorem) (K : ℕ) :
    ∃ d : ℕ, ∀ (V : Type) [Finite V] [Nonempty V] (G : SimpleGraph V),
      d * Nat.card V ≤ 2 * G.edgeSet.ncard →
      ∃ H : G.Subgraph, ∀ k ≤ K, ¬ AliceWinsGame H.coe k := by
  classical
  obtain ⟨d, hd⟩ :=
    hC4 (2 * (2 * ((2 ^ (K + 2) + 1) + 1) * (K + 2) * ((K + 2) + 1)))
  refine ⟨d, fun V _ _ G hG => ?_⟩
  obtain ⟨H0, hne, hC, havg⟩ := hd V G hG
  have : Fintype H0.verts := Fintype.ofFinite _
  have : Nonempty H0.verts := hne.to_subtype
  rw [two_mul_ncard_edgeSet H0.coe, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at havg
  obtain ⟨H1, hle, hH1⟩ := exists_spanning_bob_wins H0.coe hC (K + 2) (by omega) havg
  refine ⟨liftSub H0 H1 hle, fun k hk => ?_⟩
  rw [liftSub_coe]
  exact hH1 k (by omega)

/-- **Corollary B.** For every `K` there is `d` such that every class `C` of finite graphs
that is closed under subgraphs and in which every graph has game chromatic number at most
`K` (Alice wins the `k`-colour game for some `k ≤ K`) consists of graphs whose edges split
into `d` forests. -/
theorem bounded_arboricity (hC4 : C4FreeSubgraphTheorem) (K : ℕ) :
    ∃ d : ℕ, ∀ C : (V : Type) → SimpleGraph V → Prop,
      (∀ V G, C V G → Finite V) →
      (∀ V G, C V G → ∀ H : G.Subgraph, C H.verts H.coe) →
      (∀ V G, C V G → ∃ k ≤ K, AliceWinsGame G k) →
      ∀ V G, C V G → ArboricityLE G d := by
  classical
  obtain ⟨d, hd⟩ := exists_subgraph_bob_wins hC4 K
  refine ⟨d, fun C hfin hsub hwin V G hCG => ?_⟩
  have : Finite V := hfin V G hCG
  have : Fintype V := Fintype.ofFinite V
  apply arboricityLE_of_degenerate G d
  intro S hS
  by_contra hcon
  push Not at hcon
  let H : G.Subgraph := (⊤ : G.Subgraph).induce (S : Set V)
  have hCH : C H.verts H.coe := hsub V G hCG H
  have : Nonempty H.verts := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  have : Finite H.verts := hfin _ _ hCH
  have : Fintype H.verts := Fintype.ofFinite _
  have havg : d * Nat.card H.verts ≤ 2 * H.coe.edgeSet.ncard := by
    have hconst : d * Fintype.card H.verts = ∑ _w : H.verts, d := by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    rw [two_mul_ncard_edgeSet, Nat.card_eq_fintype_card, hconst]
    refine Finset.sum_le_sum (fun w _ => ?_)
    obtain ⟨v, hv⟩ := w
    refine (hcon v hv).trans (le_of_eq ?_)
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← Finset.card_image_of_injective _ Subtype.val_injective]
    congr 1
    ext u
    simp only [Finset.mem_filter, Finset.mem_image, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hu, hvu⟩
      exact ⟨⟨u, hu⟩, ⟨hv, hu, hvu⟩, rfl⟩
    · rintro ⟨⟨u', hu'⟩, ⟨-, -, hvu⟩, rfl⟩
      exact ⟨hu', hvu⟩
  obtain ⟨H', hH'⟩ := hd H.verts H.coe havg
  obtain ⟨k, hk, hwin'⟩ := hwin _ _ (hsub _ _ hCH H')
  exact hH' k hk hwin'

end GCG
