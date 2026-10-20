import Steinberg.Data
import Mathlib.Tactic.FinCases
import Steinberg.CyclesRootsA
import Steinberg.CyclesRootsB

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Steinberg.CycleSearch

/-- Exhaustion is composed from bounded per-root kernel reductions. -/
theorem all_roots_clear (v : Fin 82) :
    rootClear neighbors v.val 4 = true ∧ rootClear neighbors v.val 9 = true := by
  fin_cases v
  · exact root_0_clear
  · exact root_1_clear
  · exact root_2_clear
  · exact root_3_clear
  · exact root_4_clear
  · exact root_5_clear
  · exact root_6_clear
  · exact root_7_clear
  · exact root_8_clear
  · exact root_9_clear
  · exact root_10_clear
  · exact root_11_clear
  · exact root_12_clear
  · exact root_13_clear
  · exact root_14_clear
  · exact root_15_clear
  · exact root_16_clear
  · exact root_17_clear
  · exact root_18_clear
  · exact root_19_clear
  · exact root_20_clear
  · exact root_21_clear
  · exact root_22_clear
  · exact root_23_clear
  · exact root_24_clear
  · exact root_25_clear
  · exact root_26_clear
  · exact root_27_clear
  · exact root_28_clear
  · exact root_29_clear
  · exact root_30_clear
  · exact root_31_clear
  · exact root_32_clear
  · exact root_33_clear
  · exact root_34_clear
  · exact root_35_clear
  · exact root_36_clear
  · exact root_37_clear
  · exact root_38_clear
  · exact root_39_clear
  · exact root_40_clear
  · exact root_41_clear
  · exact root_42_clear
  · exact root_43_clear
  · exact root_44_clear
  · exact root_45_clear
  · exact root_46_clear
  · exact root_47_clear
  · exact root_48_clear
  · exact root_49_clear
  · exact root_50_clear
  · exact root_51_clear
  · exact root_52_clear
  · exact root_53_clear
  · exact root_54_clear
  · exact root_55_clear
  · exact root_56_clear
  · exact root_57_clear
  · exact root_58_clear
  · exact root_59_clear
  · exact root_60_clear
  · exact root_61_clear
  · exact root_62_clear
  · exact root_63_clear
  · exact root_64_clear
  · exact root_65_clear
  · exact root_66_clear
  · exact root_67_clear
  · exact root_68_clear
  · exact root_69_clear
  · exact root_70_clear
  · exact root_71_clear
  · exact root_72_clear
  · exact root_73_clear
  · exact root_74_clear
  · exact root_75_clear
  · exact root_76_clear
  · exact root_77_clear
  · exact root_78_clear
  · exact root_79_clear
  · exact root_80_clear
  · exact root_81_clear

/-- The generic theorem is ready for the shared graph's exact adjacency API. -/
theorem no_forbidden_cycles_of_complete (G : SimpleGraph (Fin 82))
    (complete : ∀ a b : Fin 82, G.Adj a b → b.val ∈ neighbors a.val) :
    ∀ v (p : G.Walk v v), p.IsCycle → p.length ≠ 4 ∧ p.length ≠ 9 := by
  intro v p hp
  have h := isCycle_not_rootClear complete p hp
  constructor
  · intro he
    exact h (by simpa [he] using (all_roots_clear v).1)
  · intro he
    exact h (by simpa [he] using (all_roots_clear v).2)

/-- The same neighbor search is run on the graph with the inserted undirected
edge 0--12. No rotation check participates in this test. -/
def addedNeighbors (v : Nat) : List Nat :=
  if v == 0 then 12 :: neighbors v
  else if v == 12 then 0 :: neighbors v
  else neighbors v

/-- Direct negative control: the C4 exclusion check is mathematically false. -/
theorem added_edge_c4_check_false : rootClear addedNeighbors 0 4 = false := by
  decide +kernel

/-- These are the four edges found by the corrupted graph's search. -/
theorem added_edge_c4_witness :
    Linked addedNeighbors 0 0 [6, 60, 12] := by
  simp only [Linked]
  decide +kernel

/-- info: 'Steinberg.CycleSearch.no_forbidden_cycles_of_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms no_forbidden_cycles_of_complete

/-- info: 'Steinberg.CycleSearch.added_edge_c4_check_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms added_edge_c4_check_false

end Steinberg.CycleSearch

namespace Steinberg.CycleSearch

/-- Each published edge has both endpoints in the cached neighbor lists. -/
theorem edgeList_covered :
    edgeList.all (fun e => (neighbors e.1).contains e.2 &&
      (neighbors e.2).contains e.1) = true := by
  decide +kernel

theorem neighbors_complete (a b : Fin 82) (h : graph.Adj a b) :
    b.val ∈ neighbors a.val := by
  have hc := List.all_eq_true.mp edgeList_covered
  rcases (graph_adj_iff a b).mp h with ⟨_, he | he⟩
  · have he' := hc (a.val, b.val) he
    simp only [Bool.and_eq_true, List.contains_iff_mem] at he'
    exact he'.1
  · have he' := hc (b.val, a.val) he
    simp only [Bool.and_eq_true, List.contains_iff_mem] at he'
    exact he'.2

end Steinberg.CycleSearch

namespace Steinberg

/-- The exact graph parsed from the published edge file has no simple cycle
of length four or nine, using Mathlib's actual walk and cycle notions. -/
theorem no_forbidden_cycles :
    ∀ v (p : graph.Walk v v), p.IsCycle → p.length ≠ 4 ∧ p.length ≠ 9 :=
  CycleSearch.no_forbidden_cycles_of_complete graph CycleSearch.neighbors_complete

/-- The exact graph with only the undirected edge 0--12 added. -/
def cycleControlGraph : SimpleGraph (Fin 82) where
  Adj a b := graph.Adj a b ∨ (a = 0 ∧ b = 12) ∨ (a = 12 ∧ b = 0)
  symm := ⟨by
    intro a b h
    rcases h with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
    · exact Or.inr (Or.inl ⟨h.2, h.1⟩)⟩
  loopless := ⟨by
    intro a h
    rcases h with h | h | h
    · exact graph.irrefl h
    · have : (0 : Fin 82) = 12 := h.1.symm.trans h.2
      exact (by decide : (0 : Fin 82) ≠ 12) this
    · have : (12 : Fin 82) = 0 := h.1.symm.trans h.2
      exact (by decide : (12 : Fin 82) ≠ 0) this⟩

theorem cycle_control_base_edges :
    graph.Adj 0 6 ∧ graph.Adj 6 60 ∧ graph.Adj 60 12 := by
  decide +kernel

/-- Explicit Mathlib walk witnessing the corrupted graph's four-cycle. -/
def cycleControlWalk : cycleControlGraph.Walk 0 0 :=
  .cons (Or.inl cycle_control_base_edges.1)
    (.cons (Or.inl cycle_control_base_edges.2.1)
      (.cons (Or.inl cycle_control_base_edges.2.2)
        (.cons (Or.inr (Or.inr ⟨rfl, rfl⟩)) .nil)))

theorem cycleControlWalk_isCycle : cycleControlWalk.IsCycle := by
  refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
  · decide +kernel
  · intro h
    cases h
  · decide +kernel

theorem cycleControlWalk_length : cycleControlWalk.length = 4 := rfl

/-- The direct DFS negative control corresponds to a real Mathlib cycle
in the graph with precisely the required edge added. -/
theorem cycle_control :
    CycleSearch.rootClear CycleSearch.addedNeighbors 0 4 = false ∧
    cycleControlWalk.IsCycle ∧ cycleControlWalk.length = 4 :=
  ⟨CycleSearch.added_edge_c4_check_false, cycleControlWalk_isCycle,
    cycleControlWalk_length⟩

/-- info: 'Steinberg.no_forbidden_cycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms no_forbidden_cycles

end Steinberg
