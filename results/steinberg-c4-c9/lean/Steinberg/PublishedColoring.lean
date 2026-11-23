import Steinberg.Encoding
import Steinberg.DataBindings
import LocalRup.PublishedTrace

namespace Steinberg
open Std.Sat

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def triangleUnits : List (CNF.Clause Nat) :=
  [[(0, true)], [(4, true)], [(20, true)]]

/-- The published DIMACS file gives the ordinary coloring clauses followed by
units assigning colors 0, 1, 2 to vertices 0, 1, 6 respectively. -/
theorem publishedClauses_eq :
    (List.range 82).flatMap vertexClauses ++ edgeList.flatMap edgeClauses ++
      triangleUnits = PublishedInput.clauses := by
  rw [edgeList_value]
  decide +kernel

private theorem triangle01 : graph.Adj 0 1 :=
  edge_adj (0, 1) (by rw [edgeList_value]; decide +kernel)

private theorem triangle06 : graph.Adj 0 6 :=
  edge_adj (0, 6) (by rw [edgeList_value]; decide +kernel)

private theorem triangle16 : graph.Adj 1 6 :=
  edge_adj (1, 6) (by rw [edgeList_value]; decide +kernel)

private def triangleColors (c : graph.Coloring (Fin 3)) (k : Fin 3) : Fin 3 :=
  if k = 0 then c 0 else if k = 1 then c 1 else c 6

private noncomputable def colorPermutation (c : graph.Coloring (Fin 3)) : Fin 3 ≃ Fin 3 :=
  Equiv.ofBijective (triangleColors c) (Finite.injective_iff_bijective.mp (by
    have h01 := c.valid triangle01
    have h06 := c.valid triangle06
    have h16 := c.valid triangle16
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [triangleColors, Ne.symm h01,
      Ne.symm h06, Ne.symm h16]))

/-- Every proper coloring can be relabeled to satisfy the three added units. -/
theorem publishedCNF_satisfied (c : graph.Coloring (Fin 3)) :
    ∃ a : Nat → Bool, PublishedInput.cnf.Sat a := by
  let e := colorPermutation c
  let fixed : graph.Coloring (Fin 3) :=
    SimpleGraph.Coloring.mk (fun v => e.symm (c v))
      (fun h hEq => c.valid h (e.symm.injective hEq))
  have h0 : fixed 0 = 0 := e.symm_apply_eq.mpr (by rfl)
  have h1 : fixed 1 = 1 := e.symm_apply_eq.mpr (by rfl)
  have h6 : fixed 6 = 2 := e.symm_apply_eq.mpr (by rfl)
  have ordinary := coloringCNF_sound graph edgeList
    (fun edge he => ⟨(edgeList_bounds edge he).1, (edgeList_bounds edge he).2, edge_adj edge he⟩)
    fixed
  refine ⟨colorAssignment fixed, ?_⟩
  rw [PublishedInput.cnf, ← publishedClauses_eq]
  simp only [CNF.Sat, CNF.eval, List.all_toArray, List.all_append, Bool.and_eq_true]
  simp only [CNF.Sat, CNF.eval, coloringCNF, List.all_toArray, List.all_append,
    Bool.and_eq_true] at ordinary
  refine ⟨ordinary, ?_⟩
  have v0 := colorAssignment_var fixed (v := 0) (by decide) 0
  have v1 := colorAssignment_var fixed (v := 1) (by decide) 1
  have v6 := colorAssignment_var fixed (v := 6) (by decide) 2
  change colorAssignment fixed 0 = _ at v0
  change colorAssignment fixed 4 = _ at v1
  change colorAssignment fixed 20 = _ at v6
  simp [triangleUnits, CNF.Clause.eval, v0, v1, v6, h0, h1, h6]

/-- The unsatisfiability of the published SAT instance excludes every proper
three-coloring of the graph. -/
theorem noColoring_of_publishedUnsat (unsat : PublishedInput.cnf.Unsat) :
    IsEmpty (graph.Coloring (Fin 3)) := by
  refine ⟨fun c => ?_⟩
  obtain ⟨a, ha⟩ := publishedCNF_satisfied c
  exact Bool.noConfusion ((unsat a).symm.trans ha)

theorem not_three_colorable_from_published : IsEmpty (graph.Coloring (Fin 3)) :=
  noColoring_of_publishedUnsat LocalRup.Published.cnf_unsat

/-- info: 'Steinberg.not_three_colorable_from_published' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_three_colorable_from_published

end Steinberg
