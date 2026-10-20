import Steinberg.Encoding
import Steinberg.DataBindings
import LocalRup.Certificate.SymmetryFreeFull

namespace Steinberg
open Std.Sat

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The symmetry-free CNF computed from the exact parsed graph. -/
def computedCNF : CNF Nat := coloringCNF 82 edgeList

/-- Kernel binding of the graph encoding to the checked certificate's exact input. -/
theorem computedCNF_eq : computedCNF = LocalRup.SymmetryFree.cnf := by
  have h : (List.range 82).flatMap vertexClauses ++ edgeList.flatMap edgeClauses =
      LocalRup.SymmetryFree.input := by
    rw [edgeList_value]
    decide +kernel
  exact congrArg (fun l : List (CNF.Clause Nat) => CNF.mk l.toArray) h

theorem coloring_satisfies (c : graph.Coloring (Fin 3)) :
    computedCNF.Sat (colorAssignment c) := by
  apply coloringCNF_sound graph edgeList _ c
  intro e he
  exact ⟨(edgeList_bounds e he).1, (edgeList_bounds e he).2, edge_adj e he⟩

/-- The exact included published graph has no proper three-coloring. -/
theorem not_three_colorable : IsEmpty (graph.Coloring (Fin 3)) := by
  refine ⟨fun c => ?_⟩
  have hs := coloring_satisfies c
  rw [computedCNF_eq] at hs
  have hu := LocalRup.SymmetryFree.LeanCertificate.cnf_unsat (colorAssignment c)
  have ht : LocalRup.SymmetryFree.cnf.eval (colorAssignment c) = true := hs
  rw [ht] at hu
  contradiction

/-- Audit the actual certificate API with fully qualified constants and types. -/
example : LocalRup.SymmetryFree.cnf =
    Std.Sat.CNF.mk LocalRup.SymmetryFree.input.toArray := rfl

example : LocalRup.Unsat LocalRup.SymmetryFree.input :=
  LocalRup.SymmetryFree.LeanCertificate.raw_unsat

example : IsEmpty (Steinberg.graph.Coloring (Fin 3)) := Steinberg.not_three_colorable

/-- Cheap raw-input shape checks supplement the stronger computed-CNF binding. -/
example : LocalRup.SymmetryFree.variables = 246 ∧
    LocalRup.SymmetryFree.input.length = 736 := by decide +kernel

example : LocalRup.SymmetryFree.input.all (fun c =>
    !c.isEmpty && c.all (fun l => l.1 < 246)) = true := by decide +kernel

example : (LocalRup.SymmetryFree.input.filter (fun c =>
    c.length == 3 && c.all (fun l => l.2))).length = 82 := by decide +kernel

example : (LocalRup.SymmetryFree.input.filter (fun c =>
    c.length == 2 && c.all (fun l => !l.2))).length = 654 := by decide +kernel

/-- info: 'Steinberg.computedCNF_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms computedCNF_eq

/-- info: 'Steinberg.not_three_colorable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_three_colorable

end Steinberg
