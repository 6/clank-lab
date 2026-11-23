import LRATCatcher.Reflect

open Std.Sat Lean Elab Command

namespace RupPieces

/-- Run the stock kernel elaborator on one empty-clause addition. Its hints
    visit the negated goal units, then the supplied clauses, in order. -/
elab "refute_hints " n:ident ppSpace f:ident ppSpace count:num : command => do
  let k := count.getNat
  let hints := (List.range k).map (· + 1)
  LRATCatcher.emitKernelTheorem n f #[.addEmpty (k + 1) hints.toArray]

theorem negUnit {a : Nat → Bool} {c : CNF.Clause Nat} {i : Nat} {p : Bool}
    (h : c.eval a = false) (m : (i,p) ∈ c) : CNF.Clause.eval a [(i,!p)] = true := by
  have hh : (a i == p) ≠ true := (List.any_eq_false.mp h) (i,p) m
  cases ha : a i <;> cases p <;> simp_all

theorem atClause (f : CNF Nat) {a : Nat → Bool} (h : f.eval a = true)
    (i : Nat) (b : i < f.clauses.size) : CNF.Clause.eval a f.clauses[i] = true :=
  (Array.all_eq_true_iff_forall_mem.mp h) _ (Array.getElem_mem b)

theorem clash (f : CNF Nat) (u : f.Unsat) (a : Nat → Bool)
    (h : f.eval a = true) : False := Bool.noConfusion ((u a).symm.trans h)

end RupPieces
