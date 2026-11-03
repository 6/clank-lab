import CD13.Endpoint
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.WellFoundedSet
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! Legal finite constructor model. -/
noncomputable section
namespace CD13
open scoped Classical
universe u
variable {V : Type u} (E : V → V → Prop)

inductive Term : V → Type u
  | initial (i : V) : Term i
  | node (i : V) (children : (j : {j // E i j}) → Term j.val) : Term i

namespace Term
variable {E}

instance (i : V) : Nonempty (Term E i) := ⟨initial i⟩

def unfold {i : V} : Term E i → Option ((j : {j // E i j}) → Term E j.val)
  | initial _ => none
  | node _ c => some c

def fold {i : V} : Option ((j : {j // E i j}) → Term E j.val) → Term E i
  | none => initial i
  | some c => node i c

-- First supporting lemma: endpoint has already been written in Endpoint.lean.
theorem fold_unfold {i : V} (t : Term E i) : fold (unfold t) = t := by
  cases t <;> rfl

private theorem finite_of_children (i : V)
    [Finite {j // E i j}] (h : ∀ j, E i j → Finite (Term E j)) : Finite (Term E i) := by
  haveI : ∀ j : {j // E i j}, Finite (Term E j.val) := fun j => h j.val j.property
  exact Finite.of_injective unfold (Function.LeftInverse.injective fold_unfold)

/-- DAG accessibility is the only finiteness input; no bound on degrees. -/
theorem finite_of_acc [Finite V] (i : V) (h : Acc (fun j i => E i j) i) :
    Finite (Term E i) := by
  induction h with
  | intro i h ih => exact finite_of_children i (fun j hj => ih j hj)

theorem finite [Finite V] (hE : Acyclic E) (i : V) : Finite (Term E i) := by
  let R : V → V → Prop := fun j i => Relation.TransGen E i j
  haveI : IsStrictOrder V R :=
    { irrefl := hE
      trans := fun _ _ _ hab hbc => hbc.trans hab }
  have hR : WellFounded R := Set.wellFoundedOn_univ.mp (Set.finite_univ.wellFoundedOn)
  apply finite_of_acc
  exact (hR.mono (fun _ _ h => Relation.TransGen.single h)).apply i

/-- Natural-number term size: variables have size zero, each constructor one
plus the total sizes of its children. -/
def size [Fintype V] {i : V} : Term E i → Nat
  | initial _ => 0
  | node _ c => 1 + ∑ j, size (c j)

@[simp] theorem size_initial [Fintype V] (i : V) : size (initial i : Term E i) = 0 := rfl
@[simp] theorem size_node [Fintype V] (i : V)
    (c : (j : {j // E i j}) → Term E j.val) :
    size (node i c) = 1 + ∑ j, size (c j) := rfl

theorem size_node_pos [Fintype V] (i : V)
    (c : (j : {j // E i j}) → Term E j.val) : 0 < size (node i c) := by
  simp only [size_node]
  omega

end Term

variable {E}

def constructorSystem [Finite V] (hE : Acyclic E) : LocalSystem E where
  S := Term E
  finite := Term.finite hE
  nonempty := fun _ => inferInstance
  localFn := Term.node

abbrev TermState (E : V → V → Prop) := ∀ i, Term E i

def initialState : TermState E := Term.initial

def step (i : V) (s : TermState E) : TermState E :=
  Function.update s i (Term.node i (fun j => s j.val))

def run (w : List V) (s : TermState E) : TermState E :=
  w.foldl (fun s i => step i s) s

def eventTerms : List V → TermState E → List (Sigma (Term E))
  | [], _ => []
  | i :: w, s => ⟨i, Term.node i (fun j => s j.val)⟩ :: eventTerms w (step i s)

@[simp] theorem step_same (i : V) (s : TermState E) :
    step i s i = Term.node i (fun j => s j.val) := by simp [step]

@[simp] theorem step_other (i j : V) (s : TermState E) (h : j ≠ i) :
    step i s j = s j := by simp [step, h]

@[simp] theorem run_nil (s : TermState E) : run [] s = s := rfl
@[simp] theorem run_cons (i : V) (w : List V) (s : TermState E) :
    run (i :: w) s = run w (step i s) := rfl

theorem run_append (p q : List V) (s : TermState E) :
    run (p ++ q) s = run q (run p s) := List.foldl_append

@[simp] theorem eventTerms_nil (s : TermState E) : eventTerms [] s = [] := rfl
@[simp] theorem eventTerms_cons (i : V) (w : List V) (s : TermState E) :
    eventTerms (i :: w) s =
    ⟨i, Term.node i (fun j => s j.val)⟩ :: eventTerms w (step i s) := rfl

end CD13
