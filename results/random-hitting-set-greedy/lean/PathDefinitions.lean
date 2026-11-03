import Endpoint

/-! Isolated paths of three triples and the bad-middle count. No probability or
Greedy hypothesis is hidden in the definitions. -/
namespace ADG
open Finset

abbrev PathTuple (m : ℕ) := Fin 7 ↪ Fin m

def pathRows {m : ℕ} (t : PathTuple m) : Finset (Fin m) := univ.image t

def pathLeft {m : ℕ} (t : PathTuple m) : Finset (Fin m) := {t 0,t 1,t 2}
def pathMiddle {m : ℕ} (t : PathTuple m) : Finset (Fin m) := {t 2,t 3,t 4}
def pathRight {m : ℕ} (t : PathTuple m) : Finset (Fin m) := {t 4,t 5,t 6}

def pathForbidden {m : ℕ} (t : PathTuple m) : Finset (Finset (Fin m)) :=
  univ.filter (fun s => 3 ≤ s.card ∧ ¬ Disjoint s (pathRows t))

def pathOccurs {m n : ℕ} (A : Matrix m n) (t : PathTuple m) : Prop :=
  exactlyOnceMiddleFirst (pathForbidden t) (pathLeft t) (pathMiddle t) (pathRight t) A

def pathOccursAt {m n : ℕ} (A : Matrix m n) (t : PathTuple m)
    (left middle right : Fin n) : Prop :=
  middle < left ∧ middle < right ∧ left ≠ right ∧
  A left = pathLeft t ∧ A middle = pathMiddle t ∧ A right = pathRight t ∧
  ∀ j, j ≠ left → j ≠ middle → j ≠ right → A j ∉ pathForbidden t

noncomputable def badMiddles {m n : ℕ} (A : Matrix m n) : Finset (Fin n) := by
  classical
  exact univ.filter (fun middle => ∃ t : PathTuple m, ∃ left right,
    pathOccursAt A t left middle right)

noncomputable def B {m n : ℕ} (A : Matrix m n) : ℕ := (badMiddles A).card

noncomputable def orderedPathCount {m n : ℕ} (A : Matrix m n) : ℕ := by
  classical
  exact (univ.filter (fun t : PathTuple m => pathOccurs A t)).card

end ADG
