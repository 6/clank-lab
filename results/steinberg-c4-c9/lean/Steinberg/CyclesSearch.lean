import Mathlib.Combinatorics.SimpleGraph.Paths

set_option autoImplicit false

namespace Steinberg.CycleSearch

/-- Bounded search for a simple path back to `root`. The visited list holds
all vertices already used, including the current vertex and the root.
Only the last edge is allowed to return to the root. -/
def clear (neighbors : Nat → List Nat) (root : Nat) :
    Nat → Nat → List Nat → Bool
  | 0, current, _ => !(neighbors current).contains root
  | remaining + 1, current, visited =>
      (neighbors current).all fun next =>
        if visited.contains next then true
        else clear neighbors root remaining next (next :: visited)

def rootClear (neighbors : Nat → List Nat) (root length : Nat) : Bool :=
  match length with
  | 0 => true
  | steps + 1 => clear neighbors root steps root [root]

end Steinberg.CycleSearch

namespace Steinberg.CycleSearch

/-- A path through the given future vertices followed by its closing edge.
This is an internal induction invariant, not the final cycle definition. -/
def Linked (neighbors : Nat → List Nat) (root : Nat) : Nat → List Nat → Prop
  | current, [] => root ∈ neighbors current
  | current, next :: rest => next ∈ neighbors current ∧ Linked neighbors root next rest

theorem clear_sound (neighbors : Nat → List Nat) (root : Nat)
    (future : List Nat) (current : Nat) (visited : List Nat)
    (hc : clear neighbors root future.length current visited = true)
    (hn : future.Nodup)
    (hd : ∀ x ∈ future, x ∉ visited)
    (hl : Linked neighbors root current future) : False := by
  induction future generalizing current visited with
  | nil =>
      exact (by simpa [clear] using hc : root ∉ neighbors current) hl
  | cons next rest ih =>
      have hnv : next ∉ visited := hd next (by simp)
      have hs := (List.all_eq_true.mp hc) next hl.1
      have hs' : clear neighbors root rest.length next (next :: visited) = true := by
        simpa [hnv] using hs
      apply ih next (next :: visited) hs' hn.tail _ hl.2
      intro x hx
      simp only [List.mem_cons, not_or]
      exact ⟨fun he => (List.nodup_cons.mp hn).1 (he ▸ hx), hd x (by simp [hx])⟩

variable {n : Nat} {G : SimpleGraph (Fin n)} {neighbors : Nat → List Nat}

/-- Completeness of the neighbor lists suffices. Extra candidate neighbors
are harmless for an exclusion proof. -/
theorem walk_linked
    (complete : ∀ a b : Fin n, G.Adj a b → b.val ∈ neighbors a.val)
    {a b : Fin n} (p : G.Walk a b) (hp : ¬p.Nil) :
    Linked neighbors b.val a.val (p.support.tail.dropLast.map Fin.val) := by
  induction p with
  | nil => exact False.elim (hp (by simp))
  | @cons a c b h p ih =>
      cases p with
      | nil => simpa [Linked] using complete a c h
      | @cons c d b h' q =>
          simp only [SimpleGraph.Walk.support_cons, List.tail_cons]
          rw [List.dropLast_cons_of_ne_nil q.support_ne_nil]
          constructor
          · exact complete a c h
          · simpa using ih (by simp)

/-- Every Mathlib cycle is tested from its existing start and orientation.
No minimum-root assumption, rotation, reversal, or absence of chords is used. -/
theorem isCycle_not_rootClear
    (complete : ∀ a b : Fin n, G.Adj a b → b.val ∈ neighbors a.val)
    {v : Fin n} (p : G.Walk v v) (hp : p.IsCycle) :
    rootClear neighbors v.val p.length ≠ true := by
  intro hc
  cases p with
  | nil => exact hp.ne_nil rfl
  | @cons v w v h q =>
      have hq : q.support.Nodup := by
        simpa using hp.support_nodup
      have hlast : q.support = q.support.dropLast ++ [v] := by
        simpa using (List.dropLast_append_getLast q.support_ne_nil).symm
      have hn : (q.support.dropLast.map Fin.val).Nodup :=
        (hq.sublist (List.dropLast_sublist _)).map Fin.val_injective
      have hd : ∀ x ∈ q.support.dropLast.map Fin.val, x ∉ [v.val] := by
        intro x hx hv
        have hxv : x = v.val := by simpa using hv
        obtain ⟨y, hy, he⟩ := List.mem_map.mp hx
        have hyv : y = v := Fin.ext (he.trans hxv)
        have hvnot : v ∉ q.support.dropLast := by
          rw [hlast, List.nodup_append] at hq
          exact fun hh => hq.2.2 v hh v (by simp) rfl
        exact hvnot (hyv ▸ hy)
      have hlen : (q.support.dropLast.map Fin.val).length = q.length := by
        simp [List.length_dropLast, q.length_support]
      apply clear_sound neighbors v.val (q.support.dropLast.map Fin.val) v.val [v.val]
      · simpa [rootClear, hlen] using hc
      · exact hn
      · exact hd
      · simpa using walk_linked complete (SimpleGraph.Walk.cons h q) (by simp)

end Steinberg.CycleSearch

namespace Steinberg.CycleSearch

/-- Lookup cache, checked against the shared graph in `Cycles`.
The graph itself is defined only in `Steinberg.Data`. -/
def neighborRows : List (List Nat) := [
  [1, 2, 3, 4, 5, 6],
  [0, 6, 18, 19, 20, 21],
  [0, 23, 32],
  [0, 24, 33],
  [0, 28, 34],
  [0, 29, 35],
  [0, 1, 60, 61],
  [8, 9, 10, 11, 12, 13, 14, 15, 16, 17],
  [7, 36, 40],
  [7, 37, 41],
  [7, 42, 44],
  [7, 43, 45],
  [7, 60, 62],
  [7, 61, 63],
  [7, 68, 72],
  [7, 69, 73],
  [7, 74, 76],
  [7, 75, 77],
  [1, 51, 64],
  [1, 52, 65],
  [1, 56, 66],
  [1, 57, 67],
  [23, 24, 25, 26],
  [2, 22, 32],
  [3, 22, 33],
  [22, 26, 38, 39],
  [22, 25, 42, 43],
  [28, 29, 30, 31],
  [4, 27, 34],
  [5, 27, 35],
  [27, 31, 36, 37],
  [27, 30, 46, 47],
  [2, 23, 33],
  [3, 24, 32],
  [4, 28, 35],
  [5, 29, 34],
  [8, 30, 40],
  [9, 30, 41],
  [25, 46, 48],
  [25, 47, 49],
  [8, 36, 41],
  [9, 37, 40],
  [10, 26, 44],
  [11, 26, 45],
  [10, 42, 45],
  [11, 43, 44],
  [31, 38, 48],
  [31, 39, 49],
  [38, 46, 49],
  [39, 47, 48],
  [51, 52, 53, 54],
  [18, 50, 64],
  [19, 50, 65],
  [50, 54, 70, 71],
  [50, 53, 74, 75],
  [56, 57, 58, 59],
  [20, 55, 66],
  [21, 55, 67],
  [55, 59, 68, 69],
  [55, 58, 78, 79],
  [6, 12, 62],
  [6, 13, 63],
  [12, 60, 63],
  [13, 61, 62],
  [18, 51, 65],
  [19, 52, 64],
  [20, 56, 67],
  [21, 57, 66],
  [14, 58, 72],
  [15, 58, 73],
  [53, 78, 80],
  [53, 79, 81],
  [14, 68, 73],
  [15, 69, 72],
  [16, 54, 76],
  [17, 54, 77],
  [16, 74, 77],
  [17, 75, 76],
  [59, 70, 80],
  [59, 71, 81],
  [70, 78, 81],
  [71, 79, 80]
]

def neighbors (v : Nat) : List Nat := neighborRows.getD v []

end Steinberg.CycleSearch
