import Steinberg.Data
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Std.Sat.CNF

namespace Steinberg
open Std.Sat

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def vertexClauses (v : Nat) : List (CNF.Clause Nat) :=
  [[(3*v, true), (3*v+1, true), (3*v+2, true)],
   [(3*v, false), (3*v+1, false)],
   [(3*v, false), (3*v+2, false)],
   [(3*v+1, false), (3*v+2, false)]]

def edgeClauses (e : Nat × Nat) : List (CNF.Clause Nat) :=
  [[(3*e.1, false), (3*e.2, false)],
   [(3*e.1+1, false), (3*e.2+1, false)],
   [(3*e.1+2, false), (3*e.2+2, false)]]

/-- Symmetry-free proper three-coloring encoding, four clauses per vertex. -/
def coloringCNF (n : Nat) (edges : List (Nat × Nat)) : CNF Nat :=
  ⟨((List.range n).flatMap vertexClauses ++ edges.flatMap edgeClauses).toArray⟩

def colorAssignment {n : Nat} (c : Fin n → Fin 3) (i : Nat) : Bool :=
  if h : i / 3 < n then decide ((c ⟨i / 3, h⟩).val = i % 3) else false

theorem colorAssignment_var {n v : Nat} (c : Fin n → Fin 3) (hv : v < n) (k : Fin 3) :
    colorAssignment c (3*v+k.val) = decide ((c ⟨v, hv⟩).val = k.val) := by
  have hdiv : (3*v+k.val) / 3 = v := by omega
  have hmod : (3*v+k.val) % 3 = k.val := by omega
  simp [colorAssignment, hdiv, hmod, hv]

theorem vertex_satisfied {n v : Nat} (c : Fin n → Fin 3) (hv : v < n) :
    (vertexClauses v).all (CNF.Clause.eval (colorAssignment c)) = true := by
  have h0 := colorAssignment_var c hv (0 : Fin 3)
  have h1 := colorAssignment_var c hv (1 : Fin 3)
  have h2 := colorAssignment_var c hv (2 : Fin 3)
  change colorAssignment c (3*v) = decide ((c ⟨v, hv⟩).val = 0) at h0
  change colorAssignment c (3*v+1) = decide ((c ⟨v, hv⟩).val = 1) at h1
  change colorAssignment c (3*v+2) = decide ((c ⟨v, hv⟩).val = 2) at h2
  have hc : (c ⟨v, hv⟩).val = 0 ∨ (c ⟨v, hv⟩).val = 1 ∨ (c ⟨v, hv⟩).val = 2 := by
    have := (c ⟨v, hv⟩).isLt
    omega
  rcases hc with h | h | h <;> simp [vertexClauses, CNF.Clause.eval, h0, h1, h2, h]

theorem edge_satisfied {n a b : Nat} (c : Fin n → Fin 3) (ha : a < n) (hb : b < n)
    (hne : c ⟨a, ha⟩ ≠ c ⟨b, hb⟩) :
    (edgeClauses (a,b)).all (CNF.Clause.eval (colorAssignment c)) = true := by
  have a0 := colorAssignment_var c ha (0 : Fin 3)
  have a1 := colorAssignment_var c ha (1 : Fin 3)
  have a2 := colorAssignment_var c ha (2 : Fin 3)
  have b0 := colorAssignment_var c hb (0 : Fin 3)
  have b1 := colorAssignment_var c hb (1 : Fin 3)
  have b2 := colorAssignment_var c hb (2 : Fin 3)
  change colorAssignment c (3*a) = decide ((c ⟨a, ha⟩).val = 0) at a0
  change colorAssignment c (3*a+1) = decide ((c ⟨a, ha⟩).val = 1) at a1
  change colorAssignment c (3*a+2) = decide ((c ⟨a, ha⟩).val = 2) at a2
  change colorAssignment c (3*b) = decide ((c ⟨b, hb⟩).val = 0) at b0
  change colorAssignment c (3*b+1) = decide ((c ⟨b, hb⟩).val = 1) at b1
  change colorAssignment c (3*b+2) = decide ((c ⟨b, hb⟩).val = 2) at b2
  have ne : (c ⟨a, ha⟩).val ≠ (c ⟨b, hb⟩).val := fun eq => hne (Fin.ext eq)
  simp [edgeClauses, CNF.Clause.eval, a0, a1, a2, b0, b1, b2]
  omega

/-- Any coloring respects this encoding if every listed edge is an actual edge. -/
theorem coloringCNF_sound {n : Nat} (G : SimpleGraph (Fin n))
    (edges : List (Nat × Nat))
    (valid : ∀ e ∈ edges, ∃ (ha : e.1 < n) (hb : e.2 < n), G.Adj ⟨e.1, ha⟩ ⟨e.2, hb⟩)
    (c : G.Coloring (Fin 3)) :
    (coloringCNF n edges).Sat (colorAssignment c) := by
  simp only [CNF.Sat, CNF.eval, coloringCNF, List.all_toArray, List.all_append,
    Bool.and_eq_true, List.all_flatMap, List.all_eq_true]
  constructor
  · intro v hv
    exact List.all_eq_true.mp (vertex_satisfied c (List.mem_range.mp hv))
  · intro e he
    obtain ⟨ha, hb, hadj⟩ := valid e he
    exact List.all_eq_true.mp (edge_satisfied c ha hb (c.valid hadj))

end Steinberg
