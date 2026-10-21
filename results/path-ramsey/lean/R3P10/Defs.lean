import Mathlib.Data.Sym.Sym2
import Mathlib.Order.PiLex
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Dedup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Group.End
import Mathlib.Data.List.GetD
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sym

/-!
# Definitions: colourings, paths, CNF semantics, and the encoder

Everything the statements and the hypotheses mention is defined here.
The encoder `encode n k` is a closed-form twin of `checks/encode.py`
(`encode.py n m --fix k`); `Checks.lean` compares its DIMACS text `dimacs`
byte for byte with each `data/cnf/k{n}p{m}.cnf`.
-/

namespace R3P10

/-! ## Colourings and monochromatic paths -/

/-- A 3-colouring of the edges of `K_n` (the diagonal of `Sym2` is never used). -/
abbrev Col (n : ℕ) := Sym2 (Fin n) → Fin 3

/-- `X` has a monochromatic path on `m` vertices: distinct vertices
`p 0, ..., p (m-1)` whose consecutive pairs all have one colour `c`. -/
def HasMonoPath (n m : ℕ) (X : Col n) : Prop :=
  ∃ (c : Fin 3) (p : Fin m → Fin n), Function.Injective p ∧
    ∀ (i : ℕ) (h : i + 1 < m), X s(p ⟨i, by omega⟩, p ⟨i + 1, h⟩) = c

/-! ## CNF semantics (DIMACS: a literal is a nonzero integer) -/

abbrev Clause := List Int
abbrev CNF := List Clause

/-- Literal `l` is true under the assignment `A` of variables `1, 2, ...`. -/
def LitTrue (A : ℕ → Prop) (l : Int) : Prop := if 0 < l then A l.natAbs else ¬ A l.natAbs

def ClauseTrue (A : ℕ → Prop) (C : Clause) : Prop := ∃ l ∈ C, LitTrue A l

def CNFTrue (A : ℕ → Prop) (F : CNF) : Prop := ∀ C ∈ F, ClauseTrue A C

/-! ## Edges and variables (the convention of `encode.py` and `check_paths.py`) -/

/-- The edges `(i, j)`, `i < j < n`, of `K_n` in row-wise order. -/
def edges (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun i => (List.range n).filterMap fun j => if i < j then some (i, j) else none

/-- The index of edge `{u, v}` in `edges n`. -/
def eidx (n u v : ℕ) : ℕ := (edges n).idxOf (min u v, max u v)

/-- The variable "edge number `k` has colour `c`": `3k + c + 1`. -/
def var (k c : ℕ) : ℕ := 3 * k + c + 1

/-- `C` is a path clause for `P_m` in `K_n`: for some colour `c` and some
`m` distinct vertices `p 0, ..., p (m-1)`, the literals of `C` are exactly
the negated variables "edge `{p i, p (i+1)}` has colour `c`". This is the
clause class `checks/check_paths.py` accepts. -/
def IsPathClause (n m : ℕ) (C : Clause) : Prop :=
  ∃ (c : Fin 3) (p : Fin m → Fin n), Function.Injective p ∧
    ∀ l : Int, l ∈ C ↔ ∃ (i : ℕ) (h : i + 1 < m),
      l = -((var (eidx n (p ⟨i, by omega⟩) (p ⟨i + 1, h⟩)) c : ℕ) : Int)

/-- `F` together with every path clause for `P_m` in `K_n` is unsatisfiable. -/
def UnsatWithPaths (n m : ℕ) (F : CNF) : Prop :=
  ∀ A : ℕ → Prop, CNFTrue A F → (∀ C, IsPathClause n m C → ClauseTrue A C) → False

/-! ## Generators of the symmetry reduction -/

/-- A symmetry: a vertex permutation and a colour permutation. It sends `X`
to `act g X`, with `(act g X) {π a, π b} = σ (X {a, b})`. -/
structure Gen (n : ℕ) where
  perm : Equiv.Perm (Fin n)
  col : Equiv.Perm (Fin 3)

/-- The vertex map `t ↦ k-1-t` on `0..k-1`, the identity elsewhere. -/
def revFun (n k : ℕ) (t : Fin n) : Fin n :=
  if h : t.val < k ∧ k ≤ n then ⟨k - 1 - t.val, by omega⟩ else t

theorem revFun_invol (n k : ℕ) : Function.Involutive (revFun n k) := by
  intro t
  unfold revFun
  by_cases h : t.val < k ∧ k ≤ n
  · rw [dif_pos h, dif_pos (by simp; omega)]; ext; simp; omega
  · rw [dif_neg h, dif_neg h]

/-- The generators `encode.py` encodes, in its order. With `k = 0`: every
vertex transposition, then the colour transpositions (0 1) and (1 2).
With `k > 0`: the transpositions of `{k, ..., n-1}`, the reversal of the
fixed path `0..k-1`, and the colour transposition (1 2). -/
def gens (n k : ℕ) : List (Gen n) :=
  let transps : List (Gen n) := (List.finRange n).flatMap fun i => (List.finRange n).filterMap
    fun j => if k ≤ i.val ∧ i < j then some ⟨Equiv.swap i j, 1⟩ else none
  if k = 0 then transps ++ [⟨1, Equiv.swap 0 1⟩, ⟨1, Equiv.swap 1 2⟩]
  else transps ++ [⟨Function.Involutive.toPerm _ (revFun_invol n k), 1⟩, ⟨1, Equiv.swap 1 2⟩]

/-! ## The encoder -/

variable {n : ℕ}

/-- Apply a vertex permutation to a natural number below `n`. -/
def permN (π : Equiv.Perm (Fin n)) (a : ℕ) : ℕ := if h : a < n then (π ⟨a, h⟩).val else a

/-- Position `src g k`: `(act g X)` at edge `k` is `g.col` of `X` at edge `src g k`. -/
def src (g : Gen n) (k : ℕ) : ℕ :=
  let e := (edges n).getD k (0, 0)
  eidx n (permN g.perm.symm e.1) (permN g.perm.symm e.2)

/-- Position `k` is skipped when `(act g X)_k = X_k` identically. -/
def skip (g : Gen n) (k : ℕ) : Bool := src g k == k && (List.finRange 3).all fun c => g.col c == c

/-- The number of non-skipped positions before `k`. -/
def ns (g : Gen n) (k : ℕ) : ℕ := ((List.range k).filter fun k' => !skip g k').length

/-- `sorted(set(l))` -/
def sd (l : List Int) : List Int := l.dedup.mergeSort (fun a b => decide (a ≤ b))

def lit (k c : ℕ) : Int := (var k c : ℕ)

/-- The clauses of position `k` in the block of generator `g` starting at variable `top`. -/
def posClauses (g : Gen n) (top k : ℕ) : CNF :=
  let s := src g k
  let A : Fin 3 → Int := fun v => lit k v
  let B : Fin 3 → Int := fun v => lit s (g.col.symm v)
  let j := ns g k
  let pre : List Int := if j = 0 then [] else [-((top + j : ℕ) : Int)]
  let ne : Int := ((top + j + 1 : ℕ) : Int)
  [sd (pre ++ [-A 1, -B 0]), sd (pre ++ [-A 2, -B 0]), sd (pre ++ [-A 2, -B 1]),
   sd (pre ++ [-A 0, -B 0, ne]), sd (pre ++ [-A 1, -B 1, ne]), sd (pre ++ [-A 2, -B 2, ne])] ++
  (if j = 0 then [] else [[-ne, ((top + j : ℕ) : Int)]]) ++
  [sd [-ne, -A 0, B 0], sd [-ne, -A 1, B 1], sd [-ne, -A 2, B 2]]

/-- The lex-leader block `X ≤lex act g X` with auxiliaries `top+1 .. top + ns g N`. -/
def blockClauses (g : Gen n) (top : ℕ) : CNF :=
  (List.range (edges n).length).flatMap fun k => if skip g k then [] else posClauses g top k

def lexBlocks : List (Gen n) → ℕ → CNF
  | [], _ => []
  | g :: gs, top => blockClauses g top ++ lexBlocks gs (top + ns g (edges n).length)

def topAfter : List (Gen n) → ℕ → ℕ
  | [], top => top
  | g :: gs, top => topAfter gs (top + ns g (edges n).length)

def exactlyOne (n : ℕ) : CNF :=
  (List.range (edges n).length).flatMap fun k =>
    [[lit k 0, lit k 1, lit k 2], [-lit k 0, -lit k 1], [-lit k 0, -lit k 2], [-lit k 1, -lit k 2]]

/-- Unit clauses: the path `0, 1, ..., k-1` has colour 0. -/
def fixUnits (n k : ℕ) : CNF := (List.range (k - 1)).map fun t => [lit (eidx n t (t + 1)) 0]

/-- The formula of `encode.py n m --fix k` (it does not depend on `m`). -/
def encode (n k : ℕ) : CNF :=
  exactlyOne n ++ fixUnits n k ++ lexBlocks (gens n k) (3 * (edges n).length)

def numVars (n k : ℕ) : ℕ := topAfter (gens n k) (3 * (edges n).length)

/-- DIMACS text, byte for byte as `encode.py n m --fix k` writes it. -/
def dimacs (n m k : ℕ) : String :=
  let F := encode n k
  let hdr := s!"c encode.py n={n} m={m} fix={k} lex=1 gens={(gens n k).length}\n" ++
    "c x(e,c)=3e+c+1, edges row-wise; path clauses added lazily\n" ++
    s!"p cnf {numVars n k} {F.length}\n"
  F.foldl (fun acc C => acc ++ " ".intercalate (C.map toString) ++ " 0\n") hdr

end R3P10
