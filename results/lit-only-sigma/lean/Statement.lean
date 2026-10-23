import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Relation

/-!
Definitions of the games and the counterexample statement.
Source: Goldwasser–Wang–Wu, EJC 18 (2011), P214, pp. 1–5;
see FAITHFULNESS.md for the source-to-statement correspondence.
-/

namespace LitOnlySigma

abbrev Graph (n : ℕ) := Fin n → Fin n → Bool
abbrev Configuration (n : ℕ) := Fin n → Bool

def Undirected {n : ℕ} (G : Graph n) : Prop := ∀ u v, G u v = G v u

def Connected {n : ℕ} (G : Graph n) : Prop :=
  ∀ u v, Relation.ReflTransGen (fun a b => G a b = true) u v

def lightNumber {n : ℕ} (x : Configuration n) : ℕ :=
  (Finset.univ.filter fun v => x v = true).card

/-- Toggle exactly the neighbors, including the played vertex iff it has a loop. -/
def regularMove {n : ℕ} (G : Graph n) (x : Configuration n) (v : Fin n) :
    Configuration n := fun w => if G v w then !x w else x w

/-- The source's lit-only move: a dark play is the identity. -/
def litOnlyMove {n : ℕ} (G : Graph n) (x : Configuration n) (v : Fin n) :
    Configuration n := if x v then regularMove G x v else x

/-- An arbitrary finite sequence, including the empty sequence; no length bound. -/
def Reachable {n : ℕ} (move : Configuration n → Fin n → Configuration n)
    (x y : Configuration n) : Prop :=
  Relation.ReflTransGen (fun a b => ∃ v, b = move a v) x y

/-- The least attainable number of lights. The attainable set contains the start. -/
noncomputable def minimumLight {n : ℕ}
    (move : Configuration n → Fin n → Configuration n) (x : Configuration n) : ℕ :=
  sInf {k | ∃ y, Reachable move x y ∧ lightNumber y = k}

noncomputable def regularMinimum {n : ℕ} (G : Graph n) (x : Configuration n) : ℕ :=
  minimumLight (regularMove G) x

noncomputable def litOnlyMinimum {n : ℕ} (G : Graph n) (x : Configuration n) : ℕ :=
  minimumLight (litOnlyMove G) x

/-- The maximum of SAME-START differences, not the difference of two maxima. -/
noncomputable def discrepancy {n : ℕ} (G : Graph n) : ℕ :=
  Finset.univ.sup fun x => litOnlyMinimum G x - regularMinimum G x

/-- Surjectivity makes every part nonempty; the adjacency equivalence forbids loops. -/
def CompleteMultipartite {n : ℕ} (G : Graph n) (m : ℕ) : Prop :=
  ∃ part : Fin n → Fin m, Function.Surjective part ∧
    ∀ u v, G u v = true ↔ part u ≠ part v

/-- Conjecture 5 for one graph. `n < 2 * discrepancy G` is the strict n/2 threshold. -/
def Conjecture5 {n : ℕ} (G : Graph n) : Prop :=
  Undirected G → Connected G → n < 2 * discrepancy G →
    ∃ m : ℕ, 0 < m ∧ m % 4 = 3 ∧ CompleteMultipartite G m

/-- Bit j of row i says whether vertex j is a neighbor of vertex i. -/
def rows : Fin 7 → ℕ := ![92, 120, 113, 99, 71, 78, 63]

def graph : Graph 7 := fun u v => (rows u).testBit v.val

def decode (code : ℕ) : Configuration 7 := fun v => code.testBit v.val

def start : Configuration 7 := decode 27

/-- Counterexample statement: the precise conjecture fails for this specific graph. -/
def CounterexampleStatement : Prop :=
  Undirected graph ∧ Connected graph ∧
  regularMinimum graph start = 0 ∧ litOnlyMinimum graph start = 4 ∧
  (∀ m, ¬ CompleteMultipartite graph m) ∧ ¬ Conjecture5 graph

end LitOnlySigma
