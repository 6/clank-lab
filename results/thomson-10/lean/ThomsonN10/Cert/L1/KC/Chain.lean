/- Adapted from proof/lean/ClaudeL1/KC/Chain.lean, aravindkarthigeyan/thomson-n9-lean, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
/-
ThomsonN10.Cert.L1.KC.Chain : SOS chunks on a whitelisted multiplier, chained through running totals.

A chunk is `SOSChunk.ofCode G w code cols prev next = ⟨w, 21, G code, cols, prev, next⟩`: its
multiplier is *not* free data but `G code` for a fixed multiplier table `G` (instantiated with
`ThomsonN10.Cert.L1.Data.Mult.gtree`, whose entries are proved equal to `10^4 * domainWeight` in the
Mathlib bridge).  `chunk_step` turns a passed chunk check into
`next = prev + Σ_{c ∈ cols} G(code) * c^2`, and `sumVal_append` lets the generated glue
telescope the chain.

Core Lean only (upstream L1 implementation).
-/
import ThomsonN10.Cert.L1.KC.Check

namespace ThomsonN10.Cert.L1.KC

/-- data shorthands used by the generated modules -/
abbrev L (c : Int) (a b d : Nat) : PTree := .leaf ⟨c, a, b, d⟩
abbrev N (l r : PTree) : PTree := .node l r

/-- the zero running total -/
def zeroTree : PTree := .leaf ⟨0, 0, 0, 0⟩

/-- a chunk whose multiplier is the table entry `G code` -/
def SOSChunk.ofCode (G : Nat → PTree) (w code : Nat) (cols : List PTree) (prev next : PTree) :
    SOSChunk :=
  { w := w, D := 21, g := G code, cols := cols, prev := prev, next := next }

/-- the SOS terms `(code, column)` of one chunk -/
def termsOf (code : Nat) (cols : List PTree) : List (Nat × PTree) := cols.map (fun c => (code, c))

section Eval
open Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast
variable {α : Type u} [CommRing α]

/-- `G(code)(x,y,z) * c(x,y,z)^2` -/
def termVal (G : Nat → PTree) (x y z : α) (p : Nat × PTree) : α :=
  (G p.1).toPoly.eval x y z * (p.2.toPoly.eval x y z * p.2.toPoly.eval x y z)

/-- sum of the term values of a list of SOS terms -/
def sumVal (G : Nat → PTree) (x y z : α) (l : List (Nat × PTree)) : α :=
  (l.map (termVal G x y z)).foldr (· + ·) 0

theorem sumVal_nil (G : Nat → PTree) (x y z : α) : sumVal G x y z [] = 0 := rfl

theorem sumVal_cons (G : Nat → PTree) (x y z : α) (p : Nat × PTree) (l : List (Nat × PTree)) :
    sumVal G x y z (p :: l) = termVal G x y z p + sumVal G x y z l := rfl

theorem sumVal_append (G : Nat → PTree) (x y z : α) (l₁ l₂ : List (Nat × PTree)) :
    sumVal G x y z (l₁ ++ l₂) = sumVal G x y z l₁ + sumVal G x y z l₂ := by
  induction l₁ with
  | nil => rw [List.nil_append, sumVal_nil]; grind
  | cons p l ih => rw [List.cons_append, sumVal_cons, sumVal_cons, ih]; grind

theorem eval_zeroTree (x y z : α) : zeroTree.toPoly.eval x y z = 0 := by
  simp only [zeroTree, PTree.toPoly, Poly.eval, Term.eval, Ring.intCast_zero]; grind

theorem mul_sumSq (G : Nat → PTree) (x y z : α) (code : Nat) (cols : List PTree) :
    (G code).toPoly.eval x y z *
        (cols.map (fun c => c.toPoly.eval x y z * c.toPoly.eval x y z)).foldr (· + ·) 0 =
      sumVal G x y z (termsOf code cols) := by
  induction cols with
  | nil => simp only [List.map_nil, List.foldr_nil, termsOf, sumVal_nil]; grind
  | cons c cs ih =>
    simp only [List.map_cons, List.foldr_cons, termsOf] at *
    rw [sumVal_cons, ← ih]
    simp only [termVal]
    grind

/-- **one chunk**: `next = prev + Σ_{c ∈ cols} G(code) c^2` on every commutative ring -/
theorem chunk_step (G : Nat → PTree) (w code : Nat) (cols : List PTree) (prev next : PTree)
    (h : (SOSChunk.ofCode G w code cols prev next).check = true) (x y z : α) :
    next.toPoly.eval x y z = prev.toPoly.eval x y z + sumVal G x y z (termsOf code cols) := by
  have hs := SOSChunk.check_sound _ h x y z
  simp only [SOSChunk.ofCode] at hs
  rw [hs, SOSBlock.eval_sqPoly_any, mul_sumSq]

end Eval

end ThomsonN10.Cert.L1.KC
