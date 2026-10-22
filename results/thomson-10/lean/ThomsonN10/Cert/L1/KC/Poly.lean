/- Adapted from proof/lean/ClaudeL1/KC/Poly.lean, aravindkarthigeyan/thomson-n9-lean, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
/-
ThomsonN10.Cert.L1.KC.Poly (copied from the upstream exact checker, namespace renamed) : sparse, *uncollected* integer polynomials in three variables.

A polynomial is a list of terms `c * u^a * v^b * t^d`; repeated exponents are allowed.
Evaluation is defined in every commutative ring (`Lean.Grind.CommRing`, the core-Lean
ring class; Mathlib provides an instance for every Mathlib `CommRing`, e.g. `ℝ`).

Written from scratch for the N=9 certificate project (core Lean 4 only, no Mathlib).
-/
namespace ThomsonN10.Cert.L1.KC

/-- A term `c * u^a * v^b * t^d`. -/
structure Term where
  c : Int
  a : Nat
  b : Nat
  d : Nat
deriving Repr, DecidableEq, Inhabited

/-- Uncollected sparse polynomial in `u, v, t`. -/
abbrev Poly := List Term

namespace Term
def mul (s t : Term) : Term := ⟨s.c * t.c, s.a + t.a, s.b + t.b, s.d + t.d⟩
def neg (s : Term) : Term := ⟨-s.c, s.a, s.b, s.d⟩
/-- same exponent triple -/
def sameExp (s : Term) (a b d : Nat) : Bool := s.a == a && s.b == b && s.d == d
end Term

namespace Poly

def neg (p : Poly) : Poly := p.map Term.neg
def mul (p q : Poly) : Poly := p.flatMap (fun s => q.map (Term.mul s))
/-- concatenation of a list of polynomials (= their sum) -/
def sum : List Poly → Poly
  | [] => []
  | p :: ps => p ++ sum ps

/-- l1 norm of the *uncollected* coefficient list (an upper bound for the collected one). -/
def l1 : Poly → Nat
  | [] => 0
  | s :: p => s.c.natAbs + l1 p

/-- collected coefficient of `u^a v^b t^d`. -/
def coeff : Poly → Nat → Nat → Nat → Int
  | [], _, _, _ => 0
  | s :: p, a, b, d => (if s.sameExp a b d then s.c else 0) + coeff p a b d

/-- every exponent of every term is `< D`. -/
def DegLt (D : Nat) (p : Poly) : Prop := ∀ s ∈ p, s.a < D ∧ s.b < D ∧ s.d < D

/-! ### l1 and coefficient algebra -/

theorem l1_append (p q : Poly) : l1 (p ++ q) = l1 p + l1 q := by
  induction p with
  | nil => simp [l1]
  | cons s p ih => simp [l1, ih]; omega

theorem l1_neg (p : Poly) : l1 (neg p) = l1 p := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    simp only [neg, List.map_cons, l1, Term.neg, Int.natAbs_neg] at *
    rw [ih]

theorem l1_map_mul (s : Term) (q : Poly) : l1 (q.map (Term.mul s)) = s.c.natAbs * l1 q := by
  induction q with
  | nil => simp [l1]
  | cons t q ih => simp [l1, ih, Term.mul, Int.natAbs_mul, Nat.mul_add]

theorem l1_mul (p q : Poly) : l1 (mul p q) = l1 p * l1 q := by
  induction p with
  | nil => simp [mul, l1]
  | cons s p ih =>
    simp only [mul, List.flatMap_cons] at *
    rw [l1_append, l1_map_mul, ih, l1, Nat.add_mul]

theorem l1_sum (ps : List Poly) : l1 (sum ps) = (ps.map l1).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [sum, l1_append, ih]

theorem coeff_append (p q : Poly) (a b d : Nat) :
    coeff (p ++ q) a b d = coeff p a b d + coeff q a b d := by
  induction p with
  | nil => simp [coeff]
  | cons s p ih => simp only [List.cons_append, coeff, ih]; omega

theorem natAbs_coeff_le (p : Poly) (a b d : Nat) : (coeff p a b d).natAbs ≤ l1 p := by
  induction p with
  | nil => simp [coeff, l1]
  | cons s p ih =>
    simp only [coeff, l1]
    have h1 : (if s.sameExp a b d then s.c else 0).natAbs ≤ s.c.natAbs := by
      split <;> simp
    have := Int.natAbs_add_le (if s.sameExp a b d then s.c else 0) (coeff p a b d)
    omega

theorem DegLt.append {D : Nat} {p q : Poly} (hp : DegLt D p) (hq : DegLt D q) :
    DegLt D (p ++ q) := by
  intro s hs
  rcases List.mem_append.mp hs with h | h
  · exact hp s h
  · exact hq s h

theorem DegLt.neg {D : Nat} {p : Poly} (hp : DegLt D p) : DegLt D (Poly.neg p) := by
  intro s hs
  simp only [Poly.neg, List.mem_map] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  exact hp t ht

/-- max exponent (over the three variables) of a polynomial -/
def maxDeg : Poly → Nat
  | [] => 0
  | s :: p => max (max s.a (max s.b s.d)) (maxDeg p)

theorem le_maxDeg {p : Poly} {s : Term} (h : s ∈ p) :
    s.a ≤ maxDeg p ∧ s.b ≤ maxDeg p ∧ s.d ≤ maxDeg p := by
  induction p with
  | nil => cases h
  | cons t p ih =>
    simp only [maxDeg]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem degLt_of_maxDeg {D : Nat} {p : Poly} (h : maxDeg p < D) : DegLt D p := by
  intro s hs
  have := le_maxDeg hs
  omega

theorem maxDeg_mul_le (p q : Poly) : ∀ s ∈ mul p q,
    s.a ≤ maxDeg p + maxDeg q ∧ s.b ≤ maxDeg p + maxDeg q ∧ s.d ≤ maxDeg p + maxDeg q := by
  intro s hs
  simp only [mul, List.mem_flatMap, List.mem_map] at hs
  obtain ⟨s1, h1, s2, h2, rfl⟩ := hs
  have := le_maxDeg h1
  have := le_maxDeg h2
  simp only [Term.mul]
  omega

end Poly

/-! ### Evaluation in an arbitrary commutative ring -/

section Eval
open Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast

variable {α : Type u} [CommRing α]

/-- `Term.eval x y z s = c * (x^a * y^b * z^d)`. -/
def Term.eval (x y z : α) (s : Term) : α := (s.c : α) * (x ^ s.a * y ^ s.b * z ^ s.d)

def Poly.eval (x y z : α) : Poly → α
  | [] => 0
  | s :: p => s.eval x y z + Poly.eval x y z p

namespace Poly

theorem eval_nil (x y z : α) : Poly.eval x y z [] = 0 := rfl

theorem eval_append (x y z : α) (p q : Poly) :
    eval x y z (p ++ q) = eval x y z p + eval x y z q := by
  induction p with
  | nil => simp only [List.nil_append, eval]; grind
  | cons s p ih => simp only [List.cons_append, eval, ih]; grind

theorem Term.eval_neg (x y z : α) (s : Term) : s.neg.eval x y z = -(s.eval x y z) := by
  simp only [Term.eval, ThomsonN10.Cert.L1.KC.Term.neg, Ring.intCast_neg]; grind

theorem eval_neg (x y z : α) (p : Poly) : eval x y z (neg p) = -(eval x y z p) := by
  induction p with
  | nil => simp only [neg, List.map_nil, eval]; grind
  | cons s p ih =>
    simp only [neg, List.map_cons, eval] at *
    rw [ih, Term.eval_neg]; grind

theorem Term.eval_mul (x y z : α) (s t : Term) :
    (s.mul t).eval x y z = s.eval x y z * t.eval x y z := by
  simp only [Term.eval, ThomsonN10.Cert.L1.KC.Term.mul, Ring.intCast_mul, Semiring.pow_add]; grind

theorem eval_map_mul (x y z : α) (s : Term) (q : Poly) :
    eval x y z (q.map (Term.mul s)) = s.eval x y z * eval x y z q := by
  induction q with
  | nil => simp only [List.map_nil, eval]; grind
  | cons t q ih => simp only [List.map_cons, eval, ih, Term.eval_mul]; grind

theorem eval_mul (x y z : α) (p q : Poly) :
    eval x y z (mul p q) = eval x y z p * eval x y z q := by
  induction p with
  | nil => simp only [mul, List.flatMap_nil, eval]; grind
  | cons s p ih =>
    simp only [mul, List.flatMap_cons] at *
    rw [eval_append, eval_map_mul, ih, eval]; grind

theorem eval_sum (x y z : α) (ps : List Poly) :
    eval x y z (sum ps) = (ps.map (eval x y z)).foldr (· + ·) 0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [sum, eval_append, ih, List.map_cons, List.foldr_cons]

/-! ### Collected coefficients determine the polynomial function -/

/-- evaluation splits along any Boolean filter -/
theorem eval_filter_split (x y z : α) (f : Term → Bool) (p : Poly) :
    eval x y z p = eval x y z (p.filter f) + eval x y z (p.filter (fun s => !f s)) := by
  induction p with
  | nil => simp only [List.filter_nil, eval]; grind
  | cons s p ih =>
    by_cases hf : f s = true
    · simp only [List.filter_cons, hf, ite_true, Bool.not_true, eval, ih]; grind
    · simp only [Bool.not_eq_true] at hf
      simp only [List.filter_cons, hf, Bool.false_eq_true, ite_false, Bool.not_false, ite_true,
        eval, ih]; grind

/-- a block of terms with one common exponent evaluates to (collected coeff) * monomial -/
theorem eval_filter_same (x y z : α) (a b d : Nat) (p : Poly) :
    eval x y z (p.filter (fun s => s.sameExp a b d)) =
      ((coeff p a b d : Int) : α) * (x ^ a * y ^ b * z ^ d) := by
  induction p with
  | nil => simp only [List.filter_nil, eval, coeff, Ring.intCast_zero]; grind
  | cons s p ih =>
    by_cases hs : s.sameExp a b d = true
    · have hs' := hs
      simp only [ThomsonN10.Cert.L1.KC.Term.sameExp, Bool.and_eq_true, beq_iff_eq] at hs'
      obtain ⟨⟨ha, hb⟩, hd⟩ := hs'
      simp only [List.filter_cons, hs, ite_true, eval, ih, coeff, Ring.intCast_add, Term.eval,
        ha, hb, hd]
      grind
    · simp only [Bool.not_eq_true] at hs
      simp only [List.filter_cons, hs, Bool.false_eq_true, ite_false, ih, coeff]
      simp only [Int.zero_add]

theorem coeff_filter_not (p : Poly) (a b d a' b' d' : Nat) :
    coeff (p.filter (fun s => !s.sameExp a b d)) a' b' d' =
      if a' = a ∧ b' = b ∧ d' = d then 0 else coeff p a' b' d' := by
  induction p with
  | nil => simp [coeff]
  | cons s p ih =>
    by_cases hs : s.sameExp a b d = true
    · simp only [List.filter_cons, hs, Bool.not_true, Bool.false_eq_true, ite_false, ih, coeff]
      simp only [ThomsonN10.Cert.L1.KC.Term.sameExp, Bool.and_eq_true, beq_iff_eq] at hs
      obtain ⟨⟨ha, hb⟩, hd⟩ := hs
      by_cases h : a' = a ∧ b' = b ∧ d' = d
      · simp [h]
      · have : s.sameExp a' b' d' = false := by
          simp only [ThomsonN10.Cert.L1.KC.Term.sameExp, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
          omega
        simp [h, this]
    · simp only [Bool.not_eq_true] at hs
      simp only [List.filter_cons, hs, Bool.not_false, ite_true, coeff, ih]
      by_cases h : a' = a ∧ b' = b ∧ d' = d
      · obtain ⟨rfl, rfl, rfl⟩ := h
        simp [hs]
      · simp [h]

/-- If every collected coefficient vanishes, the polynomial function vanishes in every
commutative ring. -/
theorem eval_eq_zero_of_coeff (p : Poly) (h : ∀ a b d, coeff p a b d = 0) (x y z : α) :
    eval x y z p = 0 := by
  -- strong induction on the length
  suffices H : ∀ n (p : Poly), p.length ≤ n → (∀ a b d, coeff p a b d = 0) → eval x y z p = 0 from
    H p.length p (Nat.le_refl _) h
  intro n
  induction n with
  | zero =>
    intro p hp _
    have : p = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rfl
  | succ n ih =>
    intro p hp hc
    match p with
    | [] => rfl
    | s :: q =>
      rw [eval_filter_split x y z (fun t => t.sameExp s.a s.b s.d) (s :: q),
        eval_filter_same, hc, Ring.intCast_zero]
      have hlen : ((s :: q).filter (fun t => !t.sameExp s.a s.b s.d)).length ≤ n := by
        have hs : s.sameExp s.a s.b s.d = true := by simp [ThomsonN10.Cert.L1.KC.Term.sameExp]
        simp only [List.filter_cons, hs, Bool.not_true, Bool.false_eq_true, ite_false]
        have := List.length_filter_le (fun t => !t.sameExp s.a s.b s.d) q
        simp only [List.length_cons] at hp
        omega
      rw [ih _ hlen (fun a b d => by rw [coeff_filter_not]; split <;> simp [hc])]
      grind

end Poly
end Eval

end ThomsonN10.Cert.L1.KC
