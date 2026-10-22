/- Adapted from proof/lean/ClaudeL1/Bridge.lean, aravindkarthigeyan/thomson-n9-lean, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
/-
ThomsonN10.Cert.L1.Bridge : from the core checker (`Poly.eval` over `Lean.Grind.CommRing`) to ordinary real
polynomial expressions.  Light Mathlib imports only (no upstream modules).

* `eval_nil_R`, `eval_cons_R`: at `ℝ` (Mathlib's `Lean.Grind.CommRing ℝ` instance, which exists at the
  pinned commit as `Field.toGrindField.toCommRing`), `Poly.eval` is the usual sum of
  `c * x^a * y^b * z^d` (definitional, `rfl`).
* `eval_eq_box` (regrouping): `p.DegLt D → p.eval x y z = Σ_{a,b,d<D} coeff p a b d * x^a y^b z^d`.
* `boxL1_eq_sum`: `boxL1 D p = Σ_{a,b,d<D} |coeff p a b d|` (as reals).
* `expr_eq_corrected` (generic kernel bridge): for integer factor columns `cols`,
  `(exprPoly cols k).eval u v t = 54 * 2^400 * myCorrected (kB cols) kp k u v t`, where `myCorrected`
  is a verbatim copy of the upstream project's `correctedFactorKernel` (identified with it in `ThomsonN10.Cert.L1.Main`).
* `gtree_eval`: the multiplier table is `10^4 * w6 (13/20)`, `w6` = the upstream project's `domainWeight` formula.

upstream L1 implementation.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import ThomsonN10.Cert.L1.KC.Ops
import ThomsonN10.Cert.L1.KC.Kernel
import ThomsonN10.Cert.L1.KC.Chain
import ThomsonN10.Cert.L1.KC.Assembly
import ThomsonN10.Cert.L1.Data.Mult

set_option exponentiation.threshold 1000

namespace ThomsonN10.Cert.L1
open ThomsonN10.Cert.L1.KC

/-! ### `Poly.eval` at `ℝ` -/

theorem eval_nil_R (x y z : ℝ) : Poly.eval x y z ([] : Poly) = 0 := rfl

theorem eval_cons_R (x y z : ℝ) (s : Term) (p : Poly) :
    Poly.eval x y z (s :: p) = (s.c : ℝ) * (x ^ s.a * y ^ s.b * z ^ s.d) + Poly.eval x y z p := rfl

theorem horner_nil_R (x : ℝ) : horner x [] = 0 := rfl
theorem horner_cons_R (x : ℝ) (c : ℤ) (cs : List ℤ) :
    horner x (c :: cs) = (c : ℝ) + x * horner x cs := rfl

/-! ### Regrouping by collected coefficients -/

theorem ite_sameExp (s : Term) (a b d : ℕ) :
    ((if s.sameExp a b d = true then s.c else 0 : ℤ) : ℝ) =
      if (a = s.a ∧ b = s.b ∧ d = s.d) then (s.c : ℝ) else 0 := by
  by_cases h : a = s.a ∧ b = s.b ∧ d = s.d
  · obtain ⟨rfl, rfl, rfl⟩ := h
    have hs : s.sameExp s.a s.b s.d = true := by simp [Term.sameExp]
    simp [hs]
  · have hs : s.sameExp a b d = false := by
      simp only [Term.sameExp, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
      omega
    simp [hs, h]

theorem box_sum_single (D : ℕ) (s : Term) (h : s.a < D ∧ s.b < D ∧ s.d < D) (x y z : ℝ) :
    ∑ a : Fin D, ∑ b : Fin D, ∑ d : Fin D,
      ((if s.sameExp a b d = true then s.c else 0 : ℤ) : ℝ) * (x ^ (a : ℕ) * y ^ (b : ℕ) * z ^ (d : ℕ)) =
    (s.c : ℝ) * (x ^ s.a * y ^ s.b * z ^ s.d) := by
  simp only [ite_sameExp]
  rw [Fintype.sum_eq_single ⟨s.a, h.1⟩]
  · rw [Fintype.sum_eq_single ⟨s.b, h.2.1⟩]
    · rw [Fintype.sum_eq_single ⟨s.d, h.2.2⟩]
      · simp
      · intro d hd
        have : (d : ℕ) ≠ s.d := fun e => hd (Fin.ext e)
        simp [this]
    · intro b hb
      apply Finset.sum_eq_zero
      intro d _
      have : (b : ℕ) ≠ s.b := fun e => hb (Fin.ext e)
      simp [this]
  · intro a ha
    apply Finset.sum_eq_zero
    intro b _
    apply Finset.sum_eq_zero
    intro d _
    have : (a : ℕ) ≠ s.a := fun e => ha (Fin.ext e)
    simp [this]

/-- **Regrouping lemma**: a polynomial with all exponents `< D` is the box sum of its collected
coefficients times monomials. -/
theorem eval_eq_box (D : ℕ) (p : Poly) (hp : p.DegLt D) (x y z : ℝ) :
    Poly.eval x y z p = ∑ a : Fin D, ∑ b : Fin D, ∑ d : Fin D,
      (p.coeff a b d : ℝ) * (x ^ (a : ℕ) * y ^ (b : ℕ) * z ^ (d : ℕ)) := by
  induction p with
  | nil => simp [Poly.coeff, eval_nil_R]
  | cons s p ih =>
    have hs := hp s (List.mem_cons_self ..)
    have hp' : Poly.DegLt D p := fun t ht => hp t (List.mem_cons_of_mem _ ht)
    rw [eval_cons_R, ih hp']
    simp only [Poly.coeff, Int.cast_add, add_mul, Finset.sum_add_distrib]
    rw [box_sum_single D s hs]

theorem nsum_eq_sum (S : ℕ) (f : ℕ → ℕ) : nsum S f = ∑ i : Fin S, f i := by
  induction S generalizing f with
  | zero => rfl
  | succ S ih =>
    rw [nsum, ih, Fin.sum_univ_succ]
    simp

/-- the exact l1 of the collected coefficients, as a real box sum -/
theorem boxL1_eq_sum (D : ℕ) (p : Poly) :
    (boxL1 D p : ℝ) = ∑ a : Fin D, ∑ b : Fin D, ∑ d : Fin D, |(p.coeff a b d : ℝ)| := by
  simp only [boxL1, nsum_eq_sum, Nat.cast_sum, Nat.cast_natAbs, Int.cast_abs]
  calc ∑ d : Fin D, ∑ b : Fin D, ∑ a : Fin D, |(p.coeff a b d : ℝ)|
      = ∑ d : Fin D, ∑ a : Fin D, ∑ b : Fin D, |(p.coeff a b d : ℝ)| := by
        apply Finset.sum_congr rfl; intro d _; exact Finset.sum_comm
    _ = ∑ a : Fin D, ∑ d : Fin D, ∑ b : Fin D, |(p.coeff a b d : ℝ)| := Finset.sum_comm
    _ = ∑ a : Fin D, ∑ b : Fin D, ∑ d : Fin D, |(p.coeff a b d : ℝ)| := by
        apply Finset.sum_congr rfl; intro a _; exact Finset.sum_comm

/-! ### Horner and list sums -/

theorem horner_eq_sum (x : ℝ) : ∀ (n : ℕ) (cs : List ℤ), cs.length ≤ n →
    horner x cs = ∑ i : Fin n, ((cs.getD i 0 : ℤ) : ℝ) * x ^ (i : ℕ)
  | 0, cs, h => by
    have : cs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [horner_nil_R]
  | n + 1, [], _ => by simp [horner_nil_R]
  | n + 1, c :: cs, h => by
    rw [horner_cons_R, Fin.sum_univ_succ, horner_eq_sum x n cs (by simp at h; omega)]
    simp only [Fin.val_zero, Fin.val_succ, List.getD_cons_zero, List.getD_cons_succ, pow_zero,
      mul_one, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ]; ring

theorem sum_getD_eq (f : List ℤ → ℝ) (hf : f [] = 0) : ∀ (n : ℕ) (l : List (List ℤ)),
    l.length ≤ n → ∑ r : Fin n, f (l.getD r []) = (l.map f).sum
  | 0, l, h => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp
  | n + 1, [], _ => by simp [hf]
  | n + 1, c :: l, h => by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, List.getD_cons_zero, List.getD_cons_succ]
    rw [sum_getD_eq f hf n l (by simp at h; omega), List.map_cons, List.sum_cons]

theorem colSum_eq (x y : ℝ) (cols : List (List ℤ)) :
    colSum x y cols = (cols.map (fun c => horner x c * horner y c)).sum := by
  induction cols with
  | nil => rfl
  | cons c cs ih => rw [List.map_cons, List.sum_cons, ← ih]; rfl

/-! ### Verbatim copies of the upstream project's kernel definitions (identified with the upstream project's in `Main`) -/

noncomputable def myCircle (a b : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => a
  | n+2 => 2*a*myCircle a b (n+1)-b*myCircle a b n

noncomputable def myThreePoint (k : ℕ) (u v t : ℝ) : ℝ :=
  myCircle (t-u*v) ((1-u^2)*(1-v^2)) k

noncomputable def myEdgeSym (F : ℝ → ℝ → ℝ → ℝ) (u v t : ℝ) : ℝ :=
  (F u v t+F v u t+F u t v+F t u v+F v t u+F t v u)/6

noncomputable def myFactorWeight {κ ρ : Type*} [Fintype κ]
    (B : κ → ρ → ℝ) (p : κ → ℝ → ℝ) (r : ρ) (u : ℝ) : ℝ :=
  ∑ i, B i r*p i u

noncomputable def myRooted {κ ρ : Type*} [Fintype κ] [Fintype ρ]
    (B : κ → ρ → ℝ) (p : κ → ℝ → ℝ) (k : ℕ) (u v t : ℝ) : ℝ :=
  ∑ r, myFactorWeight B p r u*myFactorWeight B p r v*myThreePoint k u v t

noncomputable def myCorrected {κ ρ : Type*} [Fintype κ] [Fintype ρ]
    (B : κ → ρ → ℝ) (p : κ → ℝ → ℝ) (k : ℕ) (u v t : ℝ) : ℝ :=
  let S := myEdgeSym (myRooted B p k)
  8*S u v t+S u u 1+S v v 1+S t t 1+S 1 1 1/9

theorem circ_eq_myCircle (a b : ℝ) (n : ℕ) : circ a b n = myCircle a b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rfl
    | 1, _ => rfl
    | n + 2, ih =>
      rw [circ_succ_succ, myCircle, ih (n + 1) (by omega), ih n (by omega)]
      ring

theorem qVal_eq (k : ℕ) (x y z : ℝ) : qVal x y z k = myThreePoint k x y z := by
  rw [qVal, circ_eq_myCircle, myThreePoint, pow_two, pow_two]

/-- the real factor matrix of a kernel block: `kB cols i r = cols[r][i] / 2^200` -/
noncomputable def kB (cols : List (List ℤ)) (i r : Fin 11) : ℝ :=
  (((cols.getD r []).getD i 0 : ℤ) : ℝ) / 2 ^ 200

/-- monomial features `x^i` -/
noncomputable def kp (i : Fin 11) (x : ℝ) : ℝ := x ^ (i : ℕ)

theorem getD_length_le (cols : List (List ℤ)) (hl : ∀ c ∈ cols, c.length ≤ 11) (r : ℕ) :
    (cols.getD r []).length ≤ 11 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : cols[r]? with
  | none => simp
  | some c => simpa using hl c (List.mem_of_getElem? h)

theorem fw_eq (cols : List (List ℤ)) (hl : ∀ c ∈ cols, c.length ≤ 11) (r : Fin 11) (x : ℝ) :
    myFactorWeight (kB cols) kp r x = horner x (cols.getD r []) / 2 ^ 200 := by
  rw [horner_eq_sum x 11 _ (getD_length_le cols hl r), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simp only [kB, kp]
  ring

theorem rooted_eq (cols : List (List ℤ)) (hc : cols.length ≤ 11) (hl : ∀ c ∈ cols, c.length ≤ 11)
    (k : ℕ) (x y z : ℝ) :
    rootVal cols k x y z = 2 ^ 400 * myRooted (kB cols) kp k x y z := by
  have hsum : ∑ r : Fin 11, myFactorWeight (kB cols) kp r x * myFactorWeight (kB cols) kp r y =
      colSum x y cols / 2 ^ 400 := by
    simp only [fw_eq cols hl]
    rw [colSum_eq, ← sum_getD_eq (fun c => horner x c * horner y c)
      (by simp [horner_nil_R]) 11 cols hc, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r _
    ring
  simp only [rootVal, myRooted, qVal_eq, ← Finset.sum_mul, hsum]
  ring

/-- **Generic kernel bridge**: the checker's kernel expression is `54 δ²` times (the copy of)
the upstream project's `correctedFactorKernel` with factor matrix `cols[r][i] / 2^200` and features `x^i`. -/
theorem expr_eq_corrected (cols : List (List ℤ)) (hc : cols.length ≤ 11)
    (hl : ∀ c ∈ cols, c.length ≤ 11) (k : ℕ) (u v t : ℝ) :
    (exprPoly cols k).eval u v t = 54 * 2 ^ 400 * myCorrected (kB cols) kp k u v t := by
  rw [eval_exprPoly]
  simp only [exprVal, symVal, rooted_eq cols hc hl, myCorrected, myEdgeSym]
  push_cast
  ring

/-! ### The multiplier table -/

/-- the upstream project's `domainWeight M u v t c` as a function of `c : ℕ` (zero for `c ≥ 6`) -/
noncomputable def w6 (M u v t : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1+u
  | 2 => M-u
  | 3 => 1+2*u*v*t-u^2-v^2-t^2
  | 4 => (1+u)*(M-u)
  | 5 => (1+2*u*v*t-u^2-v^2-t^2)*(1+u)*(M-u)
  | _ => 0

theorem gtree_eval (c : ℕ) (u v t : ℝ) :
    (Data.gtree c).toPoly.eval u v t = 20 * w6 (13/20) u v t c := by
  rcases c with _ | _ | _ | _ | _ | _ | c <;>
    simp [Data.gtree, w6, PTree.toPoly, eval_cons_R, eval_nil_R, Int.cast_negSucc] <;> ring

/-! ### SOS sums -/

theorem sumVal_R (G : ℕ → PTree) (x y z : ℝ) (l : List (ℕ × PTree)) :
    sumVal G x y z l = (l.map (termVal G x y z)).sum := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [sumVal_cons, ih, List.map_cons, List.sum_cons]


end ThomsonN10.Cert.L1
