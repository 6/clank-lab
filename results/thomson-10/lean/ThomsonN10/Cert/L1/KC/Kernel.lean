/- Adapted from proof/lean/ClaudeL1/KC/Kernel.lean, aravindkarthigeyan/thomson-n9-lean, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
/-
ThomsonN10.Cert.L1.KC.Kernel : kernel-evaluable check that the sum of the kernel-block expressions
`Σ_k exprPoly (B'_k) k` equals an explicit collected integer polynomial `total` (Kronecker zero
test).  The expressions are never expanded: their Kronecker value is computed by `exprVal` at the
integer point `(2^w, 2^(21w), 2^(441w))`, their uncollected l1 by `600 * colL1 * qL1`, their degree
from the column shapes (`colsOK`).

Core Lean only (upstream L1 implementation).
-/
import ThomsonN10.Cert.L1.KC.Ops

namespace ThomsonN10.Cert.L1.KC

/-- `Σ_j exprPoly (bs[j]) (k + j)` -/
def kernelPolyAux : List (List (List Int)) → Nat → Poly
  | [], _ => []
  | b :: bs, k => exprPoly b k ++ kernelPolyAux bs (k + 1)

/-- `Σ_k exprPoly (bs[k]) k` -/
def kernelPoly (bs : List (List (List Int))) : Poly := kernelPolyAux bs 0

def kernelL1Aux : List (List (List Int)) → Nat → Nat
  | [], _ => 0
  | b :: bs, k => 600 * colL1 b * qL1 k + kernelL1Aux bs (k + 1)

def blocksOK : List (List (List Int)) → Nat → Bool
  | [], _ => true
  | b :: bs, k => colsOK b k && blocksOK bs (k + 1)

theorem l1_kernelPolyAux (bs : List (List (List Int))) (k : Nat) :
    (kernelPolyAux bs k).l1 = kernelL1Aux bs k := by
  induction bs generalizing k with
  | nil => rfl
  | cons b bs ih => simp only [kernelPolyAux, kernelL1Aux, Poly.l1_append, l1_exprPoly, ih]

theorem deg_kernelPolyAux (bs : List (List (List Int))) (k : Nat) (h : blocksOK bs k = true) :
    Deg3 20 20 20 (kernelPolyAux bs k) := by
  induction bs generalizing k with
  | nil => intro s hs; cases hs
  | cons b bs ih =>
    simp only [blocksOK, Bool.and_eq_true] at h
    exact (deg_exprPoly b k h.1).append (ih (k + 1) h.2)

section Eval
open Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast
variable {α : Type u} [CommRing α]

def kernelValAux (x y z : α) : List (List (List Int)) → Nat → α
  | [], _ => 0
  | b :: bs, k => exprVal b k x y z + kernelValAux x y z bs (k + 1)

theorem eval_kernelPolyAux (x y z : α) (bs : List (List (List Int))) (k : Nat) :
    (kernelPolyAux bs k).eval x y z = kernelValAux x y z bs k := by
  induction bs generalizing k with
  | nil => rfl
  | cons b bs ih => simp only [kernelPolyAux, kernelValAux, Poly.eval_append, eval_exprPoly, ih]

end Eval

/-- kernel-total check data: factor columns of blocks `k = 0, 1, ...` and the claimed total -/
structure KTotal where
  w : Nat
  blocks : List (List (List Int))
  total : PTree
deriving Inhabited

namespace KTotal
noncomputable section

def residual (K : KTotal) : Poly := kernelPoly K.blocks ++ Poly.neg K.total.toPoly

def kval (K : KTotal) : Int :=
  kernelValAux (((2 ^ K.w : Nat) : Int)) (((2 ^ (K.w * 21) : Nat) : Int))
      (((2 ^ (K.w * (21 * 21)) : Nat) : Int)) K.blocks 0 -
    ishl (K.total.pack K.w 21).1 (K.w * (K.total.pack K.w 21).2)

def check (K : KTotal) : Bool :=
  blocksOK K.blocks 0 && decide (K.total.maxDeg < 21) &&
    decide (kernelL1Aux K.blocks 0 + K.total.l1 < 2 ^ K.w) && (K.kval == 0)

theorem residual_deg (K : KTotal) (h1 : blocksOK K.blocks 0 = true) (h2 : K.total.maxDeg < 21) :
    K.residual.DegLt 21 := by
  intro s hs
  simp only [residual, List.mem_append] at hs
  rcases hs with hs | hs
  · have := deg_kernelPolyAux K.blocks 0 h1 s hs; omega
  · simp only [Poly.neg, List.mem_map] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    have := PTree.le_maxDeg K.total t ht
    simp only [Term.neg]; omega

theorem l1_residual (K : KTotal) : K.residual.l1 = kernelL1Aux K.blocks 0 + K.total.l1 := by
  simp only [residual, Poly.l1_append, Poly.l1_neg, kernelPoly, l1_kernelPolyAux, PTree.l1_eq]

theorem kval_eq (K : KTotal) :
    uval (((2 ^ K.w : Nat) : Int)) (Poly.toU 21 K.residual) = K.kval := by
  rw [← Poly.eval_kron]
  simp only [residual, Poly.eval_append, Poly.eval_neg, kernelPoly, eval_kernelPolyAux,
    PTree.eval_kron_pack, kval, two_pow_mul_cast]
  grind

open Lean.Grind in
/-- **Soundness**: `Σ_k exprPoly (blocks[k]) k = total` on every commutative ring. -/
theorem check_sound (K : KTotal) (h : K.check = true) {α : Type u} [CommRing α] (x y z : α) :
    (kernelPoly K.blocks).eval x y z = K.total.toPoly.eval x y z := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hz := kron_eval_zero K.w 21 K.residual (residual_deg K h1 h2)
    (by rw [l1_residual]; exact h3) (by rw [kval_eq]; exact h4) x y z
  simp only [residual, Poly.eval_append, Poly.eval_neg] at hz
  grind

end
end KTotal

end ThomsonN10.Cert.L1.KC
