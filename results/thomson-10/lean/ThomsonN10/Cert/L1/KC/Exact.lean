/- Adapted from proof/lean/ClaudeL1/KC/Kernel.lean and Assembly.lean,
aravindkarthigeyan/thomson-n9-lean, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Cert.L1.KC.Assembly
namespace ThomsonN10.Cert.L1.KC
namespace Assembly
noncomputable section

def exactCheck (A : Assembly) (R : PTree) : Bool :=
  A.degOK && decide (R.maxDeg < 21) &&
    decide (A.l1bound + R.l1 < 2 ^ A.w) &&
    (A.kval - packVal A.w R == 0)

open Lean.Grind in
theorem exactCheck_sound (A : Assembly) (R : PTree) (h : A.exactCheck R = true)
    {α : Type u} [CommRing α] (x y z : α) :
    A.residual.eval x y z = R.toPoly.eval x y z := by
  simp only [exactCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨hd, hr⟩, hl⟩, hk⟩ := h
  let p := A.residual ++ Poly.neg R.toPoly
  have hp : p.DegLt 21 := by
    apply Poly.DegLt.append (A.residual_deg hd)
    intro s hs
    simp only [Poly.neg, List.mem_map] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    have := PTree.le_maxDeg R t ht
    simp only [Term.neg]
    omega
  have hpl : p.l1 < 2 ^ A.w := by
    simpa only [p, Poly.l1_append, Poly.l1_neg, A.l1_residual, PTree.l1_eq] using hl
  have he : uval (((2 ^ A.w : Nat) : Int)) (Poly.toU 21 p) = 0 := by
    rw [← Poly.eval_kron]
    simp only [p, Poly.eval_append, Poly.eval_neg]
    rw [Poly.eval_kron, A.kval_eq, PTree.eval_kron_pack]
    exact hk
  have hz := kron_eval_zero A.w 21 p hp hpl he x y z
  simp only [p, Poly.eval_append, Poly.eval_neg] at hz
  grind
end
end Assembly
end ThomsonN10.Cert.L1.KC
