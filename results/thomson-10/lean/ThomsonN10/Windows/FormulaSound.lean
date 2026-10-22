/- Adapted from aravindkarthigeyan/thomson-n9-lean, proof/lean/ClaudeWindow/FormulaSound.lean
   MIT, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e. See certificate/Windows/LICENSE-N9. -/
import ThomsonN10.Windows.WindowCheck
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Soundness of the interval determinant formulas

If the real arguments lie in the argument intervals, the real value of each formula lies in
the computed interval.
-/

namespace ThomsonN10.Windows

open Iv

theorem mem_d3 {A B C : Iv} {a b c : ℝ} (ha : A.Mem a) (hb : B.Mem b) (hc : C.Mem c) :
    (d3Iv A B C).Mem (d3R a b c) := by
  have h := mem_sub (mem_sub (mem_sub (mem_add (mem_const 1)
    (mem_mul (mem_const 2) (mem_mul (mem_mul ha hb) hc))) (mem_sq ha)) (mem_sq hb)) (mem_sq hc)
  unfold d3Iv
  convert h using 1
  unfold d3R; push_cast; ring

/-- The adjugate intervals enclose the real adjugate entries. -/
structure AdjMem (J : AdjIv) (a b c : ℝ) : Prop where
  m00 : J.a00.Mem (1 - c ^ 2)
  m11 : J.a11.Mem (1 - b ^ 2)
  m22 : J.a22.Mem (1 - a ^ 2)
  m01 : J.a01.Mem (b * c - a)
  m02 : J.a02.Mem (a * c - b)
  m12 : J.a12.Mem (a * b - c)

theorem mem_adj {A B C : Iv} {a b c : ℝ} (ha : A.Mem a) (hb : B.Mem b) (hc : C.Mem c) :
    AdjMem (adjIv A B C) a b c := by
  simp only [adjIv]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := mem_sub (mem_const 1) (mem_sq hc); convert h using 1; push_cast; ring
  · have h := mem_sub (mem_const 1) (mem_sq hb); convert h using 1; push_cast; ring
  · have h := mem_sub (mem_const 1) (mem_sq ha); convert h using 1; push_cast; ring
  · exact mem_sub (mem_mul hb hc) ha
  · exact mem_sub (mem_mul ha hc) hb
  · exact mem_sub (mem_mul ha hb) hc

theorem mem_norm {A B C V0 V1 V2 : Iv} {a b c v0 v1 v2 : ℝ}
    (ha : A.Mem a) (hb : B.Mem b) (hc : C.Mem c)
    (h0 : V0.Mem v0) (h1 : V1.Mem v1) (h2 : V2.Mem v2) :
    (normIv (d3Iv A B C) (adjIv A B C) V0 V1 V2).Mem (normR a b c v0 v1 v2) := by
  have hD := mem_d3 ha hb hc
  have hJ := mem_adj ha hb hc
  have h := mem_sub hD (mem_add (mem_add (mem_add (mem_mul hJ.m00 (mem_sq h0))
    (mem_mul hJ.m11 (mem_sq h1))) (mem_mul hJ.m22 (mem_sq h2)))
    (mem_mul (mem_const 2) (mem_add (mem_add (mem_mul hJ.m01 (mem_mul h0 h1))
      (mem_mul hJ.m02 (mem_mul h0 h2))) (mem_mul hJ.m12 (mem_mul h1 h2)))))
  unfold normIv
  convert h using 1
  unfold normR; push_cast; ring

theorem mem_pair {A B C V0 V1 V2 W0 W1 W2 T : Iv} {a b c v0 v1 v2 w0 w1 w2 t : ℝ}
    (ha : A.Mem a) (hb : B.Mem b) (hc : C.Mem c)
    (h0 : V0.Mem v0) (h1 : V1.Mem v1) (h2 : V2.Mem v2)
    (k0 : W0.Mem w0) (k1 : W1.Mem w1) (k2 : W2.Mem w2) (ht : T.Mem t) :
    (pairIv (d3Iv A B C) (adjIv A B C) V0 V1 V2 W0 W1 W2 T).Mem
      (pairR a b c v0 v1 v2 w0 w1 w2 t) := by
  have hD := mem_d3 ha hb hc
  have hJ := mem_adj ha hb hc
  have h := mem_sub (mem_mul ht hD)
    (mem_add (mem_add (mem_add (mem_add (mem_add (mem_add (mem_add (mem_add
      (mem_mul hJ.m00 (mem_mul h0 k0)) (mem_mul hJ.m01 (mem_mul h0 k1)))
      (mem_mul hJ.m02 (mem_mul h0 k2))) (mem_mul hJ.m01 (mem_mul h1 k0)))
      (mem_mul hJ.m11 (mem_mul h1 k1))) (mem_mul hJ.m12 (mem_mul h1 k2)))
      (mem_mul hJ.m02 (mem_mul h2 k0))) (mem_mul hJ.m12 (mem_mul h2 k1)))
      (mem_mul hJ.m22 (mem_mul h2 k2)))
  unfold pairIv
  convert h using 1
  unfold pairR; ring

end ThomsonN10.Windows
