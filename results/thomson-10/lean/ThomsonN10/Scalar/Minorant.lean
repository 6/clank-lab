/- Adapted from proof/lean/ThomsonN9/Bernstein/Minorant.lean and MinorantCert.lean,
   aravindkarthigeyan/thomson-n9-lean, MIT, commit
   168ff0c98cab4dfda0460ba55f8d169070ac385e. -/
import ThomsonN10.Scalar.Bridge
import ThomsonN10.Scalar.Global00
import ThomsonN10.Scalar.Global01
import ThomsonN10.Scalar.Global02
import ThomsonN10.Scalar.Global03
import ThomsonN10.Scalar.Global04
import ThomsonN10.Scalar.Global05
import ThomsonN10.Scalar.Global06
import ThomsonN10.Scalar.Global07
import ThomsonN10.Scalar.Global08
import ThomsonN10.Scalar.Global09
import ThomsonN10.Scalar.Global10
import ThomsonN10.Scalar.Global11
namespace ThomsonN10.Scalar
open Bernstein

theorem MinorantBound_holds : ThomsonN10.Interfaces.MinorantBound := by
  intro t ht1 ht2
  have hcap : t ≤ (13:ℝ)/20 := by simpa [pairCap] using ht2
  have ht : t < 1 := by linarith
  obtain ⟨hy, hyt, hs⟩ := sqrt_subst ht
  let y := Real.sqrt ((1-t)/2)
  have hylo : (8:ℝ) ≤ 20*y := by
    have hl := Real.sqrt_le_sqrt (show (2/5:ℝ)^2 ≤ (1-t)/2 by linarith)
    rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2/5)] at hl
    dsimp [y]
    linarith
  have hyhi : (20:ℝ)*y ≤ 20 := by
    have hu := Real.sqrt_le_sqrt (show (1-t)/2 ≤ (1:ℝ) by linarith)
    rw [Real.sqrt_one] at hu
    dsimp [y]
    linarith
  have hp : 0 ≤ polyEval globalPoly y := by
    by_cases h0 : (20:ℝ)*y ≤ 9
    · exact checkInterval_sound global_cert0 y (by norm_num; linarith) h0
    by_cases h1 : (20:ℝ)*y ≤ 10
    · exact checkInterval_sound global_cert1 y (by norm_num; linarith) h1
    by_cases h2 : (20:ℝ)*y ≤ 11
    · exact checkInterval_sound global_cert2 y (by norm_num; linarith) h2
    by_cases h3 : (20:ℝ)*y ≤ 12
    · exact checkInterval_sound global_cert3 y (by norm_num; linarith) h3
    by_cases h4 : (20:ℝ)*y ≤ 13
    · exact checkInterval_sound global_cert4 y (by norm_num; linarith) h4
    by_cases h5 : (20:ℝ)*y ≤ 14
    · exact checkInterval_sound global_cert5 y (by norm_num; linarith) h5
    by_cases h6 : (20:ℝ)*y ≤ 15
    · exact checkInterval_sound global_cert6 y (by norm_num; linarith) h6
    by_cases h7 : (20:ℝ)*y ≤ 16
    · exact checkInterval_sound global_cert7 y (by norm_num; linarith) h7
    by_cases h8 : (20:ℝ)*y ≤ 17
    · exact checkInterval_sound global_cert8 y (by norm_num; linarith) h8
    by_cases h9 : (20:ℝ)*y ≤ 18
    · exact checkInterval_sound global_cert9 y (by norm_num; linarith) h9
    by_cases h10 : (20:ℝ)*y ≤ 19
    · exact checkInterval_sound global_cert10 y (by norm_num; linarith) h10
    exact checkInterval_sound global_cert11 y (by norm_num; linarith) hyhi
  rw [minorant_eq]
  exact potential_bound ht (by norm_num [denominator]) hp

end ThomsonN10.Scalar
#print axioms ThomsonN10.Scalar.MinorantBound_holds
