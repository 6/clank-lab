import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

/- Continuum two-increasing mechanism. Its convexity inputs are instantiated for
   the exact generator in Copula.lean and GeneratorAdmissible.lean. -/
namespace FT23
open Set

lemma convex_four_point {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f)
    (x h k : ℝ) (hh : 0 ≤ h) (hk : 0 ≤ k) :
    f (x+h) + f (x+k) ≤ f x + f (x+h+k) := by
  by_cases hz : h+k = 0
  · have hh0 : h = 0 := by linarith
    have hk0 : k = 0 := by linarith
    simp [hh0, hk0]
  have hd : 0 < h+k := lt_of_le_of_ne (add_nonneg hh hk) (Ne.symm hz)
  have hs : k/(h+k) + h/(h+k) = 1 := by field_simp; ring
  have hs' : h/(h+k) + k/(h+k) = 1 := by linarith
  have hcomb : k/(h+k)*x + h/(h+k)*(x+h+k) = x+h := by field_simp; ring
  have kcomb : h/(h+k)*x + k/(h+k)*(x+h+k) = x+k := by field_simp; ring
  have hfirst := hf.2 (mem_univ x) (mem_univ (x+h+k))
    (div_nonneg hk hd.le) (div_nonneg hh hd.le) hs
  have hsecond := hf.2 (mem_univ x) (mem_univ (x+h+k))
    (div_nonneg hh hd.le) (div_nonneg hk hd.le) hs'
  simp only [smul_eq_mul] at hfirst hsecond
  rw [hcomb] at hfirst
  rw [kcomb] at hsecond
  calc
    f (x+h) + f (x+k) ≤
        (k/(h+k)*f x + h/(h+k)*f (x+h+k)) +
        (h/(h+k)*f x + k/(h+k)*f (x+h+k)) := add_le_add hfirst hsecond
    _ = f x + f (x+h+k) := by field_simp; ring

/-- Convexity alone, without differentiability or a density. -/
lemma convex_ordered_rectangle {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    0 ≤ f (a+c) - f (b+c) - f (a+d) + f (b+d) := by
  have h := convex_four_point hf (a+c) (b-a) (d-c) (sub_nonneg.mpr hab) (sub_nonneg.mpr hcd)
  have h1 : a+c+(b-a) = b+c := by ring
  have h2 : a+c+(d-c) = a+d := by ring
  have h3 : a+c+(b-a)+(d-c) = b+d := by ring
  rw [h3, h1, h2] at h
  linarith

end FT23
