import FT23.GeneratorInverse
import FT23.Copula

noncomputable section
open Set
namespace FT23

lemma convex_exp_affine (m c : ℝ) :
    ConvexOn ℝ univ (fun x : ℝ => Real.exp (m*x+c)) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := convexOn_exp.2 (mem_univ (m*x+c)) (mem_univ (m*y+c)) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have he : a*(m*x+c)+b*(m*y+c) = m*(a*x+b*y)+c := by
    calc
      _ = m*(a*x+b*y)+(a+b)*c := by ring
      _ = _ := by rw [hab, one_mul]
  rw [he] at h
  exact h

lemma psi_convex_univ : ConvexOn ℝ univ psi := by
  have h := (convex_exp_affine (-1) 0).sup (convex_exp_affine (-(1/2:ℝ)) (-Real.log 4))
  have he (t : ℝ) : psi t = max (Real.exp ((-1)*t+0))
      (Real.exp ((-(1/2:ℝ))*t + (-Real.log 4))) := by
    rw [psi_exp_max]
    rcases le_total (-t) (-t/2-Real.log 4) with ht | ht
    · rw [max_eq_right ht]
      have ha : (-t/2-Real.log 4) = (-(1/2:ℝ))*t+(-Real.log 4) := by ring
      have hb : (-1)*t+0 ≤ (-(1/2:ℝ))*t+(-Real.log 4) := by linarith
      rw [ha, max_eq_right (Real.exp_le_exp.mpr hb)]
    · rw [max_eq_left ht]
      have ha : -t = (-1)*t+0 := by ring
      have hb : (-(1/2:ℝ))*t+(-Real.log 4) ≤ (-1)*t+0 := by linarith
      rw [ha, max_eq_left (Real.exp_le_exp.mpr hb)]
  have hfun : psi = fun t => max (Real.exp ((-1)*t+0))
      (Real.exp ((-(1/2:ℝ))*t + (-Real.log 4))) := funext he
  rw [hfun]
  exact h

lemma phi_convex_positive : ConvexOn ℝ (Ioc (0:ℝ) 1) phi := by
  have hn : ConvexOn ℝ (Ioi (0:ℝ)) (fun u => -Real.log u) :=
    strictConcaveOn_log_Ioi.concaveOn.neg
  have htwo := (ConvexOn.smul (by norm_num : (0:ℝ) ≤ 2) hn).add_const (-Real.log 16)
  have hmax := hn.sup htwo
  have hrestricted := hmax.subset (fun u hu => hu.1) (convex_Ioc (0:ℝ) 1)
  change ConvexOn ℝ (Ioc (0:ℝ) 1)
    (fun u : ℝ => max (-Real.log u) (2 * (-Real.log u) + (-Real.log 16))) at hrestricted
  have he : (fun u : ℝ => max (-Real.log u) (2 * (-Real.log u) + (-Real.log 16))) = phi := by
    funext u
    unfold phi
    congr 1
    ring
  rw [he] at hrestricted
  exact hrestricted

theorem exact_copula : IsCopula C :=
  copula_of_core psi_convex_univ phi_antitone psi_antitone
    (fun t => (psi_positive t).le) phi_one (fun u hu => psi_phi_positive hu.1)

end FT23
