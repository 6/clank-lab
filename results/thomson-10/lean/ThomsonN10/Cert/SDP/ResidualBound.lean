/- Adapted from global-soundness/n10/project/Thomson10Soundness/SDP/ResidualBound.lean (supplied accepted N10 port of proof/lean/ThomsonN9/SDP/ResidualBound.lean, aravindkarthigeyan/thomson-n9-lean, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e, MIT). -/
import ThomsonN10.Cert.SDP.Counting

/-! Exact residual losses and the ten-point three-point energy implication. -/

namespace ThomsonN10.Cert.SDP
open ThomsonN10 ThomsonN10.Interfaces

theorem coefficient_sum_abs_bound {ι : Type*} [Fintype ι]
    (c m : ι → ℝ) (hm : ∀ i, |m i| ≤ 1) :
    |∑ i, c i * m i| ≤ ∑ i, |c i| := by
  calc
    |∑ i, c i*m i| ≤ ∑ i, |c i*m i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |c i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      nlinarith [abs_nonneg (c i), hm i]

theorem coefficient_sum_lower_bound {ι : Type*} [Fintype ι]
    (c m : ι → ℝ) (hm : ∀ i, |m i| ≤ 1) :
    -(∑ i, |c i|) ≤ ∑ i, c i*m i :=
  (abs_le.mp (coefficient_sum_abs_bound c m hm)).1

theorem triple_monomial_abs_le_one {u v t : ℝ}
    (hu : |u| ≤ 1) (hv : |v| ≤ 1) (ht : |t| ≤ 1) (a b c : ℕ) :
    |u^a*v^b*t^c| ≤ 1 := by
  simp only [abs_mul, abs_pow]
  have h₁ := pow_le_one₀ (abs_nonneg u) hu (n := a)
  have h₂ := pow_le_one₀ (abs_nonneg v) hv (n := b)
  have h₃ := pow_le_one₀ (abs_nonneg t) ht (n := c)
  calc
    |u|^a*|v|^b*|t|^c ≤ 1*1*1 := by gcongr
    _ = 1 := by ring

theorem weighted_squares_nonneg {ι : Type*} [Fintype ι]
    (w p : ι → ℝ) (hw : ∀ i, 0 ≤ w i) : 0 ≤ ∑ i, w i*(p i)^2 :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)

theorem triple_average_normalization (h : Fin 10 → Fin 10 → ℝ)
    (hs : ∀ i j, h i j = h j i) (e : ℝ) :
    distinctSum (fun i j k => (h i j+h i k+h j k)/3-e/45) =
      16*pairSum h-16*e := by
  have heq : (fun i j k => (h i j+h i k+h j k)/3-e/45) =
      (fun i j k => (1/3 : ℝ)*(h i j+h i k+h j k)+(-e/45)) := by
    funext i j k
    ring
  rw [heq, distinctSum_add, distinctSum_smul, distinctSum_three_pairs h hs,
    distinctSum_const]
  ring

theorem pairSum_from_triple_certificate (h : Fin 10 → Fin 10 → ℝ)
    (K : Fin 10 → Fin 10 → Fin 10 → ℝ) (e L : ℝ)
    (hs : ∀ i j, h i j = h j i) (hK : 0 ≤ distinctSum K)
    (hpoint : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      K i j k-L ≤ (h i j+h i k+h j k)/3-e/45) :
    e-45*L ≤ pairSum h := by
  have hsum := distinctSum_mono hpoint
  have hleft : distinctSum (fun i j k => K i j k-L) = distinctSum K-720*L := by
    simp only [sub_eq_add_neg, distinctSum_add, distinctSum_const]
    ring
  rw [hleft, triple_average_normalization h hs e] at hsum
  linarith

theorem coulomb_from_triple_certificate (x : Configuration)
    (h : Fin 10 → Fin 10 → ℝ) (K : Fin 10 → Fin 10 → Fin 10 → ℝ) (e L : ℝ)
    (hs : ∀ i j, h i j = h j i)
    (hminorant : ∀ i j, i ≠ j → h i j ≤ (‖x i-x j‖)⁻¹)
    (hK : 0 ≤ distinctSum K)
    (hpoint : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      K i j k-L ≤ (h i j+h i k+h j k)/3-e/45) :
    e-45*L ≤ coulombEnergy x := by
  apply (pairSum_from_triple_certificate h K e L hs hK hpoint).trans
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j hj
  exact hminorant i j (ne_of_lt (Finset.mem_Ioi.mp hj))

end ThomsonN10.Cert.SDP
