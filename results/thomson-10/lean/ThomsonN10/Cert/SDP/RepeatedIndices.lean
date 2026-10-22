/- Adapted from global-soundness/n10/project/Thomson10Soundness/SDP/RepeatedIndices.lean (supplied accepted N10 port of proof/lean/ThomsonN9/SDP/RepeatedIndices.lean, aravindkarthigeyan/thomson-n9-lean, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e, MIT). -/
import ThomsonN10.Cert.SDP.Counting

namespace ThomsonN10.Cert.SDP
open ThomsonN10 ThomsonN10.Interfaces

noncomputable def fullSum (T : Fin 10 → Fin 10 → Fin 10 → ℝ) : ℝ := ∑ i, ∑ j, ∑ k, T i j k

theorem fullSum_repeated_indices (T : Fin 10 → Fin 10 → Fin 10 → ℝ)
    (B : Fin 10 → Fin 10 → ℝ) (c : ℝ)
    (h₁ : ∀ i j, T i i j = B i j) (h₂ : ∀ i j, T i j i = B i j)
    (h₃ : ∀ i j, T i j j = B i j) (hd : ∀ i, B i i = c) :
    fullSum T = distinctSum T+3*offDiagonalSum B+10*c := by
  classical
  have hsplit (i j k : Fin 10) : T i j k =
      (if i ≠ j ∧ i ≠ k ∧ j ≠ k then T i j k else 0)+
      (if i = j then B i k else 0)+(if i = k then B i j else 0)+
      (if j = k then B i j else 0)-(if i = j ∧ i = k then 2*c else 0) := by
    by_cases hij : i = j
    · subst j
      by_cases hik : i = k
      · subst k
        simp [h₁, hd]
        ring
      · simp [hik, h₁]
    · by_cases hik : i = k
      · subst k
        simp [hij, Ne.symm hij, h₂]
      · by_cases hjk : j = k
        · subst k
          simp [hij, h₃]
        · simp [hij, hik, hjk]
  have hs₁ : (∑ i : Fin 10, ∑ j : Fin 10, ∑ k : Fin 10,
      if i = j then B i k else 0) = ∑ i, ∑ j, B i j := by
    simp [Finset.sum_ite_irrel]
  have hs₂ : (∑ i : Fin 10, ∑ j : Fin 10, ∑ k : Fin 10,
      if i = k then B i j else 0) = ∑ i, ∑ j, B i j := by simp
  have hs₃ : (∑ i : Fin 10, ∑ j : Fin 10, ∑ k : Fin 10,
      if j = k then B i j else 0) = ∑ i, ∑ j, B i j := by simp
  have hs₄ : (∑ i : Fin 10, ∑ j : Fin 10, ∑ k : Fin 10,
      if i = j ∧ i = k then 2*c else 0) = 20*c := by
    simp [ite_and]
    ring
  have hb : (∑ i : Fin 10, ∑ j : Fin 10, B i j) = offDiagonalSum B+10*c := by
    have hterm (i j : Fin 10) : B i j = (if i = j then 0 else B i j)+
        (if i = j then c else 0) := by
      by_cases hij : i = j
      · subst j
        simp [hd]
      · simp [hij]
    calc
      (∑ i, ∑ j, B i j) = ∑ i, ∑ j,
          ((if i = j then 0 else B i j)+(if i = j then c else 0)) := by
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j
      _ = offDiagonalSum B+10*c := by simp [offDiagonalSum, Finset.sum_add_distrib]
  have hsum : fullSum T = distinctSum T+
      (∑ i : Fin 10, ∑ j : Fin 10, B i j)+(∑ i : Fin 10, ∑ j : Fin 10, B i j)+
      (∑ i : Fin 10, ∑ j : Fin 10, B i j)-20*c := by
    calc
      fullSum T = ∑ i, ∑ j, ∑ k,
          ((if i ≠ j ∧ i ≠ k ∧ j ≠ k then T i j k else 0)+
          (if i = j then B i k else 0)+(if i = k then B i j else 0)+
          (if j = k then B i j else 0)-(if i = j ∧ i = k then 2*c else 0)) := by
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => hsplit i j k
      _ = distinctSum T+(∑ i, ∑ j, B i j)+(∑ i, ∑ j, B i j)+
          (∑ i, ∑ j, B i j)-20*c := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hs₁, hs₂, hs₃, hs₄,
          distinctSum]
  rw [hsum, hb]
  ring

theorem corrected_kernel_sum (T : Fin 10 → Fin 10 → Fin 10 → ℝ)
    (B : Fin 10 → Fin 10 → ℝ) (c : ℝ)
    (h₁ : ∀ i j, T i i j = B i j) (h₂ : ∀ i j, T i j i = B i j)
    (h₃ : ∀ i j, T i j j = B i j) (hd : ∀ i, B i i = c)
    (hs : ∀ i j, B i j = B j i) :
    distinctSum (fun i j k => 8*T i j k+(B i j+B i k+B j k)+c/9) = 8*fullSum T := by
  rw [distinctSum_add, distinctSum_add, distinctSum_smul,
    distinctSum_three_pairs B hs, distinctSum_const,
    fullSum_repeated_indices T B c h₁ h₂ h₃ hd,
    offDiagonalSum_eq_twice_pairSum B hs]
  ring

theorem corrected_kernel_sum_nonneg (T : Fin 10 → Fin 10 → Fin 10 → ℝ)
    (B : Fin 10 → Fin 10 → ℝ) (c : ℝ)
    (h₁ : ∀ i j, T i i j = B i j) (h₂ : ∀ i j, T i j i = B i j)
    (h₃ : ∀ i j, T i j j = B i j) (hd : ∀ i, B i i = c)
    (hs : ∀ i j, B i j = B j i) (hT : 0 ≤ fullSum T) :
    0 ≤ distinctSum (fun i j k => 8*T i j k+(B i j+B i k+B j k)+c/9) := by
  rw [corrected_kernel_sum T B c h₁ h₂ h₃ hd hs]
  positivity

end ThomsonN10.Cert.SDP
