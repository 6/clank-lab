/- Adapted from global-soundness/n10/project/Thomson10Soundness/SDP/CertificateBound.lean (supplied accepted N10 port of proof/lean/ThomsonN9/SDP/CertificateBound.lean, aravindkarthigeyan/thomson-n9-lean, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e, MIT). -/
import ThomsonN10.Cert.SDP.FactoredKernels
import ThomsonN10.Cert.SDP.GeometryBounds
import ThomsonN10.Cert.SDP.ResidualBound

namespace ThomsonN10.Cert.SDP
open ThomsonN10 ThomsonN10.Interfaces

def TripleDomain (M u v t : ℝ) : Prop :=
  |u| ≤ 1 ∧ |v| ≤ 1 ∧ |t| ≤ 1 ∧ u ≤ M ∧ v ≤ M ∧ t ≤ M ∧
    0 ≤ 1+2*u*v*t-u^2-v^2-t^2

theorem TripleDomain.swap_first {M u v t : ℝ} (h : TripleDomain M u v t) :
    TripleDomain M v u t := by
  rcases h with ⟨hu, hv, ht, huM, hvM, htM, hg⟩
  exact ⟨hv, hu, ht, hvM, huM, htM, by nlinarith [hg]⟩

theorem TripleDomain.swap_last {M u v t : ℝ} (h : TripleDomain M u v t) :
    TripleDomain M u t v := by
  rcases h with ⟨hu, hv, ht, huM, hvM, htM, hg⟩
  exact ⟨hu, ht, hv, huM, htM, hvM, by nlinarith [hg]⟩

noncomputable def domainWeight (M u v t : ℝ) : Fin 6 → ℝ :=
  ![1, 1+u, M-u, 1+2*u*v*t-u^2-v^2-t^2, (1+u)*(M-u),
    (1+2*u*v*t-u^2-v^2-t^2)*(1+u)*(M-u)]

theorem domainWeight_nonneg {M u v t : ℝ} (h : TripleDomain M u v t)
    (b : Fin 6) : 0 ≤ domainWeight M u v t b := by
  have hlo : 0 ≤ 1+u := by linarith [(abs_le.mp h.1).1]
  have hhi : 0 ≤ M-u := by linarith [h.2.2.2.1]
  have hgram : 0 ≤ 1+2*u*v*t-u^2-v^2-t^2 := h.2.2.2.2.2.2
  fin_cases b <;> dsimp [domainWeight] <;> positivity

theorem edgeSymmetrize_nonneg_on_domain (F : ℝ → ℝ → ℝ → ℝ) (M : ℝ)
    (hF : ∀ u v t, TripleDomain M u v t → 0 ≤ F u v t)
    {u v t : ℝ} (h : TripleDomain M u v t) : 0 ≤ edgeSymmetrize F u v t := by
  have h₁ := hF _ _ _ h
  have h₂ := hF _ _ _ h.swap_first
  have h₃ := hF _ _ _ h.swap_last
  have h₄ := hF _ _ _ h.swap_last.swap_first
  have h₅ := hF _ _ _ h.swap_first.swap_last
  have h₆ := hF _ _ _ h.swap_first.swap_last.swap_first
  unfold edgeSymmetrize
  positivity

theorem unit_gram_mem_domain (x : Configuration) (hx : ∀ i, ‖x i‖ = 1)
    (M : ℝ) (hM : ∀ i j, i ≠ j → inner ℝ (x i) (x j) ≤ M)
    (i j k : Fin 10) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    TripleDomain M (inner ℝ (x i) (x j)) (inner ℝ (x i) (x k))
      (inner ℝ (x j) (x k)) := by
  exact ⟨unit_inner_abs_le_one _ _ (hx i) (hx j),
    unit_inner_abs_le_one _ _ (hx i) (hx k),
    unit_inner_abs_le_one _ _ (hx j) (hx k), hM i j hij, hM i k hik, hM j k hjk,
    unit_triple_gram_nonneg _ _ _ (hx i) (hx j) (hx k)⟩

theorem distinctSum_sum {ι : Type*} [Fintype ι]
    (T : ι → Fin 10 → Fin 10 → Fin 10 → ℝ) :
    distinctSum (fun i j k => ∑ b, T b i j k) = ∑ b, distinctSum (T b) := by
  classical
  unfold distinctSum
  let term (i j k : Fin 10) (b : ι) :=
    if i ≠ j ∧ i ≠ k ∧ j ≠ k then T b i j k else 0
  calc
    _ = ∑ i, ∑ j, ∑ k, ∑ b, term i j k b := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      simp only [term, Finset.sum_ite_irrel, Finset.sum_const_zero]
    _ = ∑ i, ∑ j, ∑ b, ∑ k, term i j k b := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ i, ∑ b, ∑ j, ∑ k, term i j k b := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem factored_certificate_pair_bound
    {β κ ρ σ η : Type*} [Fintype β] [Fintype κ] [Fintype ρ]
    [Fintype σ] [Fintype η]
    (B : β → κ → ρ → ℝ) (p : β → κ → ℝ → ℝ) (degree : β → ℕ)
    (weight square : σ → ℝ → ℝ → ℝ → ℝ)
    (coefficient : η → ℝ) (exponent : η → Fin 3 → ℕ)
    (h : ℝ → ℝ) (e M : ℝ)
    (hweight : ∀ u v t, TripleDomain M u v t → ∀ b, 0 ≤ weight b u v t)
    (hidentity : ∀ u v t, TripleDomain M u v t →
      (h u+h v+h t)/3-e/45 =
        (∑ b, correctedFactorKernel (B b) (p b) (degree b) u v t)+
        (∑ b, weight b u v t*(square b u v t)^2)+
        ∑ b, coefficient b*(u^(exponent b 0)*v^(exponent b 1)*t^(exponent b 2)))
    (x : Configuration) (hx : ∀ i, ‖x i‖ = 1)
    (hM : ∀ i j, i ≠ j → inner ℝ (x i) (x j) ≤ M) :
    e-45*(∑ b, |coefficient b|) ≤
      pairSum (fun i j => h (inner ℝ (x i) (x j))) := by
  let K (i j k : Fin 10) := ∑ b, correctedFactorKernel (B b) (p b) (degree b)
    (inner ℝ (x i) (x j)) (inner ℝ (x i) (x k)) (inner ℝ (x j) (x k))
  apply pairSum_from_triple_certificate _ K e (∑ b, |coefficient b|)
  · intro i j
    rw [real_inner_comm]
  · rw [show K = (fun i j k => ∑ b, correctedFactorKernel (B b) (p b) (degree b)
        (inner ℝ (x i) (x j)) (inner ℝ (x i) (x k)) (inner ℝ (x j) (x k))) from rfl,
      distinctSum_sum]
    exact Finset.sum_nonneg fun b _ => corrected_factor_distinctSum_nonneg
      (B b) (p b) (degree b) x hx
  · intro i j k hij hik hjk
    have hd := unit_gram_mem_domain x hx M hM i j k hij hik hjk
    have hid := hidentity _ _ _ hd
    have hs := weighted_squares_nonneg
      (fun b => weight b (inner ℝ (x i) (x j)) (inner ℝ (x i) (x k))
        (inner ℝ (x j) (x k)))
      (fun b => square b (inner ℝ (x i) (x j)) (inner ℝ (x i) (x k))
        (inner ℝ (x j) (x k))) (hweight _ _ _ hd)
    have hr := coefficient_sum_lower_bound coefficient
      (fun b => (inner ℝ (x i) (x j))^(exponent b 0)*
        (inner ℝ (x i) (x k))^(exponent b 1)*(inner ℝ (x j) (x k))^(exponent b 2))
      (fun b => triple_monomial_abs_le_one hd.1 hd.2.1 hd.2.2.1 _ _ _)
    dsimp only [K]
    linarith

end ThomsonN10.Cert.SDP
