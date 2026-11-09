import ABC.S4.PeriodMapAux1
import ABC.Twist

/-! Uniqueness: a solution that starts on a flow line of a holomorphic field stays on it. -/

open Set Metric Filter Topology

noncomputable section

namespace ABC.S4.PeriodMapAux

open ABC

lemma solution_eq_flow {n : ℕ} {F : Cn n → Cn n} {D : Set (Cn n)} (hD : IsOpen D)
    (hF : DifferentiableOn ℂ F D) {Γ Φ : ℝ → Cn n} {T : ℝ}
    (hΓc : ContinuousOn Γ (Icc 0 T))
    (hΓd : ∀ t ∈ Ico 0 T, Γ t ∈ D → HasDerivWithinAt Γ (F (Γ t)) (Ici t) t)
    (hΦc : ContinuousOn Φ (Icc 0 T))
    (hΦd : ∀ t ∈ Ico 0 T, HasDerivWithinAt Φ (F (Φ t)) (Ici t) t)
    (hΦD : ∀ t ∈ Icc 0 T, Φ t ∈ D) (h0 : Γ 0 = Φ 0) : ∀ t ∈ Icc 0 T, Γ t = Φ t := by
  set S := {t : ℝ | Γ t = Φ t}
  have hcl : IsClosed (S ∩ Icc 0 T) := by
    have := (hΓc.prodMk hΦc).preimage_isClosed_of_isClosed isClosed_Icc isClosed_diagonal
    convert this using 1
    ext t; simp [S, and_comm]
  refine fun t ht => hcl.Icc_subset_of_forall_mem_nhdsWithin h0 (fun t₀ ht₀ => ?_) ht
  obtain ⟨hS, ht₀⟩ := ht₀
  have ht₀' : t₀ ∈ Icc 0 T := Ico_subset_Icc_self ht₀
  set p₀ := Φ t₀
  have hp₀ : p₀ ∈ D := hΦD t₀ ht₀'
  obtain ⟨K, N, hN, hLip⟩ := ((analyticAt_of_differentiableOn hD hF hp₀).contDiffAt
    (n := 1)).exists_lipschitzOnWith
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem hN (hD.mem_nhds hp₀))
  have hA : {t | Γ t ∈ ball p₀ δ ∧ Φ t ∈ ball p₀ δ} ∈ 𝓝[Icc 0 T] t₀ := by
    have h1 := (hΓc t₀ ht₀').preimage_mem_nhdsWithin (isOpen_ball.mem_nhds
      (by rw [hS]; exact mem_ball_self hδ))
    have h2 := (hΦc t₀ ht₀').preimage_mem_nhdsWithin (isOpen_ball.mem_nhds (mem_ball_self hδ))
    filter_upwards [h1, h2] with t h1 h2 using ⟨h1, h2⟩
  obtain ⟨ε, hε, hεA⟩ := Metric.mem_nhdsWithin_iff.1 hA
  set b := min (t₀ + ε / 2) T
  have htb : t₀ < b := lt_min (by linarith) ht₀.2
  have hsub : Icc t₀ b ⊆ Icc 0 T := Icc_subset_Icc ht₀.1 (min_le_right _ _)
  have hin : ∀ t ∈ Icc t₀ b, Γ t ∈ ball p₀ δ ∧ Φ t ∈ ball p₀ δ := by
    intro t ht
    refine hεA ⟨?_, hsub ht⟩
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2, min_le_left (t₀ + ε / 2) T]
  have hIco : ∀ t ∈ Ico t₀ b, t ∈ Ico 0 T := fun t ht =>
    ⟨ht₀.1.trans ht.1, ht.2.trans_le (min_le_right _ _)⟩
  have heq := ODE_solution_unique_of_mem_Icc_right (v := fun _ => F) (s := fun _ => ball p₀ δ)
    (K := K) (fun _ _ => hLip.mono fun q hq => (hball hq).1) (hΓc.mono hsub)
    (fun t ht => hΓd t (hIco t ht) (hball (hin t (Ico_subset_Icc_self ht)).1).2)
    (fun t ht => (hin t (Ico_subset_Icc_self ht)).1) (hΦc.mono hsub)
    (fun t ht => hΦd t (hIco t ht)) (fun t ht => (hin t (Ico_subset_Icc_self ht)).2) hS
  filter_upwards [Ioo_mem_nhdsGT htb] with t ht
  exact heq (Ioo_subset_Icc_self ht)

end ABC.S4.PeriodMapAux
