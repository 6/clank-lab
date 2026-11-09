import ABC.Hand
import ABC.ODE
import ABC.LemmaW
import ABC.TubeProofAux4

/-!
# The vortex tube from the certificate and the KAM input

`p` is the certified fixed point. Near `p` the orbits cross the planes `z ∈ 2πℤ`
transversally (`V_z ≥ 1.9` for `|t| ≤ 4`, by Gronwall from `V_z ≥ 1.92` on the periodic orbit
of `p`), so `retMap` and its inverse `Pinv` are continuous and mutually inverse near `p`
(`TubeProofAux2`). The KAM curves (the hypothesis `KAMInput`) inside `ball p δ₀` and Lemma W give an invariant Lipschitz
`w`. The tube function `W = Wf w` takes, at `ξ`, the value of `w` at the point where the orbit
through `ξ` crosses `z = 0` (up to the lattice), and `0` off the tube (`TubeProofAux3`).
-/

open Set Metric

namespace ABC

theorem vortex_tube_exists (hKAM : KAMInput) : ∃ W, VortexTube W := by
  obtain ⟨p, hp⟩ := Cert.fixed_point
  obtain ⟨h, ρ, L, K, g, hρ, hL, hsrc, hh0, hbil, hR, hK, hKpos, hg, hlab, hinvK⟩ :=
    hKAM p hp δ₀ δ₀_pos
  have hRδ : h '' closedBall 0 ρ ⊆ closedBall p δ₀ := hR.trans ball_subset_closedBall
  have hRN : h '' closedBall 0 ρ ⊆ closedBall p r₀ :=
    hRδ.trans (closedBall_subset_closedBall δ₀_le)
  have hP : ContinuousOn retMap (h '' closedBall 0 ρ) :=
    ((crossP_continuousOn hp mem_Icc_two_pi).mono hRN).congr
      fun a ha => retMap_eq_crossP hp (hRN ha)
  have hPinv : ContinuousOn Pinv (h '' closedBall 0 ρ) :=
    (crossP_continuousOn hp mem_Icc_neg_two_pi).mono hRN
  obtain ⟨w, ⟨C, hwL⟩, hw0, hwp, hwsupp, hwP, hwPinv⟩ :=
    lemmaW hρ hL hsrc hbil hK hKpos hg hlab hP hPinv
      (fun a ha => retMap_Pinv hp (hRN ha))
      (fun a ha => Pinv_retMap hp (hRN ha) (retMap_mem hp (hRδ ha))) hinvK
      (by rw [hh0, retMap_eq_crossP hp (mem_closedBall_self r₀_pos.le), crossP_p_pos hp])
  have hsuppR : ∀ a, w a ≠ 0 → a ∈ h '' closedBall 0 ρ := fun a ha =>
    image_mono ball_subset_closedBall (hwsupp a ha)
  have hsupp : ∀ a, w a ≠ 0 → a ∈ ball p δ₀ := fun a ha => hR (hsuppR a ha)
  have hinv : ∀ a, w a ≠ 0 → w (retMap a) = w a ∧ w (Pinv a) = w a := fun a ha =>
    ⟨hwP a (hsuppR a ha), hwPinv a (hsuppR a ha)⟩
  refine ⟨Wf w, Wf_lipschitz hp le_rfl hsupp hinv hw0 hwL, Wf_periodic w,
    Wf_nonneg hp le_rfl hsupp hinv hw0, ⟨lift p 0, ?_⟩,
    ae_inner_gradient_eq_zero (Wf_lipschitz hp le_rfl hsupp hinv hw0 hwL).choose_spec
      (Wf_Γ w),
    ⟨19 / 10, by norm_num, fun x hx => Wf_Vz hp le_rfl hsupp hinv hw0 hx⟩,
    -Real.pi, -(Real.pi / 2), 1, one_pos, fun x hx => ?_⟩
  · rw [Wf_lift_p hp le_rfl hsupp hinv hw0, ← hh0]
    exact hwp
  · obtain ⟨m, k, hm, hk⟩ := box_of_Vz (Wf_Vz hp le_rfl hsupp hinv hw0 hx)
    exact ⟨m, k, hm, hk⟩

end ABC
