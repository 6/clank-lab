import ABC.S4.R2Aux8

/-! R2 helpers: solutions of `H₂` map to solutions of `H₁` under `w ↦ Q(t) w`. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)
open scoped ContDiff NNReal Matrix

noncomputable section

namespace ABC.S4.R2Aux

open ABC ABC.S4

section T

variable {H₁ : C2 → ℂ → ℂ} {ρ s s₀ ν Kq : ℝ} {Q : ℂ → Matrix (Fin 2) (Fin 2) ℂ}

theorem H2_diffAt (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ) (hq : QData H₁ s s₀ ν Kq Q) {w : C2}
    (hw : ‖w‖ < 2 * rad ρ Kq) {t : ℂ} (ht : |t.im| < 3 * s₀ / 4) :
    DifferentiableAt ℂ (fun w => H2 H₁ Q ν w t) w := by
  have hr : DifferentiableAt ℂ (fun q : C2 × ℂ => remH H₁ Q q.1 q.2) (w, t) :=
    (remH_holo hH hρ hq).differentiableAt ((isOpen_Wset ρ Kq s₀).mem_nhds ⟨hw, ht⟩)
  have hr' : DifferentiableAt ℂ (fun w => remH H₁ Q w t) w := by
    have hpair : DifferentiableAt ℂ (fun w : C2 => (w, t)) w :=
      (hasFDerivAt_prodMk_left w t).differentiableAt
    have := hr.comp w hpair
    exact this
  have hp : DifferentiableAt ℂ (fun w : C2 => (ν : ℂ) / 2 * (w 0 ^ 2 + w 1 ^ 2)) w := by fun_prop
  exact hp.add hr'

/-- `∂ₖ H₂ = ν wₖ + ∂H₁(u)(Q eₖ) − Σ Aᵢⱼ uᵢ (Q eₖ)ⱼ`, `u = Q w`. -/
theorem H2_partial (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ) (hq : QData H₁ s s₀ ν Kq Q) {w : C2}
    (hw : ‖w‖ < 2 * rad ρ Kq) {t : ℂ} (ht : |t.im| < 3 * s₀ / 4) (k : Fin 2) :
    fderiv ℂ (fun w => H2 H₁ Q ν w t) w (eC k) =
      ν * w k + fderiv ℂ (H₁ · t) (Q t *ᵥ w) (Q t *ᵥ eC k) -
        ∑ i, ∑ j, Amat H₁ t i j * (Q t *ᵥ w) i * (Q t *ᵥ eC k) j := by
  have hts : t ∈ strip s := by show |t.im| < s; linarith [hq.s₀le, hq.s₀pos]
  set e := eC k with he_def
  set u := Q t *ᵥ w
  set v := Q t *ᵥ e
  have hline := HoloDeriv.hasDerivAt_line (H2_diffAt hH hρ hq hw ht) e
  have hG : DifferentiableAt ℂ (H₁ · t) u :=
    diffAt_slice hH (mk_mem_prod (mulVec_mem hρ hq hw ht.le) hts)
  have hb := HoloDeriv.hasDerivAt_line hG v
  have hexp : (fun z : ℂ => H2 H₁ Q ν (w + z • e) t) = fun z =>
      ν / 2 * ((w 0 + z * e 0) ^ 2 + (w 1 + z * e 1) ^ 2) + (H₁ (u + z • v) t -
        (∑ i, ∑ j, Amat H₁ t i j * (u i + z * v i) * (u j + z * v j)) / 2) := by
    funext z
    simp only [H2, remH, qf, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, u, v]
  have hl : ∀ (a c : ℂ), HasDerivAt (fun z : ℂ => a + z * c) c 0 := fun a c => by
    simpa using ((hasDerivAt_id' (0 : ℂ)).mul_const c).const_add a
  have ha : HasDerivAt (fun z : ℂ => ν / 2 * ((w 0 + z * e 0) ^ 2 + (w 1 + z * e 1) ^ 2))
      (ν / 2 * (2 * w 0 * e 0 + 2 * w 1 * e 1)) 0 := by
    have := (((hl (w 0) (e 0)).pow 2).add ((hl (w 1) (e 1)).pow 2)).const_mul ((ν : ℂ) / 2)
    convert this using 1; simp
  have hc : HasDerivAt (fun z : ℂ => ∑ i, ∑ j, Amat H₁ t i j * (u i + z * v i) * (u j + z * v j))
      (∑ i, ∑ j, Amat H₁ t i j * (v i * u j + u i * v j)) 0 := by
    refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
    have := ((hl (u i) (v i)).const_mul (Amat H₁ t i j)).mul (hl (u j) (v j))
    convert this using 1; first | (simp; done) | (simp; ring)
  have hall : HasDerivAt (fun z : ℂ => H2 H₁ Q ν (w + z • e) t)
      (ν / 2 * (2 * w 0 * e 0 + 2 * w 1 * e 1) + (fderiv ℂ (H₁ · t) u v -
        (∑ i, ∑ j, Amat H₁ t i j * (v i * u j + u i * v j)) / 2)) 0 := by
    rw [hexp]; exact ha.add (hb.sub (hc.div_const 2))
  rw [hline.unique hall]
  have hsym := Amat_symm hH hρ hts 1 0
  have he : ν / 2 * (2 * w 0 * e 0 + 2 * w 1 * e 1) = ν * w k := by
    fin_cases k <;> simp [e, eC] <;> ring
  rw [he]
  simp only [Fin.sum_univ_two]
  rw [hsym]
  ring

theorem solves_transfer (hH : IsTPHam H₁ ρ s) (hρ : 0 < ρ) (hq : QData H₁ s s₀ ν Kq Q)
    {γ : ℝ → C2} {a b : ℝ} (hγ : Solves (H2 H₁ Q ν) γ a b)
    (hmem : ∀ t ∈ Icc a b, γ t ∈ polydisc (rad ρ Kq)) :
    Solves H₁ (fun t => Q t *ᵥ γ t) a b := by
  intro t ht
  have hρ₁ : 0 < rad ρ Kq := rad_pos hρ hq.Kq0
  have hs₀ := hq.s₀pos
  have hw : ‖γ t‖ < 2 * rad ρ Kq := by have := hmem t ht; show ‖γ t‖ < _; linarith [show ‖γ t‖ < rad ρ Kq from this]
  have htim : |((t : ℂ)).im| < 3 * s₀ / 4 := by simp; positivity
  have hts : (t : ℂ) ∈ strip s := by show |((t : ℂ)).im| < s; simp; linarith [hq.s₀le]
  have hγt := hγ t ht
  have hQd : ∀ i j, HasDerivAt (fun t : ℝ => Q t i j)
      ((Bm H₁ t * Q t - (ν : ℂ) • (Q t * Jm)) i j) t := fun i j =>
    hasDerivAt_ofReal_comp (hq.ode t (by simp [hs₀]) i j)
  -- derivative of `Q(t) γ(t)`
  have hD : HasDerivWithinAt (fun t : ℝ => Q t *ᵥ γ t)
      (fun i => ∑ k, ((Bm H₁ t * Q t - (ν : ℂ) • (Q t * Jm)) i k * γ t k +
        Q t i k * hamVF (fun w => H2 H₁ Q ν w t) (γ t) k)) (Icc a b) t := by
    refine hasDerivWithinAt_pi.2 fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    exact HasDerivWithinAt.fun_sum fun k _ =>
      (hQd i k).hasDerivWithinAt.mul (hasDerivWithinAt_pi.1 hγt k)
  refine hD.congr_deriv ?_
  -- the algebra
  set u := Q t *ᵥ γ t with hu
  have hp := fun k => H2_partial hH hρ hq hw htim k (ν := ν)
  have hdet : Q t 0 0 * Q t 1 1 - Q t 0 1 * Q t 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact hq.det t
  have hsym := Amat_symm hH hρ hts 1 0
  set G : C2 → ℂ := (H₁ · (t : ℂ))
  have hlin : ∀ y : C2, fderiv ℂ G u y = y 0 * fderiv ℂ G u (eC 0) + y 1 * fderiv ℂ G u (eC 1) := by
    intro y
    conv_lhs => rw [eC_sum y]
    simp [map_add, map_smul]
  have hQe : ∀ k, Q t *ᵥ eC k = fun j => Q t j k := by
    intro k; funext j; fin_cases k <;> simp [Matrix.mulVec, dotProduct, eC, Fin.sum_univ_two]
  have e0 := hp 0
  have e1 := hp 1
  rw [hQe, hlin (fun j => Q t j 0)] at e0
  rw [hQe, hlin (fun j => Q t j 1)] at e1
  have hv1 : hamVF (fun w => H2 H₁ Q ν w t) (γ t) =
      ![fderiv ℂ (fun w => H2 H₁ Q ν w t) (γ t) (eC 1),
        -fderiv ℂ (fun w => H2 H₁ Q ν w t) (γ t) (eC 0)] := rfl
  have hv2 : hamVF G u = ![fderiv ℂ G u (eC 1), -fderiv ℂ G u (eC 0)] := rfl
  rw [hv1, hv2, e0, e1]
  set g0 := fderiv ℂ G u (eC 0)
  set g1 := fderiv ℂ G u (eC 1)
  funext i
  fin_cases i
  · simp [Fin.sum_univ_two, hu, Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.mul_apply, Bm, Jm, hsym, Matrix.vecMul]
    linear_combination (g1 - (Amat H₁ t 0 1 * (Q t 0 0 * γ t 0 + Q t 0 1 * γ t 1) +
      Amat H₁ t 1 1 * (Q t 1 0 * γ t 0 + Q t 1 1 * γ t 1))) * hdet
  · simp [Fin.sum_univ_two, hu, Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.mul_apply, Bm, Jm, hsym, Matrix.vecMul]
    linear_combination (-(g0 - (Amat H₁ t 0 0 * (Q t 0 0 * γ t 0 + Q t 0 1 * γ t 1) +
      Amat H₁ t 0 1 * (Q t 1 0 * γ t 0 + Q t 1 1 * γ t 1)))) * hdet

end T

end ABC.S4.R2Aux
