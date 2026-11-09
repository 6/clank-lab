import ABC.S4.TwistConjAux4

/-! T1 helpers: changing the eigenvector, `v ↦ c v` and `v ↦ c v̄`. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real

set_option linter.unusedSimpArgs false

noncomputable section

namespace ABC.S4.TwistConjAux

open ABC

/-- the jet of `w ↦ α w` -/
def linJet (α : ℂ) : ℕ → ℕ → ℂ
  | 1, 0 => α
  | _, _ => 0

theorem jetPoly_linJet (α w : ℂ) : jetPoly (linJet α) w = α * w := by
  rw [jetPoly_eq]; simp [linJet]

theorem beta_scale {a a' : ℕ → ℕ → ℂ} {α : ℂ} (hα : α ≠ 0)
    (h : comp a' (linJet α) 0 0 = α * a 0 0 ∧ comp a' (linJet α) 1 0 = α * a 1 0 ∧
      comp a' (linJet α) 0 1 = α * a 0 1 ∧ comp a' (linJet α) 2 0 = α * a 2 0 ∧
      comp a' (linJet α) 1 1 = α * a 1 1 ∧ comp a' (linJet α) 0 2 = α * a 0 2 ∧
      comp a' (linJet α) 3 0 = α * a 3 0 ∧ comp a' (linJet α) 2 1 = α * a 2 1 ∧
      comp a' (linJet α) 1 2 = α * a 1 2 ∧ comp a' (linJet α) 0 3 = α * a 0 3) :
    birkhoffBeta a' * (α * conj α) = birkhoffBeta a := by
  obtain ⟨-, e10, -, e20, e11, e02, -, e21, -, -⟩ := h
  simp only [comp, linJet, map_zero, mul_zero, zero_mul, add_zero, zero_add] at e10 e20 e11 e02 e21
  have hα' : conj α ≠ 0 := by simpa using hα
  have h10 : a' 1 0 = a 1 0 := mul_right_cancel₀ hα (by linear_combination e10)
  have n1 : a' 2 1 * (α * conj α) = a 2 1 :=
    mul_left_cancel₀ hα (by linear_combination e21)
  have h20 : a 2 0 = a' 2 0 * α := mul_left_cancel₀ hα (by linear_combination -e20)
  have h11 : a 1 1 = a' 1 1 * conj α := mul_left_cancel₀ hα (by linear_combination -e11)
  have n2 : a' 2 0 * a' 1 1 * (α * conj α) = a 2 0 * a 1 1 := by rw [h20, h11]; ring
  have n3 : a' 1 1 * conj (a' 1 1) * (α * conj α) = a 1 1 * conj (a 1 1) := by
    rw [h11]; simp only [map_mul, Complex.conj_conj]; ring
  have ce02 := congrArg conj e02
  simp only [map_mul, map_pow, Complex.conj_conj] at ce02
  have n4 : a' 0 2 * conj (a' 0 2) * (α * conj α) = a 0 2 * conj (a 0 2) := by
    refine mul_left_cancel₀ (mul_ne_zero hα hα') ?_
    linear_combination (a' 0 2 * conj α ^ 2) * ce02 + (conj α * conj (a 0 2)) * e02
  unfold birkhoffBeta
  simp only [normsq_eq, h10]
  linear_combination n1 + (2 / (a 1 0 * conj (a 1 0) - a 1 0)
    + 1 / (a 1 0 ^ 2 - a 1 0)) * n2 + (1 / (a 1 0 * conj (a 1 0) - conj (a 1 0))) * n3
    + (2 / (a 1 0 ^ 2 - conj (a 1 0))) * n4


theorem beta_conjv {a a' : ℕ → ℕ → ℂ} {γ : ℂ} (hγ : γ ≠ 0)
    (h : comp a' (linJet γ) 0 0 = γ * conj (a 0 0) ∧ comp a' (linJet γ) 1 0 = γ * conj (a 1 0) ∧
      comp a' (linJet γ) 0 1 = γ * conj (a 0 1) ∧ comp a' (linJet γ) 2 0 = γ * conj (a 2 0) ∧
      comp a' (linJet γ) 1 1 = γ * conj (a 1 1) ∧ comp a' (linJet γ) 0 2 = γ * conj (a 0 2) ∧
      comp a' (linJet γ) 3 0 = γ * conj (a 3 0) ∧ comp a' (linJet γ) 2 1 = γ * conj (a 2 1) ∧
      comp a' (linJet γ) 1 2 = γ * conj (a 1 2) ∧ comp a' (linJet γ) 0 3 = γ * conj (a 0 3)) :
    birkhoffBeta a' * (γ * conj γ) = conj (birkhoffBeta a) := by
  obtain ⟨-, e10, -, e20, e11, e02, -, e21, -, -⟩ := h
  simp only [comp, linJet, map_zero, mul_zero, zero_mul, add_zero, zero_add] at e10 e20 e11 e02 e21
  have hγ' : conj γ ≠ 0 := by simpa using hγ
  have h10 : a' 1 0 = conj (a 1 0) := mul_right_cancel₀ hγ (by linear_combination e10)
  have n1 : a' 2 1 * (γ * conj γ) = conj (a 2 1) :=
    mul_left_cancel₀ hγ (by linear_combination e21)
  have h20 : conj (a 2 0) = a' 2 0 * γ := mul_left_cancel₀ hγ (by linear_combination -e20)
  have h11 : conj (a 1 1) = a' 1 1 * conj γ := mul_left_cancel₀ hγ (by linear_combination -e11)
  have h11' : a 1 1 = conj (a' 1 1) * γ := by
    have := congrArg conj h11; simpa only [map_mul, Complex.conj_conj] using this
  have n2 : a' 2 0 * a' 1 1 * (γ * conj γ) = conj (a 2 0) * conj (a 1 1) := by
    rw [h20, h11]; ring
  have n3 : a' 1 1 * conj (a' 1 1) * (γ * conj γ) = conj (a 1 1) * a 1 1 := by
    rw [h11, h11']; ring
  have ce02 := congrArg conj e02
  simp only [map_mul, map_pow, Complex.conj_conj] at ce02
  have n4 : a' 0 2 * conj (a' 0 2) * (γ * conj γ) = conj (a 0 2) * a 0 2 := by
    refine mul_left_cancel₀ (mul_ne_zero hγ hγ') ?_
    linear_combination (a' 0 2 * conj γ ^ 2) * ce02 + (conj γ * a 0 2) * e02
  unfold birkhoffBeta
  simp only [normsq_eq, h10, map_add, map_mul, map_div₀, map_sub, map_pow, map_ofNat,
    Complex.conj_conj]
  linear_combination n1 + (2 / (conj (a 1 0) * a 1 0 - conj (a 1 0))
    + 1 / (conj (a 1 0) ^ 2 - conj (a 1 0))) * n2
    + (1 / (conj (a 1 0) * a 1 0 - a 1 0)) * n3
    + (2 / (conj (a 1 0) ^ 2 - a 1 0)) * n4

theorem jet_smul {G : ℂ → ℂ} {a : ℕ → ℕ → ℂ} (α : ℂ)
    (hG : (fun w => G w - jetPoly a w) =o[𝓝 0] fun w => ‖w‖ ^ 3) :
    (fun w => α * G w - jetPoly (fun j k => α * a j k) w) =o[𝓝 0] fun w => ‖w‖ ^ 3 :=
  (hG.const_mul_left α).congr_left fun w => by rw [jetPoly_eq, jetPoly_eq]; ring

theorem jet_conjv {G : ℂ → ℂ} {a : ℕ → ℕ → ℂ} (γ : ℂ)
    (hG : (fun w => G w - jetPoly a w) =o[𝓝 0] fun w => ‖w‖ ^ 3) :
    (fun w => γ * conj (G (conj w)) - jetPoly (fun j k => γ * conj (a j k)) w) =o[𝓝 0]
      fun w => ‖w‖ ^ 3 := by
  have ht : Tendsto (fun w : ℂ => conj w) (𝓝 0) (𝓝 0) := by
    simpa using (Complex.continuous_conj.tendsto (0 : ℂ))
  have h1 := hG.comp_tendsto ht
  simp only [Function.comp_def, Complex.norm_conj] at h1
  have h2 : (fun w => conj (G (conj w) - jetPoly a (conj w))) =o[𝓝 0] fun w => ‖w‖ ^ 3 := by
    refine isLittleO_norm_left.1 ?_
    simpa only [Complex.norm_conj] using h1.norm_left
  refine (h2.const_mul_left γ).congr_left fun w => ?_
  rw [jetPoly_eq, jetPoly_eq]
  simp only [map_add, map_sub, map_mul, map_pow, Complex.conj_conj]
  ring

theorem jet_lin (α : ℂ) :
    (fun w => α * w - jetPoly (linJet α) w) =o[𝓝 0] fun w : ℂ => ‖w‖ ^ 3 := by
  simp only [jetPoly_linJet, sub_self]
  exact isLittleO_zero _ _


theorem indep_core {f : E 2 → E 2} {p : E 2} {v v' : C2} {a a' : ℕ → ℕ → ℂ}
    (hdet : jdet f p = 1) (hd' : TwistData f p v' a') (hβ' : birkhoffBeta a' ≠ 0)
    (hd : TwistData f p v a) : birkhoffBeta a ≠ 0 := by
  have hv := hd.indep
  have hv' := hd'.indep
  have hf : DifferentiableAt ℝ f p := by
    by_contra hnd
    have h0 := fderiv_zero_of_not_differentiableAt hnd
    rw [jdet, h0] at hdet
    simp [LinearMap.det_zero] at hdet
  have hl := jet_linear hd hf
  have hl' := jet_linear hd' hf
  set L : ℂ → ℂ := fun w => toW v' (ofW v w) with hL
  set LC : ℂ →L[ℝ] ℂ := ((ofWC v' hv').symm : E 2 →L[ℝ] ℂ).comp (ofWC v hv : ℂ →L[ℝ] E 2)
  have hLC : ∀ w, LC w = L w := fun w => rfl
  set α := (L 1 - Complex.I * L Complex.I) / 2 with hα
  set γ := (L 1 + Complex.I * L Complex.I) / 2 with hγ
  have hLform : ∀ w, L w = α * w + γ * conj w := by
    intro w
    rw [← hLC, clm_decomp, hLC, hLC, Complex.re_eq_add_conj, Complex.im_eq_sub_conj, hα, hγ]
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  -- `L` intertwines the linear parts
  have hcomm : ∀ w, L (a 1 0 * w) = a' 1 0 * L w := by
    intro w
    have e1 : ofW v (a 1 0 * w) = fderiv ℝ f p (ofW v w) := by rw [← hl w, ofW_toW hv]
    simp only [hL]
    rw [e1, ← hl' (toW v' (ofW v w)), ofW_toW hv']
  have hLinj : ∀ w, L w = 0 → w = 0 := by
    intro w hw
    have h0 : ofW v w = 0 := by
      rw [← ofW_toW hv' (ofW v w)]; simp only [hL] at hw; rw [hw, ofW_zero]
    rw [← toW_ofW hv w, h0, toW_zero]
  -- `L` conjugates the maps in coordinates
  have hrel : ∀ w, toW v' (f (p + ofW v' (L w)) - p) = L (toW v (f (p + ofW v w) - p)) := by
    intro w
    simp only [hL]
    rw [ofW_toW hv', ofW_toW hv]
  have c1 := hcomm 1
  have c2 := hcomm Complex.I
  rw [hLform, hLform] at c1 c2
  simp only [mul_one, map_one, map_mul, Complex.conj_I] at c1 c2
  have hα' : α * a 1 0 = a' 1 0 * α := by
    linear_combination (1 / 2 : ℂ) * c1 + (-Complex.I / 2) * c2
      + (α * a 1 0 - γ * conj (a 1 0) - a' 1 0 * α + a' 1 0 * γ) / 2 * Complex.I_sq
  have hγ' : γ * conj (a 1 0) = a' 1 0 * γ := by
    linear_combination (1 / 2 : ℂ) * c1 + (Complex.I / 2) * c2
      - (α * a 1 0 - γ * conj (a 1 0) - a' 1 0 * α + a' 1 0 * γ) / 2 * Complex.I_sq
  by_cases hγ0 : γ = 0
  · -- `v' = c v`
    have hα0 : α ≠ 0 := by
      intro h0
      exact one_ne_zero (hLinj 1 (by rw [hLform]; simp [h0, hγ0]))
    have hr : ∀ w, toW v' (f (p + ofW v' (α * w)) - p) = α * toW v (f (p + ofW v w) - p) := by
      intro w
      have := hrel w
      rw [hLform, hLform, hγ0] at this
      simpa using this
    have j1 := comp_jet (F := fun w => α * w) (G := fun z => toW v' (f (p + ofW v' z) - p))
      (p := linJet α) (q := a') (by simp [linJet]) (by simp [linJet]) (jet_lin α) hd'.jet
    have j2 := jet_smul α hd.jet
    have E := jet_eq (Eventually.of_forall hr) j1 j2
    have hb := beta_scale hα0 E
    intro h0
    rw [h0] at hb
    exact hβ' ((mul_eq_zero.1 hb).resolve_right (mul_ne_zero hα0 (by simpa using hα0)))
  · by_cases hα0 : α = 0
    · -- `v' = c v̄`
      have hr : ∀ u, toW v' (f (p + ofW v' (γ * u)) - p) =
          γ * conj (toW v (f (p + ofW v (conj u)) - p)) := by
        intro u
        have := hrel (conj u)
        rw [hLform, hLform, hα0] at this
        simpa using this
      have j1 := comp_jet (F := fun w => γ * w) (G := fun z => toW v' (f (p + ofW v' z) - p))
        (p := linJet γ) (q := a') (by simp [linJet]) (by simp [linJet]) (jet_lin γ) hd'.jet
      have j2 := jet_conjv γ hd.jet
      have E := jet_eq (Eventually.of_forall hr) j1 j2
      have hb := beta_conjv hγ0 E
      intro h0
      rw [h0, map_zero] at hb
      exact hβ' ((mul_eq_zero.1 hb).resolve_right (mul_ne_zero hγ0 (by simpa using hγ0)))
    · exfalso
      have e1 : a' 1 0 = a 1 0 := mul_left_cancel₀ hα0 (by linear_combination -hα')
      have e2 : a' 1 0 = conj (a 1 0) := mul_left_cancel₀ hγ0 (by linear_combination -hγ')
      apply hd.nonreal
      exact Complex.conj_eq_iff_im.1 (e2.symm.trans e1)

end ABC.S4.TwistConjAux
