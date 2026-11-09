import ABC.S4.R7TimeRow
import ABC.S4.R123
import ABC.S4.R5

/-! Helpers for `R7_invariant`: the clockwise polar chart along a torus orbit. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)

noncomputable section

namespace ABC.S4.R7InvariantAux

open ABC ABC.S4 ABC.S4.PeriodMapAux
open ABC.Poschel2001 (XH Tstar imPart twoPiE)

-- `(2P)^{1/2}` and its `P`-derivative
def sqP (P : ℂ) : ℂ := (2 * P) ^ (1 / 2 : ℂ)

def sqP' (P : ℂ) : ℂ := 1 / 2 * (2 * P) ^ ((1 / 2 : ℂ) - 1) * 2

-- `∂_P polarW` and `∂_θ polarW`
def dP (P a : ℂ) : C2 := ![sqP' P * Complex.cos a, -(sqP' P * Complex.sin a)]

def dA (P a : ℂ) : C2 := ![-(sqP P * Complex.sin a), -(sqP P * Complex.cos a)]

lemma sq_mul_sq' {P : ℂ} (hP : P ≠ 0) : sqP P * sqP' P = 1 := by
  have h2 : (2 * P) ≠ 0 := mul_ne_zero two_ne_zero hP
  have h := (Complex.cpow_add (1 / 2 : ℂ) ((1 / 2 : ℂ) - 1) h2).symm
  have h0 : (1 / 2 : ℂ) + ((1 / 2 : ℂ) - 1) = 0 := by ring
  rw [h0, Complex.cpow_zero] at h
  unfold sqP sqP'
  linear_combination h

lemma hasDerivAt_sq {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    {P : 𝕜 → ℂ} {P' : ℂ} {t : 𝕜} (hP : HasDerivAt P P' t) (hs : 2 * P t ∈ Complex.slitPlane) :
    HasDerivAt (fun t => sqP (P t)) (sqP' (P t) * P') t := by
  have h1 : HasDerivAt (fun z : ℂ => (2 * z) ^ (1 / 2 : ℂ)) (sqP' (P t)) (P t) := by
    have := ((hasDerivAt_id (P t)).const_mul (2 : ℂ)).cpow_const (c := (1 / 2 : ℂ))
      (by simpa using hs)
    simpa [sqP'] using this
  exact h1.comp t hP

lemma hasDerivAt_polarW {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    {P A : 𝕜 → ℂ} {P' A' : ℂ} {t : 𝕜} (hP : HasDerivAt P P' t) (hA : HasDerivAt A A' t)
    (hs : 2 * P t ∈ Complex.slitPlane) :
    HasDerivAt (fun t => polarW (P t) (A t)) (P' • dP (P t) (A t) + A' • dA (P t) (A t)) t := by
  have hS := hasDerivAt_sq hP hs
  have hc : HasDerivAt (fun t => Complex.cos (A t)) (-Complex.sin (A t) * A') t :=
    (Complex.hasDerivAt_cos (A t)).comp t hA
  have hsn : HasDerivAt (fun t => Complex.sin (A t)) (Complex.cos (A t) * A') t :=
    (Complex.hasDerivAt_sin (A t)).comp t hA
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · show HasDerivAt (fun x => sqP (P x) * Complex.cos (A x)) _ t
    refine (hS.mul hc).congr_deriv ?_
    simp [dP, dA]; ring
  · show HasDerivAt (fun x => -(sqP (P x) * Complex.sin (A x))) _ t
    refine (hS.mul hsn).neg.congr_deriv ?_
    simp [dP, dA]; ring

lemma clm_apply_C2 (L : C2 →L[ℂ] ℂ) (v : C2) :
    L v = v 0 * L (Pi.single 0 1) + v 1 * L (Pi.single 1 1) := by
  have hv : v = v 0 • (Pi.single 0 1 : C2) + v 1 • (Pi.single 1 1 : C2) := by
    funext i; fin_cases i <;> simp
  conv_lhs => rw [hv]
  simp [map_add, map_smul, smul_eq_mul]

-- the chain rule through the clockwise chart gives `J∇K`
lemma field_eq (L : C2 →L[ℂ] ℂ) {P a : ℂ} (hP : P ≠ 0) :
    (-L (dA P a)) • dP P a + L (dP P a) • dA P a = ![L (Pi.single 1 1), -L (Pi.single 0 1)] := by
  have h1 := sq_mul_sq' hP
  have h2 := Complex.sin_sq_add_cos_sq a
  rw [clm_apply_C2 L (dA P a), clm_apply_C2 L (dP P a)]
  funext i
  fin_cases i
  · simp [dP, dA]
    linear_combination (L (Pi.single 1 1) * (Complex.cos a ^ 2 + Complex.sin a ^ 2)) * h1 +
      L (Pi.single 1 1) * h2
  · simp [dP, dA]
    linear_combination (-L (Pi.single 0 1) * (Complex.cos a ^ 2 + Complex.sin a ^ 2)) * h1 -
      L (Pi.single 0 1) * h2

lemma fderiv_single_eq {f : C2 → ℂ} {x : C2} (hf : DifferentiableAt ℂ f x) (j : Fin 2) {d : ℂ}
    (hl : HasDerivAt (fun z : ℂ => f (x + z • (Pi.single j 1 : C2))) d 0) :
    fderiv ℂ f x (Pi.single j 1) = d := by
  have h1 : HasDerivAt (fun z : ℂ => x + z • (Pi.single j 1 : C2)) (Pi.single j 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (Pi.single j 1 : C2)).const_add x
  have h2 : HasFDerivAt f (fderiv ℂ f x) (x + (0 : ℂ) • (Pi.single j 1 : C2)) := by
    simpa using hf.hasFDerivAt
  exact (h2.comp_hasDerivAt (0 : ℂ) h1).unique hl

-- `K′` as a function on `ℂ² × ℂ`
def Kq (ν b : ℝ) (R : C2 → ℂ → ℂ) (q : C2 × ℂ) : ℂ := Kbnf ν b R q.1 q.2

lemma differentiableAt_polarW_const {P : ℂ} {A : C2} :
    DifferentiableAt ℂ (fun θ' : C2 => polarW P (θ' 0)) A := by
  refine differentiableAt_pi.2 fun i => ?_
  fin_cases i
  · show DifferentiableAt ℂ (fun θ' : C2 => sqP P * Complex.cos (θ' 0)) A
    fun_prop
  · show DifferentiableAt ℂ (fun θ' : C2 => -(sqP P * Complex.sin (θ' 0))) A
    fun_prop

lemma differentiableAt_polarW_act {c a : ℂ} {I : C2} (hs : 2 * (c + I 0) ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (fun I' : C2 => polarW (c + I' 0) a) I := by
  have h : DifferentiableAt ℂ (fun I' : C2 => sqP (c + I' 0)) I := by
    have h0 : DifferentiableAt ℂ (fun I' : C2 => 2 * (c + I' 0)) I := by fun_prop
    exact h0.cpow_const hs
  refine differentiableAt_pi.2 fun i => ?_
  fin_cases i
  · show DifferentiableAt ℂ (fun I' : C2 => sqP (c + I' 0) * Complex.cos a) I
    exact h.mul_const _
  · show DifferentiableAt ℂ (fun I' : C2 => -(sqP (c + I' 0) * Complex.sin a)) I
    exact (h.mul_const _).neg

lemma partial_A {ν b : ℝ} (hb : b ≠ 0) {R : C2 → ℂ → ℂ} {W : C2} (hW : W 1 = 1) {I A : C2}
    {D : C2 × ℂ →L[ℂ] ℂ} (hs : 2 * (p0 ν b W + I 0) ∈ Complex.slitPlane)
    (hK : HasFDerivAt (Kq ν b R) D (polarW (p0 ν b W + I 0) (A 0), A 1)) :
    fderiv ℂ (fun θ' => ham (eNP ν b) (pertP ν b R) (I, θ', W)) A (Pi.single 0 1) =
      D (dA (p0 ν b W + I 0) (A 0), 0) := by
  set P := p0 ν b W + I 0 with hPdef
  have hfun : (fun θ' => ham (eNP ν b) (pertP ν b R) (I, θ', W)) =
      fun θ' => I 1 + Kq ν b R (polarW P (θ' 0), θ' 1) := by
    funext θ'
    rw [R5_identity ν b hb R _ (by simp [hW])]
    simp [hW, Kq, P]
  rw [hfun]
  apply fderiv_single_eq
  · exact (hK.differentiableAt.comp A
      (differentiableAt_polarW_const.prodMk (differentiableAt_apply 1 A))).const_add _
  · have hline : HasDerivAt (fun z : ℂ => (polarW P (A 0 + z), A 1))
        ((dA P (A 0), 0) : C2 × ℂ) 0 := by
      have h := hasDerivAt_polarW (hasDerivAt_const (0 : ℂ) P)
        ((hasDerivAt_id' (0 : ℂ)).const_add (A 0)) hs
      simp only [add_zero, zero_smul, one_smul, zero_add] at h
      exact h.prodMk (hasDerivAt_const (0 : ℂ) (A 1))
    have hc := (hK.comp_hasDerivAt_of_eq (0 : ℂ) hline (by simp)).const_add (I 1)
    convert hc using 1
    funext z
    simp

lemma partial_I {ν b : ℝ} (hb : b ≠ 0) {R : C2 → ℂ → ℂ} {W : C2} (hW : W 1 = 1) {I A : C2}
    {D : C2 × ℂ →L[ℂ] ℂ} (hs : 2 * (p0 ν b W + I 0) ∈ Complex.slitPlane)
    (hK : HasFDerivAt (Kq ν b R) D (polarW (p0 ν b W + I 0) (A 0), A 1)) :
    fderiv ℂ (fun I' => ham (eNP ν b) (pertP ν b R) (I', A, W)) I (Pi.single 0 1) =
      D (dP (p0 ν b W + I 0) (A 0), 0) := by
  set P := p0 ν b W + I 0 with hPdef
  have hfun : (fun I' => ham (eNP ν b) (pertP ν b R) (I', A, W)) =
      fun I' => I' 1 + Kq ν b R (polarW (p0 ν b W + I' 0) (A 0), A 1) := by
    funext I'
    rw [R5_identity ν b hb R _ (by simp [hW])]
    simp [hW, Kq]
  rw [hfun]
  apply fderiv_single_eq
  · have hd : DifferentiableAt ℂ (fun I' : C2 => Kq ν b R (polarW (p0 ν b W + I' 0) (A 0), A 1)) I :=
      have hinner : DifferentiableAt ℂ
          (fun I' : C2 => ((polarW (p0 ν b W + I' 0) (A 0), A 1) : C2 × ℂ)) I :=
        (differentiableAt_polarW_act hs).prodMk (differentiableAt_const _)
      hK.differentiableAt.comp (g := Kq ν b R) I hinner
    exact (differentiableAt_apply 1 I).add hd
  · have hline : HasDerivAt (fun z : ℂ => (polarW (P + z) (A 0), A 1))
        ((dP P (A 0), 0) : C2 × ℂ) 0 := by
      have h := hasDerivAt_polarW ((hasDerivAt_id' (0 : ℂ)).const_add P)
        (hasDerivAt_const (0 : ℂ) (A 0)) (by simpa using hs)
      simp only [add_zero, zero_smul, one_smul] at h
      exact h.prodMk (hasDerivAt_const (0 : ℂ) (A 1))
    have hc := (hK.comp_hasDerivAt_of_eq (0 : ℂ) hline (by simp)).const_add (I 1)
    convert hc using 1
    funext z
    simp [P, add_assoc]

lemma hasDerivAt_fst_apply {Z : ℝ → Ph 2} {Z' : Ph 2} {t : ℝ} (h : HasDerivAt Z Z' t) (j : Fin 2) :
    HasDerivAt (fun t => (Z t).1 j) (Z'.1 j) t :=
  hasDerivAt_pi.1 (((ContinuousLinearMap.fst ℝ C2 C2).hasFDerivAt).comp_hasDerivAt t h) j

lemma hasDerivAt_snd_apply {Z : ℝ → Ph 2} {Z' : Ph 2} {t : ℝ} (h : HasDerivAt Z Z' t) (j : Fin 2) :
    HasDerivAt (fun t => (Z t).2 j) (Z'.2 j) t :=
  hasDerivAt_pi.1 (((ContinuousLinearMap.snd ℝ C2 C2).hasFDerivAt).comp_hasDerivAt t h) j

-- a real point of the chart, inside the ball of radius `ρ`
lemma polarW_real {Pr ar ρ : ℝ} (hP : 0 < Pr) (hρ0 : 0 < ρ) (h2 : 2 * Pr < ρ ^ 2) :
    ∃ x : E 2, ofR x = polarW (Pr : ℂ) (ar : ℂ) ∧ ‖x‖ < ρ := by
  have hy2 : √(2 * Pr) ^ 2 = 2 * Pr := Real.sq_sqrt (by positivity)
  have hc : (2 * (Pr : ℂ)) ^ (1 / 2 : ℂ) = ((√(2 * Pr) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast; ring_nf
  generalize √(2 * Pr) = y at hy2 hc
  refine ⟨!₂[y * Real.cos ar, -(y * Real.sin ar)], ?_, ?_⟩
  · funext i
    fin_cases i <;> simp only [polarW, hc] <;> simp [ofR]
  · rw [EuclideanSpace.norm_eq, Real.sqrt_lt' hρ0]
    simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
    simp
    nlinarith [Real.sin_sq_add_cos_sq ar]

lemma isOpen_Tstar (s : ℝ) : IsOpen (Tstar (n := 2) s) := by
  have hc : Continuous (fun θ : C2 => imPart θ) :=
    continuous_pi fun i => Complex.continuous_im.comp (continuous_apply i)
  exact isOpen_lt (continuous_norm.comp hc) continuous_const

lemma ofRe_mem_Tstar {s : ℝ} (hs : 0 < s) (θ : Fin 2 → ℝ) : ofRe θ ∈ Tstar (n := 2) s := by
  have h : imPart (ofRe θ) = 0 := by funext i; simp [imPart, ofRe]
  show ‖imPart (ofRe θ)‖ < s / 2
  rw [h, norm_zero]; linarith

theorem main {p : E 2} {ν b ρ s C ε α r h δ c : ℝ} {R : C2 → ℂ → ℂ}
    {h₀ : OpenPartialHomeomorph (E 2) (E 2)} {P' : E 2 → E 2} (hB : BNF p ν b R ρ s C h₀ P')
    (hb : b ≠ 0) (hα : 0 < α) (hr : r ≤ ε / 2) (hρ : 2 * (ε + r) ≤ ρ ^ 2)
    {φ : (Fin 2 → ℝ) → (Fin 2 → ℝ)} {Φ : C2 → (Fin 2 → ℝ) → Ph 2}
    (hA : Conclusion 2 c (OmegaE ν b ε) α r s h δ (eNP ν b) (pertP ν b R) φ Φ)
    (σ : ℝ) (hσ : ![σ, 1] ∈ OmegaAlpha 2 (OmegaE ν b ε) α) (u : ℝ)
    (hu : ∀ θ : Fin 2 → ℝ, (Φ (ofRe θ) ![σ, 1]).2 1 = θ 1 + u) (θ₀ : ℝ) :
    ∃ x : E 2,
      ofR x = polarW (p0 ν b (ofRe (φ ![σ, 1])) + (Φ (ofRe ![θ₀, -u]) ![σ, 1]).1 0)
        ((Φ (ofRe ![θ₀, -u]) ![σ, 1]).2 0) ∧
      ofR (P' x) =
        polarW (p0 ν b (ofRe (φ ![σ, 1])) + (Φ (ofRe ![θ₀ + 2 * π * σ, -u]) ![σ, 1]).1 0)
          ((Φ (ofRe ![θ₀ + 2 * π * σ, -u]) ![σ, 1]).2 0) := by
  obtain ⟨hρ0, hs0, -⟩ := hB.pos
  have hH := hB.ham
  set ω : Fin 2 → ℝ := ![σ, 1] with hωdef
  set W : C2 := ofRe (φ ω) with hWdef
  have hW1 : W 1 = 1 := by
    have := (R7_time_row hα hA ω hσ).1
    simp [W, ofRe, this, ω]
  -- the shifted frequency fixes the base action `P₀ ∈ (ε/2, ε)`
  obtain ⟨P₀, hP₀, hP₀eq⟩ := (hA.mapsTo ω hσ).2
  have hbc : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb
  have hp0 : p0 ν b W = (P₀ : ℂ) := by
    simp only [p0, W, ofRe]
    rw [← Complex.ofReal_div, hP₀eq]
    push_cast
    field_simp
    ring
  -- every point of the torus slice is a real point of the ball, with positive action
  have hpt : ∀ θ : Fin 2 → ℝ, ∃ x : E 2,
      ofR x = polarW (p0 ν b W + (Φ (ofRe θ) ω).1 0) ((Φ (ofRe θ) ω).2 0) ∧ ‖x‖ < ρ ∧
      2 * (p0 ν b W + (Φ (ofRe θ) ω).1 0) ∈ Complex.slitPlane := by
    intro θ
    obtain ⟨a', b', hab, ha'⟩ := hA.real ω hσ θ
    have h0 : |a' 0| < r := lt_of_le_of_lt (by simpa using norm_le_pi_norm a' 0) ha'
    have hpos : 0 < P₀ + a' 0 := by linarith [(abs_lt.1 h0).1, hP₀.1]
    have hlt : 2 * (P₀ + a' 0) < ρ ^ 2 := by linarith [(abs_lt.1 h0).2, hP₀.2]
    have e1 : p0 ν b W + (Φ (ofRe θ) ω).1 0 = ((P₀ + a' 0 : ℝ) : ℂ) := by
      rw [hab, hp0]; simp [ofRe]
    have e2 : (Φ (ofRe θ) ω).2 0 = ((b' 0 : ℝ) : ℂ) := by rw [hab]; simp [ofRe]
    obtain ⟨x, hx, hxn⟩ := polarW_real (ar := b' 0) hpos hρ0 hlt
    refine ⟨x, by rw [e1, e2]; exact hx, hxn, ?_⟩
    rw [e1, show (2 : ℂ) * ((P₀ + a' 0 : ℝ) : ℂ) = ((2 * (P₀ + a' 0) : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_mem_slitPlane.2 (by linarith)
  -- the torus orbit `θ(t) = (θ₀ + tσ, −u + t)` and its image in the chart
  set θt : ℝ → Fin 2 → ℝ := fun t => ![θ₀ + t * σ, -u + t] with hθt
  set Z : ℝ → Ph 2 := fun t => Φ (ofRe (θt t)) ω with hZ
  set w : ℝ → C2 := fun t => polarW (p0 ν b W + (Z t).1 0) ((Z t).2 0) with hw
  have hpath : ∀ t : ℝ, HasDerivAt (fun t => ofRe (θt t)) (ofRe ω) t := by
    intro t
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i
    · simpa [θt, ofRe, ω] using (((hasDerivAt_id' t).mul_const σ).const_add θ₀).ofReal_comp
    · simpa [θt, ofRe, ω] using ((hasDerivAt_id' t).const_add (-u)).ofReal_comp
  have hZd : ∀ t : ℝ, HasDerivAt Z (XH (ham (eNP ν b) (pertP ν b R)) W (Z t)) t := by
    intro t
    have hd : DifferentiableAt ℂ (fun θ' => Φ θ' ω) (ofRe (θt t)) :=
      (hA.analytic ω hσ).differentiableAt ((isOpen_Tstar s).mem_nhds (ofRe_mem_Tstar hs0 _))
    have h1 := (hd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t (hpath t)
    rw [show Z t = Φ (ofRe (θt t)) ω from rfl, hA.invariant ω hσ (θt t)]
    exact h1
  have hτ : ∀ t : ℝ, (Z t).2 1 = (t : ℂ) := by
    intro t
    rw [show Z t = Φ (ofRe (θt t)) ω from rfl, hu]
    simp [θt]
  have hUo : IsOpen (polydisc ρ ×ˢ strip s) :=
    (isOpen_lt continuous_norm continuous_const).prod
      (isOpen_lt (by fun_prop : Continuous fun t : ℂ => |t.im|) continuous_const)
  have hwpd : ∀ t : ℝ, w t ∈ polydisc ρ := by
    intro t
    obtain ⟨x, hx, hxn, -⟩ := hpt (θt t)
    show ‖w t‖ < ρ
    rw [show w t = ofR x from hx.symm]
    exact (norm_ofR_le x).trans_lt hxn
  have hwd : ∀ t : ℝ, HasDerivAt w (hamVF (fun v => Kbnf ν b R v (t : ℂ)) (w t)) t := by
    intro t
    obtain ⟨x', -, -, hs⟩ := hpt (θt t)
    have hmem : ((w t, (Z t).2 1) : C2 × ℂ) ∈ polydisc ρ ×ˢ strip s :=
      ⟨hwpd t, by rw [hτ]; simp [strip, hs0]⟩
    have hK : HasFDerivAt (Kq ν b R) (fderiv ℂ (Kq ν b R) (w t, (Z t).2 1)) (w t, (Z t).2 1) :=
      ((hH.holo _ hmem).differentiableAt (hUo.mem_nhds hmem)).hasFDerivAt
    set D := fderiv ℂ (Kq ν b R) (w t, (Z t).2 1)
    set P := p0 ν b W + (Z t).1 0
    set a := (Z t).2 0
    have hPA := partial_A hb hW1 hs hK
    have hPI := partial_I hb hW1 hs hK
    have h1 : HasDerivAt (fun t => p0 ν b W + (Z t).1 0) (-D (dA P a, 0)) t := by
      have := (hasDerivAt_fst_apply (hZd t) 0).const_add (p0 ν b W)
      simpa [XH, hPA] using this
    have h2 : HasDerivAt (fun t => (Z t).2 0) (D (dP P a, 0)) t := by
      have := hasDerivAt_snd_apply (hZd t) 0
      simpa [XH, hPI] using this
    have h3 := hasDerivAt_polarW h1 h2 hs
    have hP0 : P ≠ 0 := by
      intro h0
      have h2P : (2 : ℂ) * P ∈ Complex.slitPlane := hs
      rw [h0, mul_zero] at h2P
      exact Complex.zero_notMem_slitPlane h2P
    set L : C2 →L[ℂ] ℂ := D.comp (ContinuousLinearMap.inl ℂ C2 ℂ)
    have hLv : ∀ v, D (v, 0) = L v := fun v => rfl
    have hfd : fderiv ℂ (fun v => Kbnf ν b R v (t : ℂ)) (w t) = L := by
      rw [← hτ t]
      exact (HasFDerivAt.comp (g := Kq ν b R) (w t) hK
        (hasFDerivAt_prodMk_left (𝕜 := ℂ) (w t) ((Z t).2 1))).fderiv
    rw [hLv, hLv, field_eq L hP0] at h3
    convert h3 using 1
    simp [hamVF, hfd]
  -- the endpoints
  have hθ0 : θt 0 = ![θ₀, -u] := by funext i; fin_cases i <;> simp [θt]
  have hθ2 : ofRe (θt (2 * π)) = ofRe ![θ₀ + 2 * π * σ, -u] + twoPiE 1 := by
    funext i; fin_cases i <;> simp [θt, ofRe, twoPiE]
  have hw0 : w 0 = polarW (p0 ν b W + (Φ (ofRe ![θ₀, -u]) ω).1 0) ((Φ (ofRe ![θ₀, -u]) ω).2 0) := by
    simp only [w, Z, hθ0]
  have hw2 : w (2 * π) = polarW (p0 ν b W + (Φ (ofRe ![θ₀ + 2 * π * σ, -u]) ω).1 0)
      ((Φ (ofRe ![θ₀ + 2 * π * σ, -u]) ω).2 0) := by
    simp only [w, Z, hθ2, hA.periodic ω hσ 1]
    simp [twoPiE]
  -- uniqueness against the solution given by `IsPeriodMap`
  obtain ⟨x, hx, hxn, -⟩ := hpt ![θ₀, -u]
  refine ⟨x, hx, ?_⟩
  rw [← hw2]
  obtain ⟨γ, hγs, hγ0, hγ2⟩ := hB.period x hxn
  have hpi : 0 < 2 * π := Real.two_pi_pos
  set Γ : ℝ → Cn 3 := fun t => ext (γ t) t
  set Ψ : ℝ → Cn 3 := fun t => ext (w t) t
  have hγc : ContinuousOn γ (Icc 0 (2 * π)) := fun t ht => (hγs t ht).continuousWithinAt
  have hΓc : ContinuousOn Γ (Icc 0 (2 * π)) := by
    refine continuousOn_pi.2 fun i => ?_
    fin_cases i
    · simpa [Γ, PeriodMapAux.ext] using continuousOn_pi.1 hγc 0
    · simpa [Γ, PeriodMapAux.ext] using continuousOn_pi.1 hγc 1
    · simpa [Γ, PeriodMapAux.ext] using Complex.continuous_ofReal.continuousOn
  have hΓd : ∀ t ∈ Ico 0 (2 * π), Γ t ∈ Dom ρ s →
      HasDerivWithinAt Γ (Fe (Kbnf ν b R) (Γ t)) (Ici t) t := by
    intro t ht hΓt
    have hγt := (hγs t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1))
    rw [hamVF_eq hH hΓt] at hγt
    refine hasDerivWithinAt_pi.2 fun i => ?_
    fin_cases i
    · simpa [Γ, PeriodMapAux.ext, pr] using hasDerivWithinAt_pi.1 hγt 0
    · simpa [Γ, PeriodMapAux.ext, pr] using hasDerivWithinAt_pi.1 hγt 1
    · simpa [Γ, PeriodMapAux.ext, Fe_two] using (hasDerivAt_ofReal t).hasDerivWithinAt (s := Ici t)
  have hΨD : ∀ t : ℝ, Ψ t ∈ Dom ρ s := fun t =>
    ⟨by simpa [Ψ, pr_ext] using hwpd t, by simp [Ψ, PeriodMapAux.ext, strip, hs0]⟩
  have hΨd : ∀ t : ℝ, HasDerivAt Ψ (Fe (Kbnf ν b R) (Ψ t)) t := by
    intro t
    have hwt := hwd t
    rw [hamVF_eq hH (hΨD t)] at hwt
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i
    · simpa [Ψ, PeriodMapAux.ext, pr] using hasDerivAt_pi.1 hwt 0
    · simpa [Ψ, PeriodMapAux.ext, pr] using hasDerivAt_pi.1 hwt 1
    · simpa [Ψ, PeriodMapAux.ext, Fe_two] using hasDerivAt_ofReal t
  have key := solution_eq_flow (isOpen_Dom ρ s) (Fe_diff hH) hΓc hΓd
    (fun t _ => (hΨd t).continuousAt.continuousWithinAt)
    (fun t _ => (hΨd t).hasDerivWithinAt) (fun t _ => hΨD t)
    (by simp [Γ, Ψ, hγ0, hx, hw0]) (2 * π) ⟨hpi.le, le_rfl⟩
  rw [← hγ2, ← pr_ext (γ (2 * π)) ((2 * π : ℝ) : ℂ), ← pr_ext (w (2 * π)) ((2 * π : ℝ) : ℂ)]
  exact congrArg pr key

end ABC.S4.R7InvariantAux
