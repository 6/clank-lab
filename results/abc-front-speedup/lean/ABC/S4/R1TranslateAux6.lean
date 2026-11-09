import ABC.S4.R1TranslateAux5

/-! R1 helpers: the real analytic chart `a ↦ Φ(a) - Φ(p)` near `p`, inverted by the analytic
inverse function theorem. -/

open Set Metric Filter Topology Real

noncomputable section

namespace ABC.S4.R1TranslateAux

lemma phiC_ofR (x : E 2) : phiC (ofR x) = ofR (phi x) := by
  ext i; fin_cases i <;> simp [phiC, ofR, phi]

lemma ofR_sub (x y : E 2) : ofR (x - y) = ofR x - ofR y := by
  ext i; simp [ofR]

lemma ofR_injective : Function.Injective ofR := fun x y h =>
  ext2 (by simpa [ofR] using congrFun h 0) (by simpa [ofR] using congrFun h 1)

/-- `ofR` as a real continuous linear map. -/
def ofRL : E 2 →L[ℝ] C2 :=
  ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i)

lemma ofRL_apply (x : E 2) : ofRL x = ofR x := by
  ext i; simp [ofRL, ofR]

lemma contDiff_phi {n : WithTop ℕ∞} : ContDiff ℝ n phi := by
  have hc : ∀ i : Fin 2, ContDiff ℝ n fun x : E 2 => x i := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  apply contDiff_piLp'
  intro i; fin_cases i
  · simpa [phi] using ((hc 0).mul (Real.contDiff_sin.comp (hc 1))).add
      (Real.contDiff_sin.comp (hc 0))
  · simpa [phi] using hc 1

lemma fderiv_phi_injective {a : E 2} (ha : Real.sin (a 1) + Real.cos (a 0) ≠ 0) :
    Function.Injective (fderiv ℝ phi a) := by
  have hD : HasFDerivAt phi (fderiv ℝ phi a) a :=
    ((contDiff_phi (n := 1)).differentiable one_ne_zero a).hasFDerivAt
  have h1 : HasFDerivAt (fun x => ofR (phi x)) (ofRL.comp (fderiv ℝ phi a)) a := by
    have := ofRL.hasFDerivAt.comp a hD
    simpa [Function.comp_def, ofRL_apply] using this
  have h2 : HasFDerivAt (fun x => ofR (phi x)) (((phiCD (ofR a)).restrictScalars ℝ).comp ofRL)
      a := by
    have := ((hasFDerivAt_phiC (ofR a)).restrictScalars ℝ).comp a (ofRL.hasFDerivAt (x := a))
    simpa [Function.comp_def, ofRL_apply, phiC_ofR] using this
  have heq := h1.unique h2
  rw [injective_iff_map_eq_zero]
  intro v hv
  have := congrArg (fun L : E 2 →L[ℝ] C2 => L v) heq
  simp only [ContinuousLinearMap.comp_apply, hv, map_zero, ofRL_apply,
    ContinuousLinearMap.coe_restrictScalars'] at this
  rw [phiCD_apply] at this
  have e0 := congrFun this 0
  have e1 := congrFun this 1
  simp only [ofR, Matrix.cons_val_zero, Matrix.cons_val_one, ContinuousLinearMap.zero_apply, Pi.zero_apply] at e0 e1
  have hv1 : ((v 1 : ℝ) : ℂ) = 0 := e1.symm
  rw [hv1, mul_zero, add_zero] at e0
  have ha' : Complex.sin ((a 1 : ℝ) : ℂ) + Complex.cos ((a 0 : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sin, ← Complex.ofReal_cos]; exact_mod_cast ha
  have hv0 : ((v 0 : ℝ) : ℂ) = 0 := (mul_eq_zero.1 e0.symm).resolve_left ha'
  exact ext2 (by simpa using hv0) (by simpa using hv1)

/-- The derivative of `Φ` as a continuous linear equivalence. -/
def Dequiv (a : E 2) (ha : Real.sin (a 1) + Real.cos (a 0) ≠ 0) : E 2 ≃L[ℝ] E 2 :=
  (LinearEquiv.ofInjectiveEndo (fderiv ℝ phi a : E 2 →ₗ[ℝ] E 2)
    (fderiv_phi_injective ha)).toContinuousLinearEquiv

lemma Dequiv_coe (a : E 2) (ha : Real.sin (a 1) + Real.cos (a 0) ≠ 0) :
    (Dequiv a ha : E 2 →L[ℝ] E 2) = fderiv ℝ phi a := by
  ext v; rfl

lemma hasFDerivAt_phi_sub (a p : E 2) (ha : Real.sin (a 1) + Real.cos (a 0) ≠ 0) :
    HasFDerivAt (fun a => phi a - phi p) (Dequiv a ha : E 2 →L[ℝ] E 2) a := by
  rw [Dequiv_coe]
  exact (((contDiff_phi (n := 1)).differentiable one_ne_zero a).hasFDerivAt).sub_const _

/-- The chart `a ↦ Φ(a) - Φ(p)` on a small neighbourhood of `p`, analytic both ways. -/
theorem real_chart {p : E 2} (hp0 : 0 < Real.sin (p 1) + Real.cos (p 0)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ e : OpenPartialHomeomorph (E 2) (E 2), (∀ a, e a = phi a - phi p) ∧ p ∈ e.source ∧
      e.source ⊆ ball p ε ∧ ContDiffOn ℝ ⊤ e.symm e.target ∧ ContDiffOn ℝ ⊤ e e.source := by
  set f : E 2 → E 2 := fun a => phi a - phi p with hf
  have hfc : ContDiff ℝ ⊤ f := contDiff_phi.sub contDiff_const
  have hstrict : HasStrictFDerivAt f (Dequiv p hp0.ne' : E 2 →L[ℝ] E 2) p :=
    hfc.contDiffAt.hasStrictFDerivAt' (hasFDerivAt_phi_sub p p hp0.ne') (by simp)
  set W : Set (E 2) := {a | 0 < Real.sin (a 1) + Real.cos (a 0)} ∩ ball p ε with hW
  have hWo : IsOpen W := by
    refine (isOpen_lt continuous_const ?_).inter isOpen_ball
    exact (Real.continuous_sin.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous).add
      (Real.continuous_cos.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous)
  set e := (hstrict.toOpenPartialHomeomorph f).restrOpen W hWo with he
  have hcoe : ∀ a, e a = f a := fun a => rfl
  have hsrc : e.source = (hstrict.toOpenPartialHomeomorph f).source ∩ W :=
    OpenPartialHomeomorph.restrOpen_source _ _ _
  refine ⟨e, hcoe, ?_, ?_, ?_, ?_⟩
  · rw [hsrc]
    exact ⟨hstrict.mem_toOpenPartialHomeomorph_source, hp0, mem_ball_self hε⟩
  · intro a ha; rw [hsrc] at ha; exact ha.2.2
  · intro y hy
    have ha : e.symm y ∈ e.source := e.map_target hy
    rw [hsrc] at ha
    have hρ : Real.sin (e.symm y 1) + Real.cos (e.symm y 0) ≠ 0 := ha.2.1.ne'
    exact (e.contDiffAt_symm hy (hasFDerivAt_phi_sub _ p hρ) hfc.contDiffAt).contDiffWithinAt
  · exact hfc.contDiffOn

end ABC.S4.R1TranslateAux
