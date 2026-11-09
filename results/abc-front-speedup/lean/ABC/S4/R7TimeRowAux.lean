import ABC.S4.Defs

/-! Helpers for `R7_time_row`: Darboux on a line, periodic bounds, two incommensurate periods. -/

open Set Metric Filter Topology Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)

noncomputable section

namespace ABC.S4.R7TimeRowAux

/-- A bounded function whose derivative takes at most two values: Darboux forces the derivative
to be constant, and boundedness forces it to be `0`. -/
theorem deriv_eq_zero_of_two_vals {g d : ℝ → ℝ} {a b M : ℝ}
    (hg : ∀ t, HasDerivAt g (d t) t) (hd : ∀ t, d t = a ∨ d t = b)
    (hM : ∀ t, |g t| ≤ M) : (∀ t, d t = 0) ∧ ∀ t, g t = g 0 := by
  have hconst : ∀ t, d t = d 0 := by
    intro t
    by_contra hne
    have hoc : (d '' univ).OrdConnected :=
      ordConnected_univ.image_hasDerivWithinAt fun x _ => (hg x).hasDerivWithinAt
    have hm : (d 0 + d t) / 2 ∈ d '' univ := by
      refine hoc.uIcc_subset (mem_image_of_mem d (mem_univ 0)) (mem_image_of_mem d (mem_univ t)) ?_
      rw [mem_uIcc]
      rcases le_total (d 0) (d t) with h | h
      · left; constructor <;> linarith
      · right; constructor <;> linarith
    obtain ⟨s, -, hs⟩ := hm
    have : d s = d 0 ∨ d s = d t := by
      rcases hd 0 with h0 | h0 <;> rcases hd t with ht | ht <;> rcases hd s with hs' | hs' <;>
        (left; linarith)
    rcases this with h | h <;> exact hne (by linarith)
  set k := d 0
  have hlin : ∀ t, g t = g 0 + k * t := by
    have hz : ∀ t, HasDerivAt (fun t => g t - k * t) 0 t := by
      intro t
      have h2 : HasDerivAt (fun t => k * t) k t := by simpa using (hasDerivAt_id t).const_mul k
      have := (hg t).sub h2
      rw [hconst t, sub_self] at this
      exact this
    have := is_const_of_deriv_eq_zero (fun t => (hz t).differentiableAt) (fun t => (hz t).deriv)
    intro t
    have := this t 0
    simp only [mul_zero, sub_zero] at this
    linarith
  have hk : k = 0 := by
    by_contra hk
    have h1 := hM ((M + |g 0| + 1) / k)
    rw [hlin, mul_div_cancel₀ _ hk] at h1
    have := neg_abs_le (g 0)
    have := (abs_le.1 h1).2
    linarith
  refine ⟨fun t => (hconst t).trans hk, fun t => ?_⟩
  rw [hlin t, hk, zero_mul, add_zero]

/-- A continuous function on `ℝ²`, `2π`-periodic in each variable, is bounded. -/
theorem bounded_of_periodic {F : (Fin 2 → ℝ) → ℝ} (hc : Continuous F)
    (hp : ∀ j : Fin 2, ∀ x, F (x + Pi.single j (2 * π)) = F x) : ∃ M, ∀ x, |F x| ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : Fin 2 → ℝ)) (b := fun _ => 2 * π)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨C, fun x => ?_⟩
  set y : Fin 2 → ℝ := fun i => toIcoMod two_pi_pos 0 (x i) with hy
  set n : Fin 2 → ℤ := fun i => toIcoDiv two_pi_pos 0 (x i) with hn
  have hxy : x = y + n 0 • (Pi.single 0 (2 * π) : Fin 2 → ℝ) + n 1 • Pi.single 1 (2 * π) := by
    ext i
    have := toIcoMod_add_toIcoDiv_zsmul two_pi_pos 0 (x i)
    fin_cases i <;> simp [y, n]
  have hper : ∀ j : Fin 2, Function.Periodic F (Pi.single j (2 * π)) := fun j x => hp j x
  have hFxy : F x = F y := by
    rw [hxy, ((hper 1).zsmul (n 1)) _, ((hper 0).zsmul (n 0)) _]
  have hyI : y ∈ Icc (0 : Fin 2 → ℝ) (fun _ => 2 * π) := by
    constructor
    · intro i
      exact (toIcoMod_mem_Ico two_pi_pos 0 (x i)).1
    · intro i
      have := (toIcoMod_mem_Ico two_pi_pos 0 (x i)).2
      simp only [zero_add] at this
      exact this.le
  rw [hFxy]
  simpa [Real.norm_eq_abs] using hC y hyI

/-- A continuous function on `ℝ` with two periods of irrational ratio is constant. -/
theorem const_of_two_periods {H : ℝ → ℝ} (hc : Continuous H) {p q : ℝ}
    (hp : ∀ x, H (x + p) = H x) (hq : ∀ x, H (x + q) = H x) (hirr : Irrational (p / q)) :
    ∀ x, H x = H 0 := by
  let S : AddSubgroup ℝ :=
    { carrier := {c | ∀ x, H (x + c) = H x}
      zero_mem' := fun x => by simp
      add_mem' := fun {a b} ha hb x => by
        show H (x + (a + b)) = H x
        rw [← add_assoc, hb, ha]
      neg_mem' := fun {a} ha x => by
        show H (x + -a) = H x
        conv_rhs => rw [← neg_add_cancel_right x a]
        rw [ha] }
  have hle : AddSubgroup.closure {p, q} ≤ S := by
    rw [AddSubgroup.closure_le]
    intro c hc'
    rcases hc' with rfl | rfl
    · exact hp
    · exact hq
  have hdense : Dense (S : Set ℝ) :=
    (dense_addSubgroupClosure_pair_iff.2 hirr).mono hle
  have hclosed : IsClosed (S : Set ℝ) := by
    have : (S : Set ℝ) = ⋂ x, {c | H (x + c) = H x} := by
      ext c; simp [S]
    rw [this]
    exact isClosed_iInter fun x =>
      isClosed_eq (hc.comp (continuous_const.add continuous_id)) continuous_const
  intro x
  have hx : x ∈ (S : Set ℝ) := by
    rw [← hclosed.closure_eq, hdense.closure_eq]; trivial
  have := hx 0
  simpa using this

/-- The `θ`-independent part: `∂_{I₁} ham` at `z` is the parameter `w₁`, or `0` where `fderiv`
is junk. -/
theorem fderiv_ham_I1 (ν b : ℝ) (R : C2 → ℂ → ℂ) (θc w z : Fin 2 → ℂ) :
    fderiv ℂ (fun I' => ham (eNP ν b) (pertP ν b R) (I', θc, w)) z (Pi.single 1 1) = w 1 ∨
      fderiv ℂ (fun I' => ham (eNP ν b) (pertP ν b R) (I', θc, w)) z (Pi.single 1 1) = 0 := by
  set G := fun I' => ham (eNP ν b) (pertP ν b R) (I', θc, w) with hG
  by_cases hd : DifferentiableAt ℂ G z
  · left
    have hline : HasDerivAt (fun t : ℂ => z + t • (Pi.single 1 1 : Fin 2 → ℂ))
        (Pi.single 1 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (Pi.single 1 1 : Fin 2 → ℂ)).const_add z
    have h1 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hline (by simp)
    have heq : (G ∘ fun t : ℂ => z + t • (Pi.single 1 1 : Fin 2 → ℂ)) =
        fun t => G z + w 1 * t := by
      funext t
      simp [G, ham, ABC.S4.pertP, Fin.sum_univ_two]
      ring
    have h2 : HasDerivAt (fun t : ℂ => G z + w 1 * t) (w 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (w 1)).const_add (G z)
    rw [heq] at h1
    exact h1.unique h2
  · right
    rw [fderiv_zero_of_not_differentiableAt hd]
    rfl

/-- The `θ₁`-row of `Ψ` along the real line `t ↦ θ + tω`. -/
theorem hasDerivAt_line (Ψ : (Fin 2 → ℂ) → Ph 2) (θ ω : Fin 2 → ℝ) (t : ℝ)
    (hd : DifferentiableAt ℂ Ψ (ofRe (θ + t • ω))) :
    HasDerivAt (fun t : ℝ => ((Ψ (ofRe (θ + t • ω))).2 1).re)
      ((fderiv ℂ Ψ (ofRe (θ + t • ω)) (ofRe ω)).2 1).re t := by
  have hγ : HasDerivAt (fun t : ℝ => ofRe (θ + t • ω)) (ofRe ω) t := by
    rw [hasDerivAt_pi]
    intro i
    have := (((hasDerivAt_id t).mul_const (ω i)).const_add (θ i)).ofReal_comp
    simpa [ofRe] using this
  have h1 := (hd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hγ
  let L : Ph 2 →L[ℝ] ℝ := Complex.reCLM.comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℂ) 1).comp
      (ContinuousLinearMap.snd ℝ (Fin 2 → ℂ) (Fin 2 → ℂ)))
  have h2 := L.hasFDerivAt.comp_hasDerivAt t h1
  simpa [L, Function.comp_def] using h2

/-- For `α > 0`, a Diophantine `ω ∈ Δ_α^2` has irrational ratio `ω₀ / ω₁`. -/
theorem irrational_of_delta {α : ℝ} (hα : 0 < α) {ω : Fin 2 → ℝ}
    (hω : ω ∈ ABC.Poschel2001.Delta (2 : ℝ) α) (hω1 : ω 1 ≠ 0) : Irrational (ω 0 / ω 1) := by
  rintro ⟨r, hr⟩
  set k : Fin 2 → ℤ := ![(r.den : ℤ), -r.num]
  have hk : k ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [k] at this
  have hpair : ABC.Poschel2001.pairZ k ω = 0 := by
    have h0 : ω 0 = r * ω 1 := by rw [hr]; field_simp
    have hnum : (r.num : ℝ) = r.den * r := by
      rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_mul, Rat.den_mul_eq_num]
    simp [ABC.Poschel2001.pairZ, Fin.sum_univ_two, k, h0, hnum]
    ring
  have hl1 : 0 < ABC.Poschel2001.l1norm k := by
    have : (1 : ℝ) ≤ |((k 0 : ℤ) : ℝ)| := by
      simp only [k, Matrix.cons_val_zero, Int.cast_natCast, Nat.abs_cast]
      exact_mod_cast r.den_pos
    have h1 : 0 ≤ |((k 1 : ℤ) : ℝ)| := abs_nonneg _
    simp only [ABC.Poschel2001.l1norm, Fin.sum_univ_two]
    linarith
  have := hω k hk
  rw [hpair, abs_zero] at this
  have : 0 < α / ABC.Poschel2001.l1norm k ^ (2 : ℝ) := div_pos hα (Real.rpow_pos_of_pos hl1 _)
  linarith

/-- `R7_time_row`, with `0 < α`. -/
theorem time_row {ν b ε α r s h δ c : ℝ} {R : C2 → ℂ → ℂ} {φ : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    {Φ : C2 → (Fin 2 → ℝ) → Ph 2}
    (hα : 0 < α) (hA : Conclusion 2 c (OmegaE ν b ε) α r s h δ (eNP ν b) (pertP ν b R) φ Φ) :
    ∀ ω ∈ OmegaAlpha 2 (OmegaE ν b ε) α, φ ω 1 = ω 1 ∧
      ∃ u : ℝ, ∀ θ : Fin 2 → ℝ, (Φ (ofRe θ) ω).2 1 = θ 1 + u := by
  intro ω hω
  set Ψ : (Fin 2 → ℂ) → Ph 2 := fun θ => Φ θ ω with hΨ
  have hω1 : ω 1 ≠ 0 := by
    intro h0
    have := hω.1.1
    rw [h0] at this
    norm_num at this
  -- `Ψ` is complex differentiable at real points, since its derivative there is injective
  have hdiff : ∀ x : Fin 2 → ℝ, DifferentiableAt ℂ Ψ (ofRe x) := by
    intro x
    by_contra hnd
    have hinj := (hA.embedding ω hω).2 x
    rw [fderiv_zero_of_not_differentiableAt hnd] at hinj
    have := congrFun (@hinj (Pi.single 0 1) 0 (by simp)) 0
    simp at this
  set F : (Fin 2 → ℝ) → ℝ := fun x => ((Ψ (ofRe x)).2 1).re - x 1 with hF
  have hofRe : Continuous (ofRe : (Fin 2 → ℝ) → Fin 2 → ℂ) :=
    continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)
  have hFc : Continuous F := by
    refine Continuous.sub ?_ (continuous_apply 1)
    refine Complex.continuous_re.comp ((continuous_apply 1).comp (continuous_snd.comp ?_))
    exact continuous_iff_continuousAt.2 fun x => (hdiff x).continuousAt.comp hofRe.continuousAt
  have hFp : ∀ (j : Fin 2) x, F (x + Pi.single j (2 * π)) = F x := by
    intro j x
    have hadd : ofRe (x + Pi.single j (2 * π)) = ofRe x + ABC.Poschel2001.twoPiE j := by
      ext i
      fin_cases j <;> fin_cases i <;> simp [ofRe, ABC.Poschel2001.twoPiE]
    simp only [hF, hadd, hΨ, hA.periodic ω hω j x]
    fin_cases j <;> simp [ABC.Poschel2001.twoPiE]
  obtain ⟨M, hM⟩ := bounded_of_periodic hFc hFp
  -- the `θ₁`-row of `X_H` at `φ(ω)` is `φ(ω)₁` or `0`
  set d : (Fin 2 → ℝ) → ℝ := fun x => ((fderiv ℂ Ψ (ofRe x) (ofRe ω)).2 1).re - ω 1 with hd
  have hdv : ∀ x, d x = φ ω 1 - ω 1 ∨ d x = 0 - ω 1 := by
    intro x
    have hinv := congrArg (fun z : Ph 2 => (z.2 1).re) (hA.invariant ω hω x)
    simp only [hd, hΨ, ← hinv, ABC.Poschel2001.XH]
    rcases fderiv_ham_I1 ν b R _ (ofRe (φ ω)) _ with h | h
    · left; rw [h]; simp [ofRe]
    · right; rw [h]; simp
  -- along each line `θ + tω`, `F` is constant, and the derivative is `0`
  have hline : ∀ θ : Fin 2 → ℝ, (∀ t : ℝ, d (θ + t • ω) = 0) ∧ ∀ t : ℝ, F (θ + t • ω) = F θ := by
    intro θ
    have hg : ∀ t, HasDerivAt (fun t : ℝ => F (θ + t • ω)) (d (θ + t • ω)) t := by
      intro t
      have h1 := hasDerivAt_line Ψ θ ω t (hdiff _)
      have h2 : HasDerivAt (fun t : ℝ => (θ + t • ω) 1) (ω 1) t := by
        simpa using ((hasDerivAt_id t).mul_const (ω 1)).const_add (θ 1)
      exact h1.sub h2
    have := deriv_eq_zero_of_two_vals hg (fun t => hdv _) (fun t => hM _)
    refine ⟨this.1, fun t => ?_⟩
    simpa using this.2 t
  refine ⟨?_, ?_⟩
  · have h0 := (hline 0).1 0
    simp only [zero_smul, add_zero] at h0
    rcases hdv 0 with h | h
    · linarith
    · exact absurd (by linarith : ω 1 = 0) hω1
  -- density: `F θ = Hf (θ₀ − ρ θ₁)` with `Hf` of periods `2π` and `2πρ`, `ρ` irrational
  set ρ := ω 0 / ω 1 with hρ
  have hirr : Irrational ρ := irrational_of_delta hα hω.2.1 hω1
  set Hf : ℝ → ℝ := fun y => F ![y, 0] with hHf
  have hred : ∀ θ : Fin 2 → ℝ, F θ = Hf (θ 0 - ρ * θ 1) := by
    intro θ
    rw [← (hline θ).2 (-(θ 1 / ω 1))]
    simp only [hHf]
    congr 1
    ext i
    fin_cases i <;> simp [hρ] <;> field_simp <;> ring
  have hp1 : ∀ y, Hf (y + 2 * π * ρ) = Hf y := by
    intro y
    have := hFp 1 ![y + 2 * π * ρ, 0]
    rw [hred, hred] at this
    simp only [Pi.add_apply] at this
    have e : y + 2 * π * ρ - ρ * (2 * π) = y := by ring
    simpa [e] using this.symm
  have hp2 : ∀ y, Hf (y + 2 * π) = Hf y := by
    intro y
    have := hFp 0 ![y, 0]
    rw [hred, hred] at this
    simpa using this
  have hHc : Continuous Hf := by
    refine hFc.comp ?_
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_id
    · simpa using continuous_const
  have hirr' : Irrational (2 * π * ρ / (2 * π)) := by
    rwa [mul_div_cancel_left₀ _ (by positivity : (2 * π : ℝ) ≠ 0)]
  have hconst := const_of_two_periods hHc hp1 hp2 hirr'
  refine ⟨Hf 0, fun θ => ?_⟩
  obtain ⟨a, b', hab, -⟩ := hA.real ω hω θ
  have hFθ : F θ = Hf 0 := by rw [hred, hconst]
  have h1 : (Φ (ofRe θ) ω).2 1 = (b' 1 : ℂ) := by rw [hab]; rfl
  have h2 : b' 1 - θ 1 = Hf 0 := by
    rw [← hFθ]
    simp only [hF, hΨ, h1, Complex.ofReal_re]
  rw [h1, ← h2]
  push_cast
  ring

end ABC.S4.R7TimeRowAux
