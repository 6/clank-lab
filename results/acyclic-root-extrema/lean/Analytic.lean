import Endpoint

namespace BBPSplitStar
open Polynomial

lemma evalR_expectedCandidate (x : ℝ) :
    evalR expectedCandidate x = x^4 + 90*x^3 + 66*x^2 + 12*x + 1 := by
  simp [evalR, expectedCandidate]

lemma evalC_expectedComparator (z : ℂ) :
    evalC expectedComparator z = z^4 + 85*z^3 + 66*z^2 + 12*z + 1 := by
  simp [evalC, expectedComparator]

lemma evalC_ofReal (p : Polynomial ℤ) (x : ℝ) :
    evalC p (x : ℂ) = (evalR p x : ℂ) := by
  have hhom : Complex.ofRealHom.comp (Int.castRingHom ℝ) =
      Int.castRingHom ℂ := by
    apply RingHom.ext
    intro k
    simp
  simpa only [evalC, evalR, Polynomial.eval_map, hhom, Complex.ofRealHom_eq_coe] using
    (Polynomial.hom_eval₂ (p := p) (f := Int.castRingHom ℝ) (g := Complex.ofRealHom) x).symm

lemma candidate_real_interval :
    ∃ r : ℝ, -100 < r ∧ r < -86 ∧ evalR expectedCandidate r = 0 := by
  have hleft : 0 < evalR expectedCandidate (-100) := by
    rw [evalR_expectedCandidate]
    norm_num
  have hright : evalR expectedCandidate (-86) < 0 := by
    rw [evalR_expectedCandidate]
    norm_num
  have hcont : ContinuousOn (evalR expectedCandidate) (Set.Icc (-100) (-86)) :=
    (expectedCandidate.map (Int.castRingHom ℝ)).continuous.continuousOn
  obtain ⟨r, hr, hzero⟩ :=
    intermediate_value_Icc' (by norm_num : (-100 : ℝ) ≤ -86) hcont
      (show (0 : ℝ) ∈ Set.Icc (evalR expectedCandidate (-86))
        (evalR expectedCandidate (-100)) from ⟨hright.le, hleft.le⟩)
  have hneleft : r ≠ -100 := by
    intro h
    subst r
    linarith
  have hneright : r ≠ -86 := by
    intro h
    subst r
    linarith
  exact ⟨r, lt_of_le_of_ne hr.1 (Ne.symm hneleft),
    lt_of_le_of_ne hr.2 hneright, hzero⟩

lemma normalized_comparator_lt_one (t : ℝ) (ht : 86 ≤ t) :
    85/t + 66/t^2 + 12/t^3 + 1/t^4 < 1 := by
  have h1 : 85/t ≤ (85 : ℝ)/86 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) ht
  have h2 : 66/t^2 ≤ (66 : ℝ)/86^2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 86) ht 2)
  have h3 : 12/t^3 ≤ (12 : ℝ)/86^3 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 86) ht 3)
  have h4 : 1/t^4 ≤ (1 : ℝ)/86^4 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 86) ht 4)
  have hfixed : (85 : ℝ)/86 + 66/86^2 + 12/86^3 + 1/86^4 < 1 := by
    norm_num
  linarith

lemma comparator_strict_dominance (t : ℝ) (ht : 86 ≤ t) :
    85*t^3 + 66*t^2 + 12*t + 1 < t^4 := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 86) ht
  have htne : t ≠ 0 := ne_of_gt htpos
  have hratio : (85*t^3 + 66*t^2 + 12*t + 1) / t^4 =
      85/t + 66/t^2 + 12/t^3 + 1/t^4 := by
    field_simp [htne]
  have hscaled : (85*t^3 + 66*t^2 + 12*t + 1) / t^4 < 1 := by
    rw [hratio]
    exact normalized_comparator_lt_one t ht
  exact (div_lt_one₀ (pow_pos htpos 4)).mp hscaled

lemma comparator_complex_disk (z : ℂ) (hz : evalC expectedComparator z = 0) :
    ‖z‖ < 86 := by
  by_contra hsmall
  have ht : (86 : ℝ) ≤ ‖z‖ := le_of_not_gt hsmall
  have hzero : z^4 + 85*z^3 + 66*z^2 + 12*z + 1 = 0 := by
    simpa only [evalC_expectedComparator] using hz
  have hzpow : z^4 = -(85*z^3 + 66*z^2 + 12*z + 1) := by
    linear_combination hzero
  have htriangle : ‖z‖^4 ≤ 85*‖z‖^3 + 66*‖z‖^2 + 12*‖z‖ + 1 := by
    calc
      ‖z‖^4 = ‖z^4‖ := (norm_pow z 4).symm
      _ = ‖85*z^3 + 66*z^2 + 12*z + 1‖ := by rw [hzpow, norm_neg]
      _ ≤ ‖85*z^3 + 66*z^2 + 12*z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ (‖85*z^3 + 66*z^2‖ + ‖12*z‖) + ‖(1 : ℂ)‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ ≤ ((‖85*z^3‖ + ‖66*z^2‖) + ‖12*z‖) + ‖(1 : ℂ)‖ :=
        add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
      _ = 85*‖z‖^3 + 66*‖z‖^2 + 12*‖z‖ + 1 := by
        norm_num [norm_mul, norm_pow]
  exact (not_lt_of_ge htriangle) (comparator_strict_dominance ‖z‖ ht)

lemma expected_polynomials_ne : expectedCandidate ≠ expectedComparator := by
  intro h
  have hc := congrArg (fun p : Polynomial ℤ => p.coeff 3) h
  norm_num [expectedCandidate, expectedComparator] at hc

lemma comparator_real_root_lower (r : ℝ)
    (hr : evalR expectedComparator r = 0) : -86 < r := by
  have hcast : evalC expectedComparator (r : ℂ) = 0 := by
    rw [evalC_ofReal, hr]
    simp
  have hnorm := comparator_complex_disk (r : ℂ) hcast
  rw [Complex.norm_real, Real.norm_eq_abs] at hnorm
  exact (abs_lt.mp hnorm).1

lemma negative_root_complex_norm (r : ℝ) (hr : r < -86) :
    86 < ‖(r : ℂ)‖ := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith : r < 0)]
  linarith

theorem endpoint_of_coefficients
    (hc : A candidate = expectedCandidate)
    (hj : A (J 12) = expectedComparator) : Endpoint := by
  obtain ⟨r, hrleft, hrright, hrzero⟩ := candidate_real_interval
  have hroot : evalR (A candidate) r = 0 := by simpa only [hc] using hrzero
  have hdisk : ∀ z : ℂ, evalC (A (J 12)) z = 0 → ‖z‖ < 86 := by
    intro z hz
    apply comparator_complex_disk z
    simpa only [hj] using hz
  have hne : A candidate ≠ A (J 12) := by
    simpa only [hc, hj] using expected_polynomials_ne
  have hnotreal : ¬ UniversalRealAssertion := by
    intro h
    obtain ⟨ρ, hρzero, hρmin⟩ := h 12 (by norm_num)
    have hρlower : -86 < ρ := comparator_real_root_lower ρ (by
      simpa only [hj] using hρzero)
    have hρr : ρ < r := hρmin candidate hne r hroot
    linarith
  have hnotmodulus : ¬ UniversalModulusAssertion := by
    intro h
    obtain ⟨ζ, hζzero, hζmax⟩ := h 12 (by norm_num)
    have hζsmall : ‖ζ‖ < 86 := hdisk ζ hζzero
    have hcastroot : evalC (A candidate) (r : ℂ) = 0 := by
      rw [evalC_ofReal, hroot]
      simp
    have hlarge : 86 < ‖(r : ℂ)‖ := negative_root_complex_norm r hrright
    have hle : ‖(r : ℂ)‖ ≤ ‖ζ‖ := hζmax candidate (r : ℂ) hcastroot
    linarith
  exact ⟨hc, hj, ⟨r, hrleft, hrright, hroot⟩, hdisk, hne, hnotreal, hnotmodulus⟩

end BBPSplitStar
