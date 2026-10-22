import EKG3.SieveWeight

/-! A refinement of the published OAI sieve: two distinct reduced fractions
with denominator at most Q are separated by 1/(Q²-1) for Q >= 2.
The phase/duality step uses the unchanged published finite Hilbert proof. -/
namespace EKG3
open scoped BigOperators
open OAI.Ostmann

theorem reduced_fraction_circle_separation_refined (Q q r h k : ℕ)
    (hQ : 2 ≤ Q) (hq : 0 < q) (hr : 0 < r) (hqQ : q ≤ Q) (hrQ : r ≤ Q)
    (hh : h < q) (hk : k < r) (hc : h.Coprime q) (kc : k.Coprime r)
    (hne : (q, h) ≠ (r, k)) (m : ℤ) :
    1 / ((Q : ℝ)^2 - 1) ≤ |(h : ℝ) / q - (k : ℝ) / r - m| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hden : 0 < (Q : ℝ)^2 - 1 := by nlinarith
  let t : ℝ := (h : ℝ) / q - (k : ℝ) / r - m
  have ht : t ≠ 0 := by
    have hs := reduced_fraction_circle_separation Q q r h k hq hr hqQ hrQ hh hk hc kc hne m
    have hpos : (0 : ℝ) < 1 / (Q : ℝ)^2 := by positivity
    intro he
    change 1 / (Q : ℝ)^2 ≤ |t| at hs
    rw [he, abs_zero] at hs
    linarith
  by_cases hqr : q = r
  · let z : ℤ := (h : ℤ) - k - m * q
    have hz : (z : ℝ) = (q : ℝ) * t := by
      dsimp [z, t]
      rw [← hqr]
      push_cast
      field_simp
    have hz0 : z ≠ 0 := by
      intro he
      rw [he, Int.cast_zero] at hz
      exact ht ((mul_eq_zero.mp hz.symm).resolve_left hqR.ne')
    have hz1 : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast Int.one_le_abs hz0
    rw [hz, abs_mul, abs_of_pos hqR] at hz1
    have hqle : (q : ℝ) ≤ (Q : ℝ)^2 - 1 := by
      have hqQ' : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
      nlinarith
    have hb := mul_le_mul_of_nonneg_right hqle (abs_nonneg t)
    apply (div_le_iff₀ hden).mpr
    nlinarith
  · let z : ℤ := (h : ℤ) * r - (k : ℤ) * q - m * q * r
    have hz : (z : ℝ) = (q : ℝ) * r * t := by
      dsimp [z, t]
      push_cast
      field_simp
    have hz0 : z ≠ 0 := by
      intro he
      rw [he, Int.cast_zero] at hz
      exact ht ((mul_eq_zero.mp hz.symm).resolve_left (mul_ne_zero hqR.ne' hrR.ne'))
    have hz1 : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast Int.one_le_abs hz0
    rw [hz, abs_mul, abs_mul, abs_of_pos hqR, abs_of_pos hrR] at hz1
    have hprodN : q * r + 1 ≤ Q * Q := by
      by_cases hqtop : q = Q
      · have hrlt : r + 1 ≤ Q := by omega
        nlinarith
      · have hqlt : q + 1 ≤ Q := by omega
        nlinarith
    have hprodR : (q : ℝ) * r + 1 ≤ (Q : ℝ)^2 := by exact_mod_cast (show q * r + 1 ≤ Q ^ 2 by nlinarith [hprodN])
    have hb := mul_le_mul_of_nonneg_right (by linarith : (q : ℝ)*r ≤ (Q : ℝ)^2-1)
      (abs_nonneg t)
    apply (div_le_iff₀ hden).mpr
    nlinarith

theorem reducedFractionPoint_separated_refined (Q : ℕ) (hQ : 2 ≤ Q) :
    CircleSeparated (reducedFractionPoint Q) (1 / ((Q : ℝ)^2 - 1)) := by
  intro s t hst m
  rcases s with ⟨⟨q, hq⟩, ⟨h, hh⟩⟩
  rcases t with ⟨⟨r, hr⟩, ⟨k, hk⟩⟩
  simp only [Finset.mem_Icc] at hq hr
  simp only [reducedNumerators, Finset.mem_filter, Finset.mem_range] at hh hk
  have hne : (q, h) ≠ (r, k) := by
    intro he
    have hqr := congrArg Prod.fst he
    have hhk := congrArg Prod.snd he
    dsimp at hqr hhk
    subst r
    subst k
    exact hst rfl
  exact reduced_fraction_circle_separation_refined Q q r h k hQ (by omega) (by omega)
    hq.2 hr.2 hh.1 hk.1 hh.2 hk.2 hne m

theorem publishedAdditiveLargeSieve_refined (M Q : ℕ) (hQ : 2 ≤ Q)
    (J : ℤ) (c : Fin M → ℂ) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ h ∈ reducedNumerators q, ‖additiveSieveSum c J q h‖^2) ≤
      ((M : ℝ) + (Q : ℝ)^2 - 1) * ∑ n, ‖c n‖^2 := by
  classical
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hδ : 0 < 1 / ((Q : ℝ)^2 - 1) := by apply one_div_pos.mpr; nlinarith
  have h := separated_additive_sieve (reducedFractionPoint Q) (1 / ((Q : ℝ)^2 - 1))
    hδ (reducedFractionPoint_separated_refined Q hQ) M (J : ℝ) c
  have hconst : 1 / (1 / ((Q : ℝ)^2 - 1)) = (Q : ℝ)^2 - 1 := by field_simp
  rw [hconst] at h
  change (∑ s : ReducedFractionIndex Q,
    ‖∑ n, c n * sieveHalfPhase (2 * ((J : ℝ) + (n.val : ℝ)) *
      ((s.2.val : ℝ) / s.1.val))‖^2) ≤ _ at h
  rw [reducedFraction_sum Q (fun q h =>
    ‖∑ n, c n * sieveHalfPhase (2 * ((J : ℝ) + (n.val : ℝ)) *
      ((h : ℝ) / q))‖^2)] at h
  simpa only [additiveSieveSum, sieveAdditivePhase_eq_half, add_sub_assoc] using h

end EKG3
