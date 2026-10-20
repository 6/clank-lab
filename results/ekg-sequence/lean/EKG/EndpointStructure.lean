import EKG.EndpointDefinitions
import EKG.PartA
import EKG.PartB
import EKG.SmoothedPositions

/-! Structural transfer to the one-based, odd-prime-only smoothing.
The ordinary branch uses the pre-occurrence frontier. That frontier is
unchanged by the occurrence unless the occurrence equals it exactly.
Consequently Part A at the post-occurrence prefix and Part B at the
pre-occurrence prefix have exactly the same frontier scale; no logarithmic
rate comparison or extra constant is needed. -/
namespace EKG.CanonicalEndpoint

/-- The new smoothing differs from the archive smoothing only at 2 and 6. -/
theorem smoothValue_eq_archive {m : ℕ} (hm2 : m ≠ 2) (hm6 : m ≠ 6) :
    smoothValue m = EKG.smoothValue m := by
  by_cases hp : m.Prime
  · simp [smoothValue, EKG.smoothValue, hp, hm2]
  · by_cases ht : (m / 3).Prime ∧ m = 3 * (m / 3)
    · have ht2 : m / 3 ≠ 2 := by
        intro he
        apply hm6
        omega
      have hnew : (m / 3).Prime ∧ m / 3 ≠ 2 ∧ m = 3 * (m / 3) :=
        ⟨ht.1, ht2, ht.2⟩
      simp only [smoothValue, EKG.smoothValue,
        if_neg (show ¬ (m.Prime ∧ m ≠ 2) from fun h => hp h.1),
        if_neg hp, if_pos ht, if_pos hnew]
    · have ht' : ¬ ((m / 3).Prime ∧ m / 3 ≠ 2 ∧ m = 3 * (m / 3)) := by
        rintro ⟨hprime, _, heq⟩
        exact ht ⟨hprime, heq⟩
      simp only [smoothValue, EKG.smoothValue, if_neg hp,
        show ¬ (m.Prime ∧ m ≠ 2) from fun h => hp h.1,
        if_false, if_neg ht, if_neg ht']

/-- The first smoothing branch applies to every odd prime. -/
theorem smoothValue_of_odd_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    smoothValue p = 2 * p := by
  simp [smoothValue, hp, hp2]

/-- The second smoothing branch applies to three times every odd prime. -/
theorem smoothValue_of_odd_prime_tick {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    smoothValue (3 * p) = 2 * p := by
  have hpge := hp.two_le
  have htwo : 3 * p ≠ 2 := by omega
  have hsix : 3 * p ≠ 6 := by omega
  rw [smoothValue_eq_archive htwo hsix]
  exact EKG.smoothValue_of_three_mul_prime hp

/-- The exceptional raw values occur at one-based positions 2 and 4 only. -/
theorem b_eq_archive_smoothing {n : ℕ} (hn : 5 ≤ n) :
    b n = EKG.smoothValue (canonical.a (n - 1)) := by
  have hm2 : canonical.a (n - 1) ≠ 2 := by
    intro he
    have hi := canonical.injective (he.trans canonical.seed_one.symm)
    omega
  have hsix : canonical.a 3 = 6 := by
    simpa [FiniteBase.value] using
      (FiniteBase.first_thirteen canonical (n := 3) (by omega))
  have hm6 : canonical.a (n - 1) ≠ 6 := by
    intro he
    have hi := canonical.injective (he.trans hsix.symm)
    omega
  exact smoothValue_eq_archive hm2 hm6

/-- Adding a value different from the least unused even leaves that even
least and unused. The small-index guard makes subtraction exact. -/
theorem frontier_post_eq_pre {i : ℕ} (hi : 1 ≤ i)
    (hne : canonical.a i ≠ frontier canonical (i - 1)) :
    frontier canonical i = frontier canonical (i - 1) := by
  apply Nat.le_antisymm
  · have hs := frontier_spec canonical (i - 1)
    apply frontier_le canonical i _ hs.1 hs.2.1
    rintro ⟨j, hj, he⟩
    by_cases hji : j = i
    · subst j
      exact hne he
    · apply hs.2.2
      exact ⟨j, by omega, he⟩
  · exact frontier_monotone canonical (by omega)

/-- Actual A and B give a uniform ordinary-position little-o estimate at
the pre-occurrence frontier. This has no count or localization hypothesis. -/
theorem eventual_ordinary_proximity (delta : ℝ) (hdelta : 0 < delta) :
    ∃ N : ℕ, ∀ i : ℕ, N ≤ i →
      1 < canonical.a i → ¬ (canonical.a i).Prime →
      ¬ spanTickValue (canonical.a i) →
      |(canonical.a i : ℝ) - (frontier canonical (i - 1) : ℝ)| ≤
        delta * logRate (frontier canonical (i - 1)) := by
  obtain ⟨NA, hA⟩ := PartA.canonical_upper_excursion delta hdelta
  obtain ⟨NB, hB⟩ := PartB.canonical_missing_composite delta hdelta
  refine ⟨NA + NB + 4, ?_⟩
  intro i hi hbig hcomp hnt
  have hi4 : 4 ≤ i := by omega
  have he4 := frontier_ge_four canonical (t := i - 1) (by omega)
  have he1 : (1 : ℝ) < (frontier canonical (i - 1) : ℝ) := by
    exact_mod_cast (show 1 < frontier canonical (i - 1) by omega)
  have hR : 0 ≤ delta * logRate (frontier canonical (i - 1)) := by
    unfold logRate
    exact mul_nonneg hdelta.le (div_nonneg (by positivity)
      (Real.log_pos he1).le)
  apply abs_le.mpr
  constructor
  · by_cases hbelow : canonical.a i < frontier canonical (i - 1)
    · have hfree : ¬ UsedBefore canonical.a (i - 1 + 1) (canonical.a i) := by
        simpa only [show i - 1 + 1 = i by omega] using term_unused canonical i
      have hb := hB (i - 1) (by omega) (canonical.a i) (by omega)
        hcomp hbelow hfree
      have hb' : (frontier canonical (i - 1) : ℝ) - (canonical.a i : ℝ) <
          delta * logRate (frontier canonical (i - 1)) := by
        simpa only [logRate, ← mul_div_assoc] using hb
      linarith
    · have hlo : (frontier canonical (i - 1) : ℝ) ≤ (canonical.a i : ℝ) := by
        exact_mod_cast (Nat.le_of_not_gt hbelow)
      linarith
  · by_cases heq : canonical.a i = frontier canonical (i - 1)
    · rw [heq, sub_self]
      exact hR
    · have hf := frontier_post_eq_pre (by omega : 1 ≤ i) heq
      have ha := hA i (by omega)
      rw [hf] at ha
      have ha' : max ((nonTickTop canonical i : ℝ) -
          (frontier canonical (i - 1) : ℝ)) 0 ≤
          delta * logRate (frontier canonical (i - 1)) := by
        simpa only [logRate, ← mul_div_assoc] using ha
      have htop : (canonical.a i : ℝ) ≤ (nonTickTop canonical i : ℝ) := by
        exact_mod_cast nonTick_le_top canonical (i := i) le_rfl hnt
      have hmax := le_max_left ((nonTickTop canonical i : ℝ) -
        (frontier canonical (i - 1) : ℝ)) (0 : ℝ)
      linarith

/-- Every sufficiently late one-based position is within little-o of an
actual frontier at one of the three fixed shifts 2, 3, 4. Odd prime and
odd-prime tick branches are equalities, by the proved prime blocks. -/
theorem eventual_frontier_proxy (delta : ℝ) (hdelta : 0 < delta) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ j : ℕ,
      2 ≤ j ∧ j ≤ 4 ∧
      |(b n : ℝ) - (frontier canonical (n - j) : ℝ)| ≤
        delta * logRate (frontier canonical (n - j)) := by
  obtain ⟨N, hN⟩ := eventual_ordinary_proximity delta hdelta
  refine ⟨N + 10, ?_⟩
  intro n hn
  have hn10 : 10 ≤ n := by omega
  have hsmooth := b_eq_archive_smoothing (n := n) (by omega)
  rcases canonical.smoothed_position_cases (n := n - 1) (by omega) with ho | hf
  · refine ⟨2, by omega, by omega, ?_⟩
    rw [hsmooth, ho.2.2.2]
    have hnear := hN (n - 1) (by omega) ho.1 ho.2.1 ho.2.2.1
    simpa only [show n - 1 - 1 = n - 2 by omega] using hnear
  · rcases hf with hf | hf
    · refine ⟨3, by omega, by omega, ?_⟩
      rw [hsmooth, hf, show n - 1 - 2 = n - 3 by omega, sub_self, abs_zero]
      unfold logRate
      have he4 := frontier_ge_four canonical (t := n - 3) (by omega)
      have he1 : (1 : ℝ) < (frontier canonical (n - 3) : ℝ) := by
        exact_mod_cast (show 1 < frontier canonical (n - 3) by omega)
      exact mul_nonneg hdelta.le (div_nonneg (by positivity) (Real.log_pos he1).le)
    · refine ⟨4, by omega, by omega, ?_⟩
      rw [hsmooth, hf, show n - 1 - 3 = n - 4 by omega, sub_self, abs_zero]
      unfold logRate
      have he4 := frontier_ge_four canonical (t := n - 4) (by omega)
      have he1 : (1 : ℝ) < (frontier canonical (n - 4) : ℝ) := by
        exact_mod_cast (show 1 < frontier canonical (n - 4) by omega)
      exact mul_nonneg hdelta.le (div_nonneg (by positivity) (Real.log_pos he1).le)

end EKG.CanonicalEndpoint
