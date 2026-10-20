import SolutionEndpoint

-- Consequences of the main theorem for the sign of a(n) - n and for
-- Jasinski's three lines. The positive source imports only proved sources.

open EKG.CanonicalEndpoint

namespace EKG.Corollaries

/-- Eventually n < b(n) ≤ (1 + η) n. -/
theorem b_window (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (n : ℝ) < b n ∧ (b n : ℝ) ≤ (1 + η) * n := by
  obtain ⟨N₁, hN₁3, hN₁⟩ := ekg_sharp_all_index (1 / 6) (by norm_num)
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge (Real.exp (1 / (2 * η)))
  refine ⟨max N₁ N₂, le_trans hN₁3 (le_max_left _ _), fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have h1 := hN₁ n hn1
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast le_trans hN₁3 hn1
  have hnpos : (0 : ℝ) < n := by linarith
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  have hq : 0 < (n : ℝ) / Real.log n := div_pos hnpos hlog
  have e3 : (n : ℝ) / (3 * Real.log n) = (1 / 3) * ((n : ℝ) / Real.log n) := by
    field_simp
  rw [e3] at h1
  have habs := abs_le.mp h1
  constructor
  · nlinarith [habs.1]
  · have hexp : Real.exp (1 / (2 * η)) ≤ n :=
      le_trans hN₂ (by exact_mod_cast hn2)
    have hL : 1 / (2 * η) ≤ Real.log n := by
      have := Real.log_le_log (Real.exp_pos _) hexp
      rwa [Real.log_exp] at this
    have h2η : 1 ≤ 2 * η * Real.log n := by
      have h := mul_le_mul_of_nonneg_left hL (by linarith : (0 : ℝ) ≤ 2 * η)
      have hc : 2 * η * (1 / (2 * η)) = 1 := by field_simp
      linarith
    have hnl : (n : ℝ) / Real.log n ≤ 2 * η * n := by
      rw [div_le_iff₀ hlog]
      nlinarith
    nlinarith [habs.2]

/-- The arithmetic facts used for the sign and the three lines. -/
theorem eventual_branch_facts :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((a n).Prime → n < 2 * a n ∧ 3 * (2 * a n) ≤ 4 * n) ∧
      (¬ (a n).Prime → n < a n ∧ 2 * a n ≠ 3 * n) := by
  obtain ⟨N, hN3, hN⟩ := b_window (1 / 3) (by norm_num)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hlo, hhi⟩ := hN n hn
  have hn3 : 3 ≤ n := le_trans hN3 hn
  have hlo' : n < b n := by exact_mod_cast hlo
  have hhi' : 3 * b n ≤ 4 * n := by
    have : ((3 * b n : ℕ) : ℝ) ≤ ((4 * n : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  simp only [b] at hlo' hhi'
  unfold EKG.CanonicalEndpoint.smoothValue at hlo' hhi'
  by_cases h2 : a n = 2
  · rw [h2] at hlo'
    norm_num at hlo'
    omega
  split_ifs at hlo' hhi' with h1 h3
  · exact ⟨fun _ => by omega, fun hp => absurd h1.1 hp⟩
  · refine ⟨fun hp => absurd ⟨hp, h2⟩ h1, fun _ => by omega⟩
  · refine ⟨fun hp => absurd ⟨hp, h2⟩ h1, fun _ => by omega⟩

end EKG.Corollaries

open EKG.Corollaries

/-- For all sufficiently large n, a(n) < n when a(n) is prime and a(n) > n
when it is not (Ordowski's conjecture on A064413, in eventual form). -/
theorem ekg_eventual_sign :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((a n).Prime → a n < n) ∧ (¬ (a n).Prime → n < a n) := by
  obtain ⟨N, hN⟩ := eventual_branch_facts
  refine ⟨N, fun n hn => ⟨fun hp => ?_, fun hp => (hN n hn).2 hp |>.1⟩⟩
  have := (hN n hn).1 hp
  omega

/-- Jasinski's three lines on A152458 and A152519 hold at finitely many
indices. -/
theorem ekg_jasinski_finite :
    {k : ℕ | 0 < k ∧ 2 * a k = k}.Finite ∧
    {k : ℕ | 0 < k ∧ a k = k}.Finite ∧
    {k : ℕ | 0 < k ∧ 2 * a k = 3 * k}.Finite := by
  obtain ⟨N, hN⟩ := eventual_branch_facts
  have key : ∀ k : ℕ, N ≤ k → 2 * a k ≠ k ∧ a k ≠ k ∧ 2 * a k ≠ 3 * k := by
    intro k hk
    by_cases hp : (a k).Prime
    · have := (hN k hk).1 hp
      omega
    · have := (hN k hk).2 hp
      omega
  refine ⟨(Set.finite_lt_nat N).subset ?_, (Set.finite_lt_nat N).subset ?_,
    (Set.finite_lt_nat N).subset ?_⟩ <;>
  · intro k hk
    simp only [Set.mem_ofPred_eq] at hk ⊢
    by_contra hlt
    have := key k (by omega)
    omega

/-- The indices of A155549 and A064420 form finite sets. -/
theorem ekg_exceptional_finite :
    {n : ℕ | 0 < n ∧ ¬ (a n).Prime ∧ a n ≤ n - 1}.Finite ∧
    {k : ℕ | 0 < k ∧ a (k + 1) = k}.Finite := by
  obtain ⟨N, hN⟩ := eventual_branch_facts
  refine ⟨(Set.finite_lt_nat (N + 1)).subset ?_, (Set.finite_lt_nat (N + 4)).subset ?_⟩
  · intro n hn
    simp only [Set.mem_ofPred_eq] at hn ⊢
    by_contra hlt
    have := ((hN n (by omega)).2 hn.2.1).1
    omega
  · intro k hk
    simp only [Set.mem_ofPred_eq] at hk ⊢
    by_contra hlt
    by_cases hp : (a (k + 1)).Prime
    · have := (hN (k + 1) (by omega)).1 hp
      omega
    · have := ((hN (k + 1) (by omega)).2 hp).1
      omega
