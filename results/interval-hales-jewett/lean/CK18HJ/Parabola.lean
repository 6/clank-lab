import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Lemmas 2 and 3 of the paper, in integer arithmetic

`f(t) = C + A t² - 2 s t` with `1 ≤ A ≤ 2Q` and `0 ≤ s ≤ A(M-1)` takes two
letters `t, u ∈ [0, M)` to different blocks' parities: `⌊f(t)/32Q⌋` and
`⌊f(u)/32Q⌋` differ in parity.
-/

namespace CK18HJ

/-- The upper side (vertex `s/A ≤ (M-1)/2`): letters `t₀ = ⌈s/A⌉` and `t₀ + i`,
with `i` the first step reaching the next block (Lemmas 2 and 3). -/
theorem parabola_upper (Q M A s C : ℤ) (K : ℕ) (hQ : 1 ≤ Q) (hK : 32 * Q ≤ (K : ℤ) * K)
    (hM : 2 * (K : ℤ) + 2 ≤ M) (hA1 : 1 ≤ A) (hA2 : A ≤ 2 * Q) (hs0 : 0 ≤ s)
    (hs : 2 * s ≤ A * (M - 1)) :
    ∃ t u : ℤ, 0 ≤ t ∧ t < M ∧ 0 ≤ u ∧ u < M ∧
      ((C + A * t ^ 2 - 2 * s * t) / (32 * Q) % 2 = 1 ↔
        ¬ (C + A * u ^ 2 - 2 * s * u) / (32 * Q) % 2 = 1) := by
  have hB : (0 : ℤ) < 32 * Q := by linarith
  -- t₀ = ⌈s/A⌉, so s ≤ A t₀ < s + A
  set t₀ := (s + A - 1) / A with ht₀
  have h1 : A * t₀ ≥ s := by
    have := (Int.ediv_lt_iff_lt_mul (b := t₀ + 1) (by linarith : (0 : ℤ) < A)).1
      (by rw [ht₀]; linarith)
    nlinarith
  have h2 : A * t₀ < s + A := by
    have := (Int.le_ediv_iff_mul_le (a := t₀) (by linarith : (0 : ℤ) < A)).1 le_rfl
    nlinarith
  have ht0 : 0 ≤ t₀ := by
    by_contra h
    push Not at h
    nlinarith
  have ht1 : 2 * t₀ ≤ M := by
    by_contra h
    push Not at h
    nlinarith
  set d := A * t₀ - s with hd
  have hd0 : 0 ≤ d := by linarith
  have hdA : d < A := by linarith
  set v : ℕ → ℤ := fun j => C + A * (t₀ + j) ^ 2 - 2 * s * (t₀ + j) with hv
  have hspan : ∀ j : ℕ, v j - v 0 = 2 * d * j + A * (j : ℤ) ^ 2 := by
    intro j; simp only [hv, hd]; push_cast; ring
  have hstep : ∀ j : ℕ, v (j + 1) - v j = 2 * d + A * (2 * j + 1) := by
    intro j; simp only [hv, hd]; push_cast; ring
  -- the block of v 0
  set k := v 0 / (32 * Q) with hk
  have hk1 : k * (32 * Q) ≤ v 0 := (Int.le_ediv_iff_mul_le hB).1 le_rfl
  have hk2 : v 0 < (k + 1) * (32 * Q) := (Int.ediv_lt_iff_lt_mul hB).1 (by linarith)
  -- the span to K reaches the next block
  have hP : ∃ j : ℕ, (k + 1) * (32 * Q) ≤ v j := by
    refine ⟨K, ?_⟩
    have := hspan K
    have : (0 : ℤ) ≤ 2 * d * K := by positivity
    nlinarith
  classical
  set i := Nat.find hP with hi
  have hvi : (k + 1) * (32 * Q) ≤ v i := Nat.find_spec hP
  have hiK : i ≤ K := Nat.find_min' hP (by
    have := hspan K
    have : (0 : ℤ) ≤ 2 * d * K := by positivity
    nlinarith)
  have hi0 : i ≠ 0 := by
    intro h0; rw [h0] at hvi; linarith
  obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [hj] at hvi hiK
  have hvj : v j < (k + 1) * (32 * Q) := by
    have := Nat.find_min hP (show j < Nat.find hP by omega)
    push Not at this; exact this
  -- A j² < 32Q, so 2Aj < 16Q and the step from j is below 32Q
  have hAj : A * (j : ℤ) ^ 2 < 32 * Q := by
    have := hspan j
    have : (0 : ℤ) ≤ 2 * d * j := by positivity
    nlinarith
  have h2Aj : 2 * A * j < 16 * Q := by
    by_contra h
    push Not at h
    have hj0 : (0 : ℤ) ≤ j := by positivity
    nlinarith [mul_le_mul h h (by positivity) (by positivity)]
  have hvi2 : v (j + 1) < (k + 2) * (32 * Q) := by
    have := hstep j
    nlinarith
  have hq : v (j + 1) / (32 * Q) = k + 1 := by
    have a := (Int.le_ediv_iff_mul_le hB).2 hvi
    have b := (Int.ediv_lt_iff_lt_mul hB).2 (show v (j + 1) < (k + 1 + 1) * (32 * Q) by linarith)
    omega
  refine ⟨t₀, t₀ + (j + 1 : ℕ), ht0, by omega, by positivity, by push_cast; omega, ?_⟩
  have e0 : C + A * t₀ ^ 2 - 2 * s * t₀ = v 0 := by simp [hv]
  have e1 : C + A * (t₀ + ((j + 1 : ℕ) : ℤ)) ^ 2 - 2 * s * (t₀ + ((j + 1 : ℕ) : ℤ)) = v (j + 1) := by
    simp [hv]
  rw [e0, e1, hq, ← hk]
  omega

/-- Both sides: the lower side is the upper side for `t ↦ M - 1 - t`. -/
theorem parabola (Q M A s C : ℤ) (K : ℕ) (hQ : 1 ≤ Q) (hK : 32 * Q ≤ (K : ℤ) * K)
    (hM : 2 * (K : ℤ) + 2 ≤ M) (hA1 : 1 ≤ A) (hA2 : A ≤ 2 * Q) (hs0 : 0 ≤ s)
    (hs : s ≤ A * (M - 1)) :
    ∃ t u : ℤ, 0 ≤ t ∧ t < M ∧ 0 ≤ u ∧ u < M ∧
      ((C + A * t ^ 2 - 2 * s * t) / (32 * Q) % 2 = 1 ↔
        ¬ (C + A * u ^ 2 - 2 * s * u) / (32 * Q) % 2 = 1) := by
  rcases le_or_gt (2 * s) (A * (M - 1)) with h | h
  · exact parabola_upper Q M A s C K hQ hK hM hA1 hA2 hs0 h
  · obtain ⟨t, u, ht0, ht1, hu0, hu1, hc⟩ :=
      parabola_upper Q M A (A * (M - 1) - s) (C + A * (M - 1) ^ 2 - 2 * s * (M - 1)) K
        hQ hK hM hA1 hA2 (by linarith) (by linarith)
    refine ⟨M - 1 - t, M - 1 - u, by omega, by omega, by omega, by omega, ?_⟩
    have e : ∀ x : ℤ, C + A * (M - 1 - x) ^ 2 - 2 * s * (M - 1 - x) =
        C + A * (M - 1) ^ 2 - 2 * s * (M - 1) + A * x ^ 2 - 2 * (A * (M - 1) - s) * x := by
      intro x; ring
    rw [e, e]; exact hc

end CK18HJ
