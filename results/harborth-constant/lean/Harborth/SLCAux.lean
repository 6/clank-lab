import Harborth.DSH

/-! Auxiliary lemmas for the Symmetric Layer Criterion. -/

open Finset
open scoped Pointwise

namespace Harborth

/-- Intermediate value lemma for sums of bounded sequences. -/
lemma exists_interval_sum (lo hi : ℕ → ℕ) (hl : ∀ i, lo i ≤ hi i) :
    ∀ (n T : ℕ), ∑ i ∈ range n, lo i ≤ T → T ≤ ∑ i ∈ range n, hi i →
      ∃ h : ℕ → ℕ, (∀ i, lo i ≤ h i ∧ h i ≤ hi i) ∧ ∑ i ∈ range n, h i = T := by
  intro n
  induction n with
  | zero =>
    intro T h1 h2
    simp only [Finset.sum_range_zero] at *
    exact ⟨lo, fun i => ⟨le_rfl, hl i⟩, by omega⟩
  | succ n ih =>
    intro T h1 h2
    rw [sum_range_succ] at h1 h2
    have hlh : ∑ i ∈ range n, lo i ≤ ∑ i ∈ range n, hi i := sum_le_sum fun i _ => hl i
    obtain ⟨h, hh, hs⟩ := ih (T - max (lo n) (T - ∑ i ∈ range n, hi i)) (by omega) (by omega)
    refine ⟨fun i => if i = n then max (lo n) (T - ∑ i ∈ range n, hi i) else h i, ?_, ?_⟩
    · intro i
      by_cases hi' : i = n
      · subst hi'
        simp only [ite_true]
        have := hl i
        omega
      · simp only [hi', ite_false]; exact hh i
    · rw [sum_range_succ]
      have : ∑ i ∈ range n, (if i = n then max (lo n) (T - ∑ i ∈ range n, hi i) else h i)
          = ∑ i ∈ range n, h i :=
        sum_congr rfl (fun i hi => by simp [(mem_range.1 hi).ne])
      rw [this, hs]
      simp only [ite_true]
      omega

/-- Iterated Cauchy–Davenport over layers, using Dias da Silva–Hamidoune on each. -/
lemma layers_cover {p : ℕ} [Fact p.Prime] (L : ℕ → Finset (ZMod p)) (h : ℕ → ℕ)
    (hh : ∀ i, h i ≤ (L i).card) :
    ∀ n, ∃ Z : Finset (ZMod p),
      min p (∑ i ∈ range n, h i * ((L i).card - h i) + 1) ≤ Z.card ∧
      ∀ z ∈ Z, ∃ B : ℕ → Finset (ZMod p), (∀ i, i < n → B i ⊆ L i ∧ (B i).card = h i) ∧
        ∑ i ∈ range n, ∑ x ∈ B i, x = z := by
  intro n
  induction n with
  | zero =>
    refine ⟨{0}, ?_, ?_⟩
    · simp
    · intro z hz
      refine ⟨fun _ => ∅, fun i hi => absurd hi (Nat.not_lt_zero _), ?_⟩
      simp at hz
      simp [hz]
  | succ n ih =>
    obtain ⟨Z, hZ, hZB⟩ := ih
    have hp : p.Prime := Fact.out
    have hSc := dsh (L n) (h n) (hh n)
    have hZpos : 0 < Z.card :=
      lt_of_lt_of_le (lt_min hp.pos (Nat.succ_pos _)) hZ
    have hSpos : 0 < (((L n).powersetCard (h n)).image (fun B => ∑ x ∈ B, x)).card :=
      lt_of_lt_of_le (lt_min hp.pos (Nat.succ_pos _)) hSc
    have hcd := ZMod.cauchy_davenport hp (Finset.card_pos.1 hZpos) (Finset.card_pos.1 hSpos)
    refine ⟨Z + ((L n).powersetCard (h n)).image (fun B => ∑ x ∈ B, x), ?_, ?_⟩
    · rw [sum_range_succ]
      generalize ∑ i ∈ range n, h i * ((L i).card - h i) = W at *
      generalize h n * ((L n).card - h n) = w at *
      generalize (((L n).powersetCard (h n)).image (fun B => ∑ x ∈ B, x)).card = s at *
      generalize Z.card = c at *
      omega
    · intro z hz
      obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 hz
      obtain ⟨B, hB, hBs⟩ := hZB x hx
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hy
      rw [mem_powersetCard] at hC
      refine ⟨fun i => if i = n then C else B i, ?_, ?_⟩
      · intro i hi
        by_cases hin : i = n
        · subst hin; simpa using hC
        · simp only [hin, ite_false]; exact hB i (by omega)
      · rw [sum_range_succ]
        have : ∑ i ∈ range n, ∑ x ∈ (if i = n then C else B i), x = ∑ i ∈ range n, ∑ x ∈ B i, x :=
          sum_congr rfl (fun i hi => by simp [(mem_range.1 hi).ne])
        rw [this, hBs]
        simp

lemma half_mul (x h : ℕ) (h1 : x / 2 ≤ h) (h2 : h ≤ (x + 1) / 2) : h * (x - h) = x ^ 2 / 4 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' x
  · have : h = k := by omega
    subst this
    have e1 : 2 * h - h = h := by omega
    have e2 : (2 * h) ^ 2 = 4 * (h * h) := by ring
    rw [e1, e2]; omega
  · have e2 : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    rw [e2]
    have : h = k ∨ h = k + 1 := by omega
    rcases this with rfl | rfl
    · have : 2 * h + 1 - h = h + 1 := by omega
      rw [this]; omega
    · have : 2 * k + 1 - (k + 1) = k := by omega
      rw [this, mul_comm]; omega

end Harborth
