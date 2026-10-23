import CubelikeSC.Characters

/-!
# Spectral identities

For `S ⊆ V` with `n = |S|` and `σ = Σ_{s∈S} s`:
`λ_a = n - 2 Σ_s (a·s)`, `|λ_a| ≤ n`, `λ_0 = n`, `λ_a ≡ n - 2(a·σ) (mod 4)`,
`σ ∈ K(S)`, `K(S)` is closed under addition, and `Σ_a λ_a² = 128 n`.
-/

namespace CubelikeSC

variable (S : Finset V)

/-- `σ = Σ_{s∈S} s`. -/
def sigma : V := ∑ s ∈ S, s

lemma lam_eq (a : V) : lam S a = S.card - 2 * ∑ s ∈ S, ((a ⬝ᵥ s).val : ℤ) := by
  unfold lam
  simp only [neg_one_pow_val_eq, Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum]
  simp

lemma lam_zero : lam S 0 = S.card := by
  simp [lam]

lemma abs_lam_le (a : V) : |lam S a| ≤ S.card := by
  unfold lam
  calc |∑ s ∈ S, ((-1 : ℤ) ^ (a ⬝ᵥ s).val)| ≤ ∑ s ∈ S, |((-1 : ℤ) ^ (a ⬝ᵥ s).val)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = S.card := by simp

/-- The sum of the `(a·s).val` is `a·σ` in `ZMod 2`. -/
lemma cast_sum_val (a : V) :
    ((∑ s ∈ S, (a ⬝ᵥ s).val : ℕ) : ZMod 2) = a ⬝ᵥ sigma S := by
  simp [sigma, dotProduct_sum, ZMod.natCast_val]

/-- Lemma 2, `mod 4` part: `λ_a ≡ n - 2(a·σ) (mod 4)`. -/
lemma lam_mod4 (a : V) : lam S a ≡ S.card - 2 * ((a ⬝ᵥ sigma S).val : ℤ) [ZMOD 4] := by
  have h := cast_sum_val S a
  rw [← ZMod.natCast_zmod_val (a ⬝ᵥ sigma S), ZMod.natCast_eq_natCast_iff'] at h
  have hv : (a ⬝ᵥ sigma S).val < 2 := ZMod.val_lt _
  rw [lam_eq]
  have h2 : ((∑ s ∈ S, (a ⬝ᵥ s).val : ℕ) : ℤ) ≡ ((a ⬝ᵥ sigma S).val : ℤ) [ZMOD 2] := by
    rw [Int.ModEq]; exact_mod_cast h
  push_cast at h2
  have := Int.ModEq.mul_left' (c := 2) h2
  rw [show (2 : ℤ) * 2 = 4 by norm_num] at this
  exact Int.ModEq.sub_left _ this

lemma mem_K {g : V} : g ∈ K S ↔ ∀ a b : V, lam S a = lam S b → a ⬝ᵥ g = b ⬝ᵥ g := by
  simp [K]

/-- Lemma 2: `σ ∈ K(S)`. -/
lemma sigma_mem_K : sigma S ∈ K S := by
  rw [mem_K]
  intro a b hab
  rw [lam_eq, lam_eq] at hab
  have h : (∑ s ∈ S, (a ⬝ᵥ s).val : ℕ) = ∑ s ∈ S, (b ⬝ᵥ s).val := by
    have : (∑ s ∈ S, ((a ⬝ᵥ s).val : ℤ)) = ∑ s ∈ S, ((b ⬝ᵥ s).val : ℤ) := by linarith
    exact_mod_cast this
  rw [← cast_sum_val, ← cast_sum_val, h]

/-- Lemma 1. -/
lemma zero_mem_K : (0 : V) ∈ K S := by
  rw [mem_K]; intro a b _; simp

lemma add_mem_K {g g' : V} (hg : g ∈ K S) (hg' : g' ∈ K S) : g + g' ∈ K S := by
  rw [mem_K] at *
  intro a b hab
  rw [dotProduct_add, dotProduct_add, hg a b hab, hg' a b hab]

/-- Lemma 8 (Parseval): `Σ_a λ_a² = 128 n`. -/
lemma parseval : ∑ a : V, (lam S a) ^ 2 = 128 * S.card := by
  have hsq : ∀ a : V, (lam S a) ^ 2 =
      ∑ s ∈ S, ∑ s' ∈ S, ((-1 : ℤ) ^ (a ⬝ᵥ (s + s')).val) := by
    intro a
    rw [sq, lam, Finset.sum_mul_sum]
    simp [dotProduct_add, neg_one_pow_val_add]
  simp only [hsq]
  rw [Finset.sum_comm]
  have hin : ∀ s ∈ S, ∑ a : V, ∑ s' ∈ S, ((-1 : ℤ) ^ (a ⬝ᵥ (s + s')).val) = 128 := by
    intro s hs
    rw [Finset.sum_comm]
    have : ∀ s', ∑ a : V, ((-1 : ℤ) ^ (a ⬝ᵥ (s + s')).val) = if s' = s then 128 else 0 := by
      intro s'
      rw [sum_char]
      by_cases h : s' = s
      · subst h; simp [add_eq_zero_iff_eq']
      · have h' : ¬ (s + s' = 0) := by rw [add_eq_zero_iff_eq']; exact Ne.symm h
        simp [h, h']
    rw [Finset.sum_congr rfl (fun s' _ => this s')]
    simp [hs]
  rw [Finset.sum_congr rfl hin]
  simp [mul_comm]

end CubelikeSC
