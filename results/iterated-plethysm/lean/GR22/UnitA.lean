import GR22.Spec

/-!
# Specialization: `AtAComplete`, `AtAPlethysm` and two anchors

`h_n[1 - x - y]` from Newton's identity (generating function `(1 - x t)(1 - y t)/(1 - t)`),
the specialization of a plethysm through the Adams operations, and the kernel-checked anchors
`h₂[h₂] = s₄ + s₂₂` and `h₃[h₂] = s₆ + s₄₂ + s₂₂₂`.
-/

noncomputable section
namespace GR22

open MvPolynomial

/-- The candidate values of `h_n[1 - x - y]`. -/
def unitA_cand (n : ℕ) : XY := if n = 0 then 1 else if n = 1 then 1 - x - y else Q

lemma unitA_atA_power (k : ℕ) : atA (power (k + 1)) = 1 - x ^ (k + 1) - y ^ (k + 1) := by
  simp [power, atA]

/-- `∑_{i < m} (1 - x^(i+1) - y^(i+1)) Q` in closed form. -/
lemma unitA_sumQ (m : ℕ) :
    ∑ i ∈ Finset.range m, (1 - x ^ (i + 1) - y ^ (i + 1)) * Q =
      (m : XY) * Q - (1 - y) * (x - x ^ (m + 1)) - (1 - x) * (y - y ^ (m + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]; push_cast; simp only [Q]; ring

/-- Newton's identity holds for the candidate sequence. -/
lemma unitA_newton (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (1 - x ^ (k + 1) - y ^ (k + 1)) * unitA_cand (n - k) =
      ((n + 1 : ℕ) : XY) * unitA_cand (n + 1) := by
  rcases n with _ | _ | m
  · simp [unitA_cand]
  · simp [Finset.sum_range_succ, unitA_cand, Q]; ring
  · rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h : ∀ k ∈ Finset.range (m + 1),
        (1 - x ^ (k + 1) - y ^ (k + 1)) * unitA_cand (m + 1 + 1 - k) =
          (1 - x ^ (k + 1) - y ^ (k + 1)) * Q := by
      intro k hk
      rw [Finset.mem_range] at hk
      have h1 : m + 1 + 1 - k ≠ 0 := by omega
      have h2 : m + 1 + 1 - k ≠ 1 := by omega
      simp [unitA_cand, h1, h2]
    rw [Finset.sum_congr rfl h, unitA_sumQ]
    have e1 : m + 1 + 1 - (m + 1) = 1 := by omega
    have e0 : m + 1 + 1 - (m + 1 + 1) = 0 := by omega
    simp only [e1, e0, unitA_cand]
    simp only [one_ne_zero, ite_false, ite_true, show m + 1 + 1 + 1 ≠ 0 by omega,
      show m + 1 + 1 + 1 ≠ 1 by omega]
    push_cast; simp only [Q]; ring

lemma unitA_atA_complete_eq (n : ℕ) : atA (complete n) = unitA_cand n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp [complete, unitA_cand]
    · rw [complete, map_mul, map_sum]
      have h : ∀ k : Fin (n + 1), atA (power (k.val + 1) * complete (n - k.val)) =
          (1 - x ^ (k.val + 1) - y ^ (k.val + 1)) * unitA_cand (n - k.val) := by
        intro k
        rw [map_mul, unitA_atA_power, ih _ (by omega)]
      rw [Finset.sum_congr rfl (fun k _ => h k),
        Fin.sum_univ_eq_sum_range (fun k => (1 - x ^ (k + 1) - y ^ (k + 1)) *
          unitA_cand (n - k)), unitA_newton]
      rw [atA, aeval_C, algebraMap_eq, ← map_natCast C, ← mul_assoc, ← map_mul]
      push_cast
      rw [inv_mul_cancel₀ (by positivity), map_one, one_mul]

theorem atA_complete : AtAComplete := by
  refine ⟨?_, ?_, fun n hn => ?_⟩
  · rw [unitA_atA_complete_eq]; rfl
  · rw [unitA_atA_complete_eq]; rfl
  · rw [unitA_atA_complete_eq, unitA_cand]
    simp [show n ≠ 0 by omega, show n ≠ 1 by omega]

/-- For `k ≥ 1`, specializing after the Adams operation `ψ^k` is `x, y ↦ x^k, y^k` after
specializing. -/
lemma unitA_atA_comp_adams (k : ℕ) (hk : 1 ≤ k) :
    atA.comp (rename (fun i : ℕ => k * (i + 1) - 1)) = (frob k).comp atA := by
  apply MvPolynomial.algHom_ext
  intro i
  have e : k * (i + 1) - 1 + 1 = k * (i + 1) := by
    have : 1 ≤ k * (i + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  simp [atA, frob, x, y, e, pow_mul]

lemma unitA_atA_adams (k : ℕ) (hk : 1 ≤ k) (g : SF) : atA (adams k g) = frob k (atA g) := by
  have := congrArg (fun φ : SF →ₐ[ℚ] XY => φ g) (unitA_atA_comp_adams k hk)
  simpa [adams] using this

theorem atA_plethysm : AtAPlethysm := by
  intro f g
  rw [plethysm, ← AlgHom.coe_toRingHom, hom_eval₂]
  congr 1
  · ext q; simp [atA]
  · funext i; simp [unitA_atA_adams (i + 1) (by omega)]

/-! ### Anchors: `h₂[h₂]` and `h₃[h₂]`, computed in the power sums -/

/-- Identities with rational coefficients are checked by `ring` after the injective map into
the fraction field. -/
abbrev unitA_K := FractionRing SF

lemma unitA_inj : Function.Injective (algebraMap SF unitA_K) := IsFractionRing.injective _ _

instance unitA_charZero : CharZero unitA_K := charZero_of_injective_algebraMap (algebraMap ℚ unitA_K).injective

lemma unitA_mapC (q : ℚ) : algebraMap SF unitA_K (C q) = (q : unitA_K) := by
  rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, eq_ratCast]

lemma unitA_complete_one : complete 1 = X 0 := by
  simp [complete, power]

lemma unitA_complete_two : complete 2 = C (1/2) * (X 0 ^ 2 + X 1) := by
  rw [complete]; simp [Fin.sum_univ_succ, power, unitA_complete_one, complete]
  apply unitA_inj; simp [unitA_mapC]; ring

lemma unitA_complete_three : complete 3 = C (1/6) * (X 0 ^ 3 + 3 * X 0 * X 1 + 2 * X 2) := by
  rw [complete]; simp [Fin.sum_univ_succ, power, unitA_complete_one, unitA_complete_two, complete]
  apply unitA_inj; simp [unitA_mapC, map_ofNat]; ring

lemma unitA_complete_four : complete 4 =
    C (1/24) * (X 0 ^ 4 + 6 * X 0 ^ 2 * X 1 + 3 * X 1 ^ 2 + 8 * X 0 * X 2 + 6 * X 3) := by
  rw [complete]
  simp [Fin.sum_univ_succ, power, unitA_complete_one, unitA_complete_two, unitA_complete_three,
    complete]
  apply unitA_inj; simp [unitA_mapC, map_ofNat]; ring

lemma unitA_complete_five : complete 5 =
    C (1/120) * (X 0 ^ 5 + 10 * X 0 ^ 3 * X 1 + 15 * X 0 * X 1 ^ 2 + 20 * X 0 ^ 2 * X 2 +
      20 * X 1 * X 2 + 30 * X 0 * X 3 + 24 * X 4) := by
  rw [complete]
  simp [Fin.sum_univ_succ, power, unitA_complete_one, unitA_complete_two, unitA_complete_three,
    unitA_complete_four, complete]
  apply unitA_inj; simp [unitA_mapC, map_ofNat]; ring

lemma unitA_complete_six : complete 6 =
    C (1/720) * (X 0 ^ 6 + 15 * X 0 ^ 4 * X 1 + 45 * X 0 ^ 2 * X 1 ^ 2 + 15 * X 1 ^ 3 +
      40 * X 0 ^ 3 * X 2 + 120 * X 0 * X 1 * X 2 + 40 * X 2 ^ 2 + 90 * X 0 ^ 2 * X 3 +
      90 * X 1 * X 3 + 144 * X 0 * X 4 + 120 * X 5) := by
  rw [complete]
  simp [Fin.sum_univ_succ, power, unitA_complete_one, unitA_complete_two, unitA_complete_three,
    unitA_complete_four, unitA_complete_five, complete]
  apply unitA_inj; simp [unitA_mapC, map_ofNat]; ring

lemma unitA_schur_one (a : ℕ) : schur [a] = completeZ a := by
  unfold schur; erw [Matrix.det_fin_one]; simp

lemma unitA_schur_two (a b : ℕ) :
    schur [a, b] = completeZ a * completeZ b - completeZ (a + 1) * completeZ (b - 1) := by
  unfold schur; erw [Matrix.det_fin_two]; simp

lemma unitA_schur_222 : schur [2, 2, 2] =
    complete 2 * (complete 2 * complete 2 - complete 3 * complete 1) -
      complete 3 * (complete 1 * complete 2 - complete 3) +
      complete 4 * (complete 1 * complete 1 - complete 2) := by
  unfold schur; erw [Matrix.det_fin_three]
  simp [completeZ, complete]
  ring

lemma unitA_completeZ_ofNat (n : ℕ) : completeZ n = complete n := by simp [completeZ]


theorem anchor_h2_h2 : plethysm (complete 2) (complete 2) = schur [4] + schur [2, 2] := by
  rw [unitA_schur_one, unitA_schur_two]
  simp [plethysm, completeZ, adams, unitA_complete_one, unitA_complete_two, unitA_complete_three,
    unitA_complete_four]
  apply unitA_inj; simp [unitA_mapC, map_ofNat]; ring

theorem anchor_h3_h2 :
    plethysm (complete 3) (complete 2) = schur [6] + schur [4, 2] + schur [2, 2, 2] := by
  rw [unitA_schur_one, unitA_schur_two, unitA_schur_222]
  simp [plethysm, completeZ, adams, unitA_complete_one, unitA_complete_two, unitA_complete_three,
    unitA_complete_four, unitA_complete_five, unitA_complete_six]
  apply unitA_inj; simp [unitA_mapC, map_ofNat]; ring

end GR22

#print axioms GR22.atA_complete
#print axioms GR22.atA_plethysm
#print axioms GR22.anchor_h2_h2
#print axioms GR22.anchor_h3_h2
