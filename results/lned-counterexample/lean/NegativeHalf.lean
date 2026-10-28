import FieldClaim

namespace LNEDExtension
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

/-- Translation by half; this is an actual K-algebra automorphism. -/
noncomputable def translateHalf : K[X] ≃ₐ[K] K[X] := algEquivAevalXAddC (1 / 2 : K)
noncomputable def negativeHalfIdeal : Ideal K[X] :=
  Ideal.span {(X : K[X]) * (X + C (1 / 2 : K))}
noncomputable def negativeHalfImage : Set K[X] :=
  diff 1 '' ((negativeHalfIdeal : Ideal K[X]) : Set K[X])

/-- Exact translated-power endpoint, with actual ideal-image nonmembership. -/
def NegativeHalfEndpoint (K : Type*) [Field K] [CharZero K] : Prop :=
  (∀ m : ℕ, 1 ≤ m → ((X + C (1 / 2 : K)) ^ 2) ^ m ∈ negativeHalfImage) ∧
  (∀ m : ℕ, 1 ≤ m → (X + C (1 / 2 : K)) * ((X + C (1 / 2 : K)) ^ 2) ^ m ∉ negativeHalfImage) ∧
  ¬ Mathieu (negativeHalfImage : Set K[X])

lemma translateHalf_apply (p : K[X]) : translateHalf p = p.comp (X + C (1 / 2 : K)) := rfl
lemma translateHalf_X : translateHalf (X : K[X]) = X + C (1 / 2 : K) := by
  rw [translateHalf_apply, X_comp]

lemma translateHalf_diff (p : K[X]) : translateHalf (diff 1 p) = diff 1 (translateHalf p) := by
  have heq : (X + C (1 : K)).comp (X + C (1 / 2 : K)) =
      (X + C (1 / 2 : K)).comp (X + C (1 : K)) := by
    simp only [add_comp, X_comp, C_comp]
    ring
  simp only [translateHalf_apply, diff, shift, sub_comp, comp_assoc]
  rw [heq]

lemma translateHalf_ideal (p : K[X]) :
    p ∈ ideal 1 ↔ translateHalf p ∈ negativeHalfIdeal := by
  rw [ideal_field_eq]
  simp only [negativeHalfIdeal, Ideal.mem_span_singleton]
  rw [← map_dvd_iff (translateHalf : K[X] ≃ₐ[K] K[X])]
  have hg : translateHalf ((X : K[X]) * (X - C (1 / 2 : K))) =
      X * (X + C (1 / 2 : K)) := by
    simp only [translateHalf_apply, mul_comp, X_comp, sub_comp, C_comp]
    ring
  rw [hg]

/-- Both directions concern arbitrary K[X]-preimages of the literal ideals. -/
lemma translateHalf_image (p : K[X]) :
    p ∈ image 1 ↔ translateHalf p ∈ negativeHalfImage := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨translateHalf q, (translateHalf_ideal q).mp hq, (translateHalf_diff q).symm⟩
  · rintro ⟨q, hq, he⟩
    refine ⟨translateHalf.symm q, (translateHalf_ideal _).mpr (by simpa using hq), ?_⟩
    apply (translateHalf : K[X] ≃ₐ[K] K[X]).injective
    simpa only [translateHalf_diff, AlgEquiv.apply_symm_apply] using he

lemma negativeHalf_even (m : ℕ) (hm : 1 ≤ m) :
    ((X + C (1 / 2 : K)) ^ 2) ^ m ∈ negativeHalfImage := by
  have h := (translateHalf_image (K := K) _).mp (even_image (R := K) m hm)
  simpa only [map_pow, translateHalf_X] using h

lemma negativeHalf_odd (m : ℕ) (hm : 1 ≤ m) :
    (X + C (1 / 2 : K)) * ((X + C (1 / 2 : K)) ^ 2) ^ m ∉ negativeHalfImage := by
  have h := (translateHalf_image (K := K) ((X : K[X]) * (X ^ 2) ^ m)).not
  simpa only [map_mul, map_pow, translateHalf_X] using h.mp (odd_not_image (R := K) m hm)

theorem negativeHalf_endpoint : NegativeHalfEndpoint K := by
  refine ⟨negativeHalf_even, negativeHalf_odd, ?_⟩
  intro hW
  obtain ⟨N, hN⟩ := hW ((X + C (1 / 2 : K)) ^ 2) (negativeHalf_even (K := K))
    (X + C (1 / 2 : K)) 1
  exact negativeHalf_odd (K := K) (max N 1) (le_max_right N 1)
    (by simpa only [mul_one] using hN (max N 1) (le_max_left N 1))

/-- Beta=-1/2 is literally X(X-beta), not a different ideal. -/
lemma negativeHalfIdeal_eq_beta : negativeHalfIdeal (K := K) =
    Ideal.span {(X : K[X]) * (X - C (-1 / 2 : K))} := by
  simp only [negativeHalfIdeal, neg_div, map_neg, sub_neg_eq_add]

/-- Full LNED/ideal counterexample, with translated witnesses. -/
theorem negativeHalf_counterexample :
    ∃ (φ : K[X] →ₐ[K] K[X]) (D : K[X] →ₗ[K] K[X]) (J : Ideal K[X]),
      (∀ p : K[X], φ p = p.comp (X + 1)) ∧
      (∀ p : K[X], D p = p - φ p) ∧
      J = Ideal.span {(X : K[X]) * (X - C (-1 / 2 : K))} ∧
      (∀ p : K[X], ∃ N : ℕ, 0 < N ∧ ((D : K[X] → K[X])^[N]) p = 0) ∧
      (∀ p q : K[X], D (p * q) = D p * q + p * D q - D p * D q) ∧
      (∀ m : ℕ, 1 ≤ m → ((X + C (1 / 2 : K)) ^ 2) ^ m ∈ D '' (J : Set K[X])) ∧
      (∀ m : ℕ, 1 ≤ m → (X + C (1 / 2 : K)) * ((X + C (1 / 2 : K)) ^ 2) ^ m ∉ D '' (J : Set K[X])) ∧
      ¬ Mathieu (D '' (J : Set K[X])) := by
  obtain ⟨hev, hod, hM⟩ := negativeHalf_endpoint (K := K)
  refine ⟨shiftAlg 1, diffLinear 1, negativeHalfIdeal, ?_, fun _ => rfl,
    negativeHalfIdeal_eq_beta, locally_nilpotent 1, E_identity 1, hev, hod, hM⟩
  intro p
  simp only [shiftAlg_apply, shift, C_1]

#print axioms translateHalf_diff
#print axioms translateHalf_ideal
#print axioms translateHalf_image
#print axioms negativeHalf_endpoint
#print axioms negativeHalf_counterexample
end LNEDExtension
