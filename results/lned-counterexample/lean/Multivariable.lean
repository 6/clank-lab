import Rescale
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.CharP.Algebra

namespace LNEDExtension
open Polynomial
variable {K : Type*} [Field K] [CharZero K] {σ : Type*}

local instance : CharZero (MvPolynomial σ K) :=
  charZero_of_injective_algebraMap (algebraMap K (MvPolynomial σ K)).injective

/-- Actual shift endomorphism: none is shifted by one; every some-variable is fixed. -/
noncomputable def mvShift : MvPolynomial (Option σ) K →ₐ[K] MvPolynomial (Option σ) K :=
  MvPolynomial.aeval fun i => match i with
    | none => MvPolynomial.X none + 1
    | some j => MvPolynomial.X (some j)

noncomputable def mvDiff (p : MvPolynomial (Option σ) K) := p - mvShift p
noncomputable def mvIdeal : Ideal (MvPolynomial (Option σ) K) :=
  Ideal.span {MvPolynomial.X none * (MvPolynomial.X none - MvPolynomial.C (1 / 2 : K))}
noncomputable def mvImage : Set (MvPolynomial (Option σ) K) := mvDiff '' ((mvIdeal : Ideal (MvPolynomial (Option σ) K)) : Set _)

def MvMathieu (W : Set (MvPolynomial (Option σ) K)) : Prop :=
  ∀ a, (∀ m : ℕ, 1 ≤ m → a ^ m ∈ W) →
    ∀ b d, ∃ N : ℕ, ∀ m : ℕ, N ≤ m → b * a ^ m * d ∈ W

/-- Exact endpoint, on the actual multivariable ring and the literal ideal. -/
def MvEndpoint (K : Type*) [Field K] [CharZero K] (σ : Type*) : Prop :=
  (∀ p : MvPolynomial (Option σ) K, ∃ N : ℕ, 0 < N ∧ (mvDiff^[N]) p = 0) ∧
  (∀ p q : MvPolynomial (Option σ) K,
    mvDiff (p * q) = mvDiff p * q + p * mvDiff q - mvDiff p * mvDiff q) ∧
  (∀ m : ℕ, 1 ≤ m → ((MvPolynomial.X none) ^ 2 : MvPolynomial (Option σ) K) ^ m ∈ mvImage) ∧
  (∀ m : ℕ, 1 ≤ m → (MvPolynomial.X none : MvPolynomial (Option σ) K) *
    ((MvPolynomial.X none) ^ 2 : MvPolynomial (Option σ) K) ^ m ∉ mvImage) ∧
  ¬ MvMathieu (mvImage : Set (MvPolynomial (Option σ) K))

noncomputable def univariate :
    MvPolynomial (Option σ) K ≃ₐ[K] (MvPolynomial σ K)[X] :=
  MvPolynomial.optionEquivLeft K σ

lemma univariate_X : univariate (MvPolynomial.X none : MvPolynomial (Option σ) K) = X :=
  MvPolynomial.optionEquivLeft_X_none K σ

lemma univariate_shift (p : MvPolynomial (Option σ) K) :
    univariate (mvShift p) = shift 1 (univariate p) := by
  have heq : (univariate : MvPolynomial (Option σ) K ≃ₐ[K] (MvPolynomial σ K)[X]).toAlgHom.comp mvShift =
      ((Polynomial.aeval (X + C (1 : MvPolynomial σ K)) :
        (MvPolynomial σ K)[X] →ₐ[MvPolynomial σ K] (MvPolynomial σ K)[X]).restrictScalars K).comp
        (univariate : MvPolynomial (Option σ) K ≃ₐ[K] (MvPolynomial σ K)[X]).toAlgHom := by
    ext i
    cases i with
    | none => simp [univariate, mvShift, MvPolynomial.optionEquivLeft_X_none, ← comp_eq_aeval]
    | some i => simp [univariate, mvShift, MvPolynomial.optionEquivLeft_X_some, ← comp_eq_aeval]
  exact DFunLike.congr_fun heq p

lemma univariate_diff (p : MvPolynomial (Option σ) K) :
    univariate (mvDiff p) = diff 1 (univariate p) := by
  simp only [mvDiff, map_sub, univariate_shift, diff]

lemma univariate_ideal (p : MvPolynomial (Option σ) K) :
    p ∈ mvIdeal ↔ univariate p ∈ ideal 1 := by
  have hh : (half : MvPolynomial σ K) = MvPolynomial.C (1 / 2 : K) := by
    simp [half, map_div₀, MvPolynomial.algebraMap_eq]
  simp only [mvIdeal, ideal, one_mul, Ideal.mem_span_singleton]
  rw [← map_dvd_iff (univariate : MvPolynomial (Option σ) K ≃ₐ[K] (MvPolynomial σ K)[X])]
  simp only [map_mul, map_sub, univariate_X]
  rw [hh]
  simp only [univariate, MvPolynomial.optionEquivLeft_C]

lemma univariate_image (p : MvPolynomial (Option σ) K) :
    p ∈ mvImage ↔ univariate p ∈ image 1 := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨univariate q, (univariate_ideal q).mp hq, (univariate_diff q).symm⟩
  · rintro ⟨q, hq, heq⟩
    refine ⟨univariate.symm q, (univariate_ideal _).mpr (by simpa using hq), ?_⟩
    apply (univariate : MvPolynomial (Option σ) K ≃ₐ[K] (MvPolynomial σ K)[X]).injective
    simpa only [univariate_diff, AlgEquiv.apply_symm_apply] using heq

lemma mv_locally_nilpotent (p : MvPolynomial (Option σ) K) :
    ∃ N : ℕ, 0 < N ∧ (mvDiff^[N]) p = 0 := by
  obtain ⟨N, hN, hz⟩ := locally_nilpotent (1 : MvPolynomial σ K) (univariate p)
  have hi : ∀ n, univariate ((mvDiff^[n]) p) = ((diff 1)^[n]) (univariate p) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [Function.iterate_succ_apply', univariate_diff, ih]
  refine ⟨N, hN, ?_⟩
  apply (univariate : MvPolynomial (Option σ) K ≃ₐ[K] (MvPolynomial σ K)[X]).injective
  rw [hi, hz, map_zero]

lemma mv_E (p q : MvPolynomial (Option σ) K) :
    mvDiff (p * q) = mvDiff p * q + p * mvDiff q - mvDiff p * mvDiff q := by
  simp only [mvDiff, map_mul]
  ring

lemma mv_even (m : ℕ) (hm : 1 ≤ m) :
    ((MvPolynomial.X none) ^ 2 : MvPolynomial (Option σ) K) ^ m ∈ mvImage := by
  rw [univariate_image]
  simpa only [map_pow, univariate_X] using even_image (R := MvPolynomial σ K) m hm

lemma mv_odd (m : ℕ) (hm : 1 ≤ m) :
    (MvPolynomial.X none : MvPolynomial (Option σ) K) *
    ((MvPolynomial.X none) ^ 2 : MvPolynomial (Option σ) K) ^ m ∉ mvImage := by
  rw [univariate_image]
  simpa only [map_mul, map_pow, univariate_X] using odd_not_image (R := MvPolynomial σ K) m hm

lemma mv_not_mathieu : ¬ MvMathieu (mvImage : Set (MvPolynomial (Option σ) K)) := by
  intro hW
  obtain ⟨N, hN⟩ := hW ((MvPolynomial.X none) ^ 2) (mv_even (K := K) (σ := σ))
    (MvPolynomial.X none) 1
  exact mv_odd (K := K) (σ := σ) (max N 1) (le_max_right N 1)
    (by simpa only [mul_one] using hN (max N 1) (le_max_left N 1))

/-- Any set of extra variables, with a distinguished variable none. -/
theorem multivariable_endpoint : MvEndpoint K σ :=
  ⟨mv_locally_nilpotent, mv_E, mv_even, mv_odd, mv_not_mathieu⟩

#print axioms univariate_shift
#print axioms univariate_ideal
#print axioms univariate_image
#print axioms multivariable_endpoint
end LNEDExtension
