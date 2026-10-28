import Multivariable
import FieldClaim
import Mathlib.Logic.Equiv.Option

namespace LNEDExtension
variable {K : Type*} [Field K] [CharZero K] {τ : Type*}

/-- The actual endomorphism shifting exactly the chosen variable. -/
noncomputable def chosenShift (v : τ) : MvPolynomial τ K →ₐ[K] MvPolynomial τ K := by
  classical
  exact MvPolynomial.aeval fun i => if i = v then MvPolynomial.X i + 1 else MvPolynomial.X i
noncomputable def chosenDiff (v : τ) (p : MvPolynomial τ K) := p - chosenShift v p
noncomputable def chosenLinear (v : τ) : MvPolynomial τ K →ₗ[K] MvPolynomial τ K :=
  LinearMap.id - (chosenShift v).toLinearMap
noncomputable def chosenIdeal (v : τ) : Ideal (MvPolynomial τ K) :=
  Ideal.span {MvPolynomial.X v * (MvPolynomial.X v - MvPolynomial.C (1 / 2 : K))}
noncomputable def chosenImage (v : τ) : Set (MvPolynomial τ K) :=
  chosenDiff v '' ((chosenIdeal v : Ideal (MvPolynomial τ K)) : Set _)

def ChosenMathieu (W : Set (MvPolynomial τ K)) : Prop :=
  ∀ a, (∀ m : ℕ, 1 ≤ m → a ^ m ∈ W) →
    ∀ b d, ∃ N : ℕ, ∀ m : ℕ, N ≤ m → b * a ^ m * d ∈ W

/-- Exact statement on any index type with one chosen variable. -/
def ChosenEndpoint (v : τ) : Prop :=
  (∀ p : MvPolynomial τ K, ∃ N : ℕ, 0 < N ∧ ((chosenDiff v)^[N]) p = 0) ∧
  (∀ p q : MvPolynomial τ K, chosenDiff v (p * q) =
    chosenDiff v p * q + p * chosenDiff v q - chosenDiff v p * chosenDiff v q) ∧
  (∀ m : ℕ, 1 ≤ m → ((MvPolynomial.X v) ^ 2 : MvPolynomial τ K) ^ m ∈ chosenImage v) ∧
  (∀ m : ℕ, 1 ≤ m → (MvPolynomial.X v : MvPolynomial τ K) *
    ((MvPolynomial.X v) ^ 2 : MvPolynomial τ K) ^ m ∉ chosenImage v) ∧
  ¬ ChosenMathieu (chosenImage v : Set (MvPolynomial τ K))

noncomputable def chosenRename (v : τ) :
    MvPolynomial τ K ≃ₐ[K] MvPolynomial (Option {i // i ≠ v}) K := by
  classical
  exact MvPolynomial.renameEquiv K (Equiv.optionSubtypeNe v).symm

lemma chosenRename_X (v : τ) : chosenRename v (MvPolynomial.X v : MvPolynomial τ K) =
    MvPolynomial.X none := by
  classical
  simp [chosenRename, MvPolynomial.renameEquiv_apply, Equiv.optionSubtypeNe_symm_self]

lemma chosenRename_C (v : τ) (a : K) : chosenRename v (MvPolynomial.C a) = MvPolynomial.C a := by
  classical
  simp [chosenRename, MvPolynomial.renameEquiv_apply]

lemma chosenRename_shift (v : τ) (p : MvPolynomial τ K) :
    chosenRename v (chosenShift v p) = mvShift (chosenRename v p) := by
  classical
  have heq : (chosenRename v : MvPolynomial τ K ≃ₐ[K] _).toAlgHom.comp (chosenShift v) =
      mvShift.comp (chosenRename v).toAlgHom := by
    ext i
    by_cases h : i = v
    · subst i
      simp [chosenShift, chosenRename, mvShift, MvPolynomial.renameEquiv_apply,
        Equiv.optionSubtypeNe_symm_self]
    · simp [chosenShift, chosenRename, mvShift, MvPolynomial.renameEquiv_apply,
        Equiv.optionSubtypeNe_symm_of_ne h, h]
  exact DFunLike.congr_fun heq p

lemma chosenRename_diff (v : τ) (p : MvPolynomial τ K) :
    chosenRename v (chosenDiff v p) = mvDiff (chosenRename v p) := by
  simp only [chosenDiff, map_sub, chosenRename_shift, mvDiff]

lemma chosenRename_ideal (v : τ) (p : MvPolynomial τ K) :
    p ∈ chosenIdeal v ↔ chosenRename v p ∈ mvIdeal := by
  simp only [chosenIdeal, mvIdeal, Ideal.mem_span_singleton]
  rw [← map_dvd_iff (chosenRename v : MvPolynomial τ K ≃ₐ[K] _)]
  simp only [map_mul, map_sub, chosenRename_X, chosenRename_C]

lemma chosenRename_image (v : τ) (p : MvPolynomial τ K) :
    p ∈ chosenImage v ↔ chosenRename v p ∈ mvImage := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨chosenRename v q, (chosenRename_ideal v q).mp hq, (chosenRename_diff v q).symm⟩
  · rintro ⟨q, hq, he⟩
    refine ⟨(chosenRename v).symm q, (chosenRename_ideal v _).mpr (by simpa using hq), ?_⟩
    apply (chosenRename v).injective
    simpa only [chosenRename_diff, AlgEquiv.apply_symm_apply] using he

lemma chosen_ln (v : τ) (p : MvPolynomial τ K) :
    ∃ N : ℕ, 0 < N ∧ ((chosenDiff v)^[N]) p = 0 := by
  obtain ⟨N, hN, hz⟩ := mv_locally_nilpotent (chosenRename v p)
  have hi : ∀ n, chosenRename v (((chosenDiff v)^[n]) p) = (mvDiff^[n]) (chosenRename v p) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply', chosenRename_diff, ih]
  refine ⟨N, hN, ?_⟩
  apply (chosenRename v).injective
  rw [hi, hz, map_zero]

lemma chosen_E (v : τ) (p q : MvPolynomial τ K) :
    chosenDiff v (p * q) = chosenDiff v p * q + p * chosenDiff v q - chosenDiff v p * chosenDiff v q := by
  simp only [chosenDiff, map_mul]
  ring

lemma chosen_even (v : τ) (m : ℕ) (hm : 1 ≤ m) :
    ((MvPolynomial.X v) ^ 2 : MvPolynomial τ K) ^ m ∈ chosenImage v := by
  rw [chosenRename_image]
  simpa only [map_pow, chosenRename_X] using mv_even (K := K) (σ := {i // i ≠ v}) m hm

lemma chosen_odd (v : τ) (m : ℕ) (hm : 1 ≤ m) :
    (MvPolynomial.X v : MvPolynomial τ K) * ((MvPolynomial.X v) ^ 2 : MvPolynomial τ K) ^ m ∉ chosenImage v := by
  rw [chosenRename_image]
  simpa only [map_mul, map_pow, chosenRename_X] using mv_odd (K := K) (σ := {i // i ≠ v}) m hm

theorem chosen_variable_endpoint (v : τ) : ChosenEndpoint (K := K) v := by
  refine ⟨chosen_ln v, chosen_E v, chosen_even v, chosen_odd v, ?_⟩
  intro hW
  obtain ⟨N, hN⟩ := hW ((MvPolynomial.X v) ^ 2) (chosen_even (K := K) v)
    (MvPolynomial.X v) 1
  exact chosen_odd (K := K) v (max N 1) (le_max_right N 1)
    (by simpa only [mul_one] using hN (max N 1) (le_max_left N 1))

/-- K[x1,...,xn], n≥1, with the first variable shifted. -/
theorem finite_variable_endpoint (n : ℕ) (hn : 1 ≤ n) :
    ChosenEndpoint (K := K) (⟨0, hn⟩ : Fin n) := chosen_variable_endpoint _

lemma chosenLinear_apply (v : τ) (p : MvPolynomial τ K) :
    chosenLinear v p = chosenDiff v p := rfl

lemma chosenShift_X [DecidableEq τ] (v i : τ) :
    chosenShift (K := K) v (MvPolynomial.X i) =
      if i = v then MvPolynomial.X i + 1 else MvPolynomial.X i := by
  classical
  simp [chosenShift]

/-- Literal LNED ideal counterexample on an arbitrary index set. -/
theorem chosen_variable_counterexample (v : τ) :
    ∃ (φ : MvPolynomial τ K →ₐ[K] MvPolynomial τ K)
      (D : MvPolynomial τ K →ₗ[K] MvPolynomial τ K) (J : Ideal (MvPolynomial τ K)),
      φ (MvPolynomial.X v) = MvPolynomial.X v + 1 ∧
      (∀ i : τ, i ≠ v → φ (MvPolynomial.X i) = MvPolynomial.X i) ∧
      (∀ p : MvPolynomial τ K, D p = p - φ p) ∧
      J = Ideal.span {MvPolynomial.X v * (MvPolynomial.X v - MvPolynomial.C (1 / 2 : K))} ∧
      (∀ p : MvPolynomial τ K, ∃ N : ℕ, 0 < N ∧ ((D : _ → _)^[N]) p = 0) ∧
      (∀ p q : MvPolynomial τ K, D (p * q) = D p * q + p * D q - D p * D q) ∧
      (∀ m : ℕ, 1 ≤ m → ((MvPolynomial.X v) ^ 2 : MvPolynomial τ K) ^ m ∈ D '' (J : Set _)) ∧
      (∀ m : ℕ, 1 ≤ m → (MvPolynomial.X v : MvPolynomial τ K) *
        ((MvPolynomial.X v) ^ 2 : MvPolynomial τ K) ^ m ∉ D '' (J : Set _)) ∧
      ¬ ChosenMathieu (D '' (J : Set _)) := by
  classical
  obtain ⟨hLN, hE, hev, hod, hM⟩ := chosen_variable_endpoint (K := K) v
  refine ⟨chosenShift v, chosenLinear v, chosenIdeal v, ?_, ?_, fun _ => rfl,
    rfl, hLN, hE, hev, hod, hM⟩
  · simp [chosenShift]
  · intro i hi
    simp [chosenShift, hi]

#print axioms chosen_variable_counterexample

#print axioms chosenRename_shift
#print axioms chosenRename_ideal
#print axioms chosenRename_image
#print axioms chosen_variable_endpoint
#print axioms finite_variable_endpoint
end LNEDExtension
