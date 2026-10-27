import Shared
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity

/- Genuine arbitrary-arm specialization of the canonical arrow quotient.
No endpoint, primeness, or nonzero-fibre hypothesis is used. -/
namespace Makonzi
open scoped BigOperators
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2000

/-- The actual polynomial indeterminate embedded into the rational field. -/
noncomputable def T (p : Fin 3 → ℕ) : RationalField p :=
  algebraMap (Polynomial (CoeffField p)) (RationalField p) Polynomial.X

noncomputable def armRational (p : Fin 3 → ℕ) (i : Fin 3) : RationalField p :=
  coeffToRational p (armCoeff p i)

theorem coeffToField_injective (p : Fin 3 → ℕ) :
    Function.Injective (algebraMap (CoeffRing p) (CoeffField p)) :=
  IsFractionRing.injective _ _

theorem fieldToRational_injective (p : Fin 3 → ℕ) :
    Function.Injective (algebraMap (CoeffField p) (RationalField p)) :=
  (algebraMap (CoeffField p) (RationalField p)).injective

theorem coeffToRational_injective (p : Fin 3 → ℕ) :
    Function.Injective (coeffToRational p) :=
  (fieldToRational_injective p).comp (coeffToField_injective p)

theorem polynomialToRational_injective (p : Fin 3 → ℕ) :
    Function.Injective (algebraMap (Polynomial (CoeffField p)) (RationalField p)) :=
  RatFunc.algebraMap_injective _

theorem armCoeff_ne_zero (p : Fin 3 → ℕ) (i : Fin 3) : armCoeff p i ≠ 0 := by
  classical
  unfold armCoeff
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => MvPolynomial.X_ne_zero _)

theorem armRational_ne_zero (p : Fin 3 → ℕ) (i : Fin 3) : armRational p i ≠ 0 := by
  exact (map_ne_zero_iff (coeffToRational p) (coeffToRational_injective p)).mpr
    (armCoeff_ne_zero p i)

theorem T_ne_zero (p : Fin 3 → ℕ) : T p ≠ 0 := by
  exact RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero

theorem T_add_arm_ne_zero (p : Fin 3 → ℕ) (i : Fin 3) : T p + armRational p i ≠ 0 := by
  let c : CoeffField p := algebraMap (CoeffRing p) (CoeffField p) (armCoeff p i)
  have h : (Polynomial.X + Polynomial.C c : Polynomial (CoeffField p)) ≠ 0 := by
    intro h
    have := congrArg (fun f : Polynomial (CoeffField p) => f.coeff 1) h
    simp at this
  change algebraMap (Polynomial (CoeffField p)) (RationalField p) Polynomial.X +
    algebraMap (CoeffField p) (RationalField p) c ≠ 0
  rw [RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C, ← map_add]
  exact RatFunc.algebraMap_ne_zero h

/-- Only the first downward arrow in each arm has a nontrivial value. -/
noncomputable def downFirst (p : Fin 3 → ℕ) (i : Fin 3) : RationalField p :=
  if i = 0 then (T p + armRational p 2) / T p
  else if i = 1 then 1 else -armRational p 2 / T p

noncomputable def downValue (p : Fin 3 → ℕ) (e : Edge p) : RationalField p :=
  if e.2.val = 0 then downFirst p e.1 else 1

theorem downFirst_ne_zero (p : Fin 3 → ℕ) (i : Fin 3) : downFirst p i ≠ 0 := by
  fin_cases i
  · change (T p + armRational p 2) / T p ≠ 0
    exact @div_ne_zero (RationalField p) _ _ _ (T_add_arm_ne_zero p 2) (T_ne_zero p)
  · exact one_ne_zero
  · change -armRational p 2 / T p ≠ 0
    exact @div_ne_zero (RationalField p) _ _ _ (neg_ne_zero.mpr (armRational_ne_zero p 2)) (T_ne_zero p)

theorem downValue_ne_zero (p : Fin 3 → ℕ) (e : Edge p) : downValue p e ≠ 0 := by
  unfold downValue
  split_ifs <;> first | exact downFirst_ne_zero p e.1 | exact one_ne_zero

noncomputable def specializationArrow (p : Fin 3 → ℕ) : Arrow p → RationalField p
  | (false, e) => downValue p e
  | (true, e) => coeffToRational p (MvPolynomial.X e) / downValue p e

noncomputable def specializationEval (p : Fin 3 → ℕ) : ArrowRing p →+* RationalField p :=
  MvPolynomial.eval₂Hom ((coeffToRational p).comp MvPolynomial.C) (specializationArrow p)

/-- The product is uniform in the arm length; the only distinguished edge is zero. -/
theorem prod_downValue (p : Fin 3 → ℕ) (hp : ∀ i, 2 ≤ p i) (i : Fin 3) :
    (∏ j : Fin (p i), downValue p ⟨i, j⟩) = downFirst p i := by
  classical
  let z : Fin (p i) := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) (hp i)⟩
  rw [Finset.prod_eq_single z]
  · simp [downValue, z]
  · intro j _ hj
    have hj0 : j.val ≠ 0 := by
      intro h
      apply hj
      exact Fin.ext h
    simp [downValue, hj0]
  · simp

theorem specializationEval_D (p : Fin 3 → ℕ) (hp : ∀ i, 2 ≤ p i) (i : Fin 3) :
    specializationEval p (D p i) = downFirst p i := by
  simpa [D, specializationEval, specializationArrow, map_prod] using prod_downValue p hp i

theorem specializationEval_U (p : Fin 3 → ℕ) (hp : ∀ i, 2 ≤ p i) (i : Fin 3) :
    specializationEval p (U p i) = armRational p i / downFirst p i := by
  classical
  simp only [U, map_prod, specializationEval, MvPolynomial.eval₂Hom_X', specializationArrow]
  rw [Finset.prod_div_distrib (β := RationalField p), prod_downValue p hp i]
  congr 1
  simp [armRational, armCoeff, map_prod]

theorem specializationEval_edge (p : Fin 3 → ℕ) (e : Edge p) :
    specializationEval p (MvPolynomial.X (false, e) * MvPolynomial.X (true, e)) =
      coeffToRational p (MvPolynomial.X e) := by
  simp only [map_mul, specializationEval, MvPolynomial.eval₂Hom_X', specializationArrow]
  exact @mul_div_cancel₀ (RationalField p) _ _ _ (downValue_ne_zero p e)

/-- The cancellation identity, used with the actual nonzero indeterminate below. -/
theorem canonical_field_identity {L : Type*} [Field L] (t c : L) (ht : t ≠ 0) :
    (t+c)/t - 1 + -c/t = 0 := by
  field_simp

@[simp] theorem downFirst_zero (p : Fin 3 → ℕ) :
    downFirst p 0 = (T p + armRational p 2) / T p := by
  simp only [downFirst, if_pos rfl, if_true]

@[simp] theorem downFirst_one (p : Fin 3 → ℕ) : downFirst p 1 = 1 := by
  simp only [downFirst, show (1 : Fin 3) ≠ 0 by decide, if_false, if_pos rfl, if_true]

@[simp] theorem downFirst_two (p : Fin 3 → ℕ) :
    downFirst p 2 = -armRational p 2 / T p := by
  simp only [downFirst, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide, if_false]

theorem specializationEval_canonical (p : Fin 3 → ℕ) (hp : ∀ i, 2 ≤ p i) :
    specializationEval p (D p 0 - D p 1 + D p 2) = 0 := by
  rw [map_add, map_sub, specializationEval_D p hp, specializationEval_D p hp,
    specializationEval_D p hp, downFirst_zero, downFirst_one, downFirst_two]
  exact canonical_field_identity (L := RationalField p) _ _ (T_ne_zero p)

/-- Actual lift from the entire canonical arrow quotient. -/
noncomputable def psi (p : Fin 3 → ℕ) (hp : ∀ i, 2 ≤ p i) :
    ArrowRing p ⧸ canonicalIdeal p →+* RationalField p :=
  Ideal.Quotient.lift (canonicalIdeal p) (specializationEval p) (by
    change canonicalIdeal p ≤ RingHom.ker (specializationEval p)
    rw [canonicalIdeal, Ideal.span_le]
    intro f hf
    rcases Set.mem_singleton_iff.mp hf with rfl
    exact specializationEval_canonical p hp)

@[simp] theorem psi_mk (p : Fin 3 → ℕ) (hp : ∀ i, 2 ≤ p i) (f : ArrowRing p) :
    psi p hp (Ideal.Quotient.mk (canonicalIdeal p) f) = specializationEval p f := rfl

/-- Every edge, including the first on each arm, has its original coefficient value. -/
theorem psi_comp_phi_edge (p : Fin 3 → ℕ) (hp : ∀ i, 2 ≤ p i) (e : Edge p) :
    ((psi p hp).comp (phi p)) (MvPolynomial.X (Sum.inr e)) =
      coeffToRational p (MvPolynomial.X e) := by
  simpa [phi, arrowEval, arrowImage] using specializationEval_edge p e

theorem w0_field_identity {L : Type*} [Field L] (t b c : L) :
    (t+c)/t * (b/1) = b*(t+c)/t := by
  simp only [div_one]
  ring

theorem w1_field_identity {L : Type*} [Field L] (t a c : L) :
    1 * (a/((t+c)/t)) = a*t/(t+c) := by
  simp only [one_mul, div_div_eq_mul_div]

theorem w2_field_identity {L : Type*} [Field L] (t c : L)
    (_ht : t ≠ 0) (hc : c ≠ 0) : -(1 * (c/(-c/t))) = t := by
  field_simp [hc]

theorem psi_comp_phi_W0 (p : Fin 3 → ℕ) (hp : ∀ i, 2 ≤ p i) :
    ((psi p hp).comp (phi p)) (W p 0) =
      armRational p 1 * (T p + armRational p 2) / T p := by
  simp only [RingHom.comp_apply, phi, psi_mk, W, arrowEval, MvPolynomial.eval₂Hom_X']
  simp only [arrowImage, show (0 : Fin 3) = 0 by rfl, if_true]
  rw [map_mul, specializationEval_D p hp, specializationEval_U p hp]
  rw [downFirst_zero, downFirst_one]
  exact w0_field_identity (L := RationalField p) _ _ _

theorem psi_comp_phi_W1 (p : Fin 3 → ℕ) (hp : ∀ i, 2 ≤ p i) :
    ((psi p hp).comp (phi p)) (W p 1) =
      armRational p 0 * T p / (T p + armRational p 2) := by
  simp only [RingHom.comp_apply, phi, psi_mk, W, arrowEval, MvPolynomial.eval₂Hom_X']
  simp only [arrowImage, show (1 : Fin 3) ≠ 0 by decide, if_false, if_pos rfl, if_true]
  rw [map_mul, specializationEval_D p hp, specializationEval_U p hp]
  rw [downFirst_one, downFirst_zero]
  exact w1_field_identity (L := RationalField p) _ _ _

theorem psi_comp_phi_W2 (p : Fin 3 → ℕ) (hp : ∀ i, 2 ≤ p i) :
    ((psi p hp).comp (phi p)) (W p 2) = T p := by
  simp only [RingHom.comp_apply, phi, psi_mk, W, arrowEval, MvPolynomial.eval₂Hom_X']
  simp only [arrowImage, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide, if_false]
  rw [map_neg, map_mul, specializationEval_D p hp, specializationEval_U p hp]
  rw [downFirst_one, downFirst_two]
  exact w2_field_identity (L := RationalField p) _ _ (T_ne_zero p) (armRational_ne_zero p 2)

/-- The whole coefficient-polynomial subring is carried by its faithful inclusion. -/
theorem psi_comp_phi_coeff (p : Fin 3 → ℕ) (hp : ∀ i, 2 ≤ p i) :
    ((psi p hp).comp (phi p)).comp (coeffEmbed p) = coeffToRational p := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [coeffEmbed, phi, arrowEval, specializationEval]
  · intro e
    simpa [coeffEmbed] using psi_comp_phi_edge p hp e

theorem psi_comp_phi_coeff_apply (p : Fin 3 → ℕ) (hp : ∀ i, 2 ≤ p i)
    (r : CoeffRing p) :
    ((psi p hp).comp (phi p)) (coeffEmbed p r) = coeffToRational p r :=
  RingHom.congr_fun (psi_comp_phi_coeff p hp) r

/-- The complete all-arm bridge, with no conditional denominator assumptions. -/
theorem allArmSpecialization (p : Fin 3 → ℕ) (hp : ∀ i, 2 ≤ p i) :
    ∃ Ψ : ArrowRing p ⧸ canonicalIdeal p →+* RationalField p,
      (∀ e : Edge p, (Ψ.comp (phi p)) (MvPolynomial.X (Sum.inr e)) =
        coeffToRational p (MvPolynomial.X e)) ∧
      (Ψ.comp (phi p)) (W p 0) = armRational p 1 * (T p + armRational p 2) / T p ∧
      (Ψ.comp (phi p)) (W p 1) = armRational p 0 * T p / (T p + armRational p 2) ∧
      (Ψ.comp (phi p)) (W p 2) = T p :=
  ⟨psi p hp, psi_comp_phi_edge p hp, psi_comp_phi_W0 p hp,
    psi_comp_phi_W1 p hp, psi_comp_phi_W2 p hp⟩

#print axioms allArmSpecialization
#print axioms psi_comp_phi_coeff
#print axioms armRational_ne_zero
#print axioms T_add_arm_ne_zero
#print axioms coeffToRational_injective
end Makonzi
