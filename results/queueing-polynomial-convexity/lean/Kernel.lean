import H
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

namespace BLSH
open scoped BigOperators
open MvPolynomial

noncomputable section
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Coefficient-one sum over all multi-indices of total degree d. -/
def hp (d : Nat) : MvPolynomial σ Real :=
  ∑ α ∈ Finset.finsuppAntidiag (Finset.univ : Finset σ) d,
    MvPolynomial.monomial α 1

@[simp] theorem coeff_hp (d : Nat) (α : σ →₀ Nat) :
    (hp (σ := σ) d).coeff α = if (∑ i, α i) = d then 1 else 0 := by
  classical
  simp [hp, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, eq_comm]

/-- The directional derivative, as an algebraic derivation. -/
def direction (z : σ → Real) : Derivation Real (MvPolynomial σ Real) (MvPolynomial σ Real) :=
  ∑ i, z i • MvPolynomial.pderiv i

@[simp] theorem direction_X (z : σ → Real) (i : σ) :
    direction z (MvPolynomial.X i) = MvPolynomial.C (z i) := by
  simp [direction, Pi.single_apply, smul_eq_C_mul]

theorem coeff_direction (z : σ → Real) (p : MvPolynomial σ Real) (α : σ →₀ Nat) :
    (direction z p).coeff α =
      ∑ i, z i * p.coeff (α + Finsupp.single i 1) * (α i + 1) := by
  simp [direction, MvPolynomial.coeff_pderiv,
    mul_assoc, Nat.cast_add, Nat.cast_one]

/-- Evaluation along a line has the formally differentiated polynomial as derivative. -/
theorem hasDerivAt_line (p : MvPolynomial σ Real) (w z : σ → Real) (t : Real) :
    HasDerivAt (fun t => MvPolynomial.eval (fun i => w i + t * z i) p)
      (MvPolynomial.eval (fun i => w i + t * z i) (direction z p)) t := by
  induction p using MvPolynomial.induction_on with
  | C r => simpa using (hasDerivAt_const t r)
  | add p q hp hq =>
    convert hp.add hq using 1
    · funext s
      simp only [map_add, Pi.add_apply]
    · simp only [map_add]
  | mul_X p i hp =>
    have hi : HasDerivAt (fun t : Real => w i + t * z i) (z i) t := by
      convert ((hasDerivAt_id t).mul_const (z i)).const_add (w i) using 1 <;> simp
    convert hp.mul hi using 1
    · funext s
      simp only [map_mul, MvPolynomial.eval_X, Pi.mul_apply]
    · simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, direction_X,
        MvPolynomial.eval_C, MvPolynomial.eval_X]
      ring

/-- A polynomial with nonnegative coefficients is nonnegative on the orthant. -/
theorem eval_nonneg_of_coeff (p : MvPolynomial σ Real)
    (hc : ∀ α, 0 ≤ p.coeff α) (w : σ → Real) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ MvPolynomial.eval w p := by
  rw [p.as_sum]
  simp only [map_sum, MvPolynomial.eval_monomial]
  exact Finset.sum_nonneg fun α _ => mul_nonneg (hc α)
    (Finset.prod_nonneg fun i _ => pow_nonneg (hw i) _)


@[simp] theorem sum_shift (α : σ →₀ Nat) (i : σ) :
    (∑ j : σ, (α + Finsupp.single i 1 : σ →₀ Nat) j) = (∑ j, α j) + 1 := by
  simp [Finsupp.add_apply, Finsupp.single_apply, Finset.sum_add_distrib]

/-- The coefficient of each Hessian monomial is a square plus a nonnegative diagonal term. -/
theorem coeff_direction2_hp (z : σ → Real) (d : Nat) (α : σ →₀ Nat) :
    (direction z (direction z (hp (σ := σ) d))).coeff α =
      if (∑ i, α i) + 2 = d then
        (∑ i, ((α i : Real) + 1) * z i) ^ 2 +
          ∑ i, ((α i : Real) + 1) * z i ^ 2
      else 0 := by
  simp_rw [coeff_direction, coeff_hp, sum_shift]
  by_cases h : (∑ i, α i) + 2 = d
  · simp only [Nat.add_assoc, show (1 : Nat) + 1 = 2 from rfl, h, if_true, mul_one]
    simp only [Finsupp.add_apply, Finsupp.single_apply, Nat.cast_add, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
    have hin (i : σ) :
        (∑ j, z j * (((α j : Real) + if i = j then 1 else 0) + 1)) =
          (∑ j, ((α j : Real) + 1) * z j) + z i := by
      calc
        _ = ∑ j, (((α j : Real) + 1) * z j + if i = j then z j else 0) := by
          apply Finset.sum_congr rfl
          intro j _
          split_ifs <;> ring
        _ = _ := by simp [Finset.sum_add_distrib]
    simp_rw [hin]
    calc
      _ = (∑ i, ((α i : Real) + 1) * z i) *
            (∑ i, ((α i : Real) + 1) * z i) +
            ∑ i, ((α i : Real) + 1) * z i ^ 2 := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by ring
  · simp [Nat.add_assoc, h]

 theorem coeff_direction2_hp_nonneg (z : σ → Real) (d : Nat) (α : σ →₀ Nat) :
    0 ≤ (direction z (direction z (hp (σ := σ) d))).coeff α := by
  rw [coeff_direction2_hp]
  split_ifs
  · exact add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ =>
      mul_nonneg (by positivity) (sq_nonneg _))
  · exact le_rfl


/-- General affine-line assembly; the next theorem discharges this algebraic premise. -/
theorem convexOn_eval_of_direction2 (p : MvPolynomial σ Real)
    (hc : ∀ (z : σ → Real) α, 0 ≤ (direction z (direction z p)).coeff α) :
    ConvexOn Real {w : σ → Real | ∀ i, 0 ≤ w i} (fun w => MvPolynomial.eval w p) := by
  have hs : Convex Real {w : σ → Real | ∀ i, 0 ≤ w i} := by
    intro x hx y hy a b ha hb hab i
    exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  let z : σ → Real := fun i => y i - x i
  let f : Real → Real := fun t => MvPolynomial.eval (fun i => x i + t * z i) p
  let f' : Real → Real := fun t => MvPolynomial.eval (fun i => x i + t * z i) (direction z p)
  let f'' : Real → Real := fun t => MvPolynomial.eval (fun i => x i + t * z i)
    (direction z (direction z p))
  have hd (t : Real) : HasDerivAt f (f' t) t := hasDerivAt_line p x z t
  have hdd (t : Real) : HasDerivAt f' (f'' t) t := hasDerivAt_line (direction z p) x z t
  have hf : ConvexOn Real (Set.Icc 0 1) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
      ((continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt).continuousOn)
      (fun t _ => (hd t).hasDerivWithinAt)
      (fun t _ => (hdd t).hasDerivWithinAt)
    intro t ht
    apply eval_nonneg_of_coeff _ (hc z)
    have ht' : t ∈ Set.Icc (0 : Real) 1 := interior_subset ht
    intro i
    dsimp [z]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht'.2) (hx i), mul_nonneg ht'.1 (hy i)]
  have h := hf.2 (show (0 : Real) ∈ Set.Icc 0 1 by simp)
    (show (1 : Real) ∈ Set.Icc 0 1 by simp) ha hb hab
  have heq : (fun i => x i + b * z i) = a • x + b • y := by
    funext i
    dsimp [z]
    have hae : a = 1 - b := by linarith
    rw [hae]
    ring
  simpa [f, z, smul_eq_mul, heq] using h

theorem convexOn_hp (d : Nat) :
    ConvexOn Real {w : σ → Real | ∀ i, 0 ≤ w i}
      (fun w => MvPolynomial.eval w (hp (σ := σ) d)) :=
  convexOn_eval_of_direction2 _ (fun z α => coeff_direction2_hp_nonneg z d α)

/-- Split the canonical coefficient-one polynomial at the first variable. -/
theorem finSucc_hp (m d : Nat) :
    MvPolynomial.finSuccEquiv Real m (hp (σ := Fin (m+1)) d) =
      ∑ k ∈ Finset.range (d+1), Polynomial.monomial k (hp (σ := Fin m) (d-k)) := by
  apply Polynomial.ext
  intro k
  apply MvPolynomial.ext
  intro α
  rw [MvPolynomial.finSuccEquiv_coeff_coeff, coeff_hp]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  by_cases hk : k < d + 1
  · simp [hk, coeff_hp, Fin.sum_univ_succ]
    have heq : (k + ∑ i, α i = d) ↔ (∑ i, α i = d - k) := by omega
    simp only [heq]
  · have hne : k + (∑ i, α i) ≠ d := by omega
    simp [hk, coeff_hp, Fin.sum_univ_succ, hne]

/-- Faithful bridge from coefficient-one monomials to the shared recursion. -/
theorem eval_hp_complete (m d : Nat) (w : Fin m → Real) :
    MvPolynomial.eval w (hp (σ := Fin m) d) = complete (List.ofFn w) d := by
  induction m generalizing d with
  | zero =>
    have hp0 : hp (σ := Fin 0) d = if d = 0 then 1 else 0 := by
      apply MvPolynomial.ext
      intro α
      have hα : α = 0 := Subsingleton.elim _ _
      subst α
      split_ifs <;> simp_all [coeff_hp, eq_comm]
    rw [hp0]
    cases d <;> simp [complete]
  | succ m ih =>
    rw [show w = Fin.cons (w 0) (fun i => w i.succ) from (Fin.cons_self_tail w).symm]
    rw [MvPolynomial.eval_eq_eval_mv_eval', finSucc_hp]
    simp only [Polynomial.map_sum, Polynomial.map_monomial, map_sum,
      Polynomial.eval_finsetSum, Polynomial.eval_monomial, ih, List.ofFn_succ, complete,
      Fin.cons_zero, Fin.cons_succ]
    apply Finset.sum_congr rfl
    intro k hk
    ring

theorem complete_convex (m d : Nat) :
    ConvexOn Real {w : Fin m → Real | ∀ i, 0 ≤ w i}
      (fun w => complete (List.ofFn w) d) := by
  simpa only [eval_hp_complete] using (convexOn_hp (σ := Fin m) d)

end
end BLSH
