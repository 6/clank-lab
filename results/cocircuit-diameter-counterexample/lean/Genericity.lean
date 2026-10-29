import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic

/- The kernel-checked Vandermonde part of the frozen symbolic route.
   It neither states nor assumes labelled-cell preservation. -/
namespace ADKZPricing

noncomputable section

open Polynomial Matrix

def vandermondeDirection {n r : ℕ} (f : Fin r → Fin n) : Matrix (Fin r) (Fin r) ℚ :=
  Matrix.vandermonde (fun i => ((f i).val : ℚ) + 1)

def minorPolynomial {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℚ)
    (f : Fin r → Fin n) : ℚ[X] :=
  Matrix.det ((X : ℚ[X]) • (vandermondeDirection f).map C +
    Matrix.map (fun i j => A (f i) j : Matrix (Fin r) (Fin r) ℚ) C)

theorem minor_top_coefficient {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℚ)
    (f : Fin r → Fin n) :
    (minorPolynomial A f).coeff r = Matrix.det (vandermondeDirection f) := by
  simpa only [minorPolynomial, Fintype.card_fin] using
    Polynomial.coeff_det_X_add_C_card (vandermondeDirection f)
      (fun i j => A (f i) j : Matrix (Fin r) (Fin r) ℚ)

theorem minor_constant_coefficient {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℚ)
    (f : Fin r → Fin n) :
    (minorPolynomial A f).coeff 0 = Matrix.det (fun i j => A (f i) j) := by
  exact Polynomial.coeff_det_X_add_C_zero (vandermondeDirection f)
    (fun i j => A (f i) j)

theorem minor_polynomial_nonzero {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℚ)
    (f : Fin r → Fin n) (hf : Function.Injective f) : minorPolynomial A f ≠ 0 := by
  have hv : Function.Injective (fun i : Fin r => ((f i).val : ℚ) + 1) := by
    intro i j h
    apply hf
    apply Fin.ext
    have he : ((f i).val : ℚ) = ((f j).val : ℚ) := add_right_cancel h
    exact_mod_cast he
  have hd : Matrix.det (vandermondeDirection f) ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr hv
  intro hz
  have h := minor_top_coefficient A f
  rw [hz, Polynomial.coeff_zero] at h
  exact hd h.symm

def rationalPerturbation {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℚ) (t : ℚ) :
    Matrix (Fin n) (Fin r) ℚ :=
  fun i j => A i j + t * ((i.val : ℚ) + 1) ^ j.val

theorem evaluate_minor {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℚ)
    (f : Fin r → Fin n) (t : ℚ) :
    (minorPolynomial A f).eval t = Matrix.det (fun i j => rationalPerturbation A t (f i) j) := by
  change (Polynomial.evalRingHom t) (Matrix.det _) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [vandermondeDirection, Matrix.vandermonde_apply, rationalPerturbation, add_comm]

/-- Every positive rational interval contains a specialization making ALL
    maximal minors nonzero. This is an existence proof, not a computation
    of an amplitude or an enumeration of minors. -/
theorem arbitrarily_small_uniform {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℚ)
    (ε : ℚ) (hε : 0 < ε) :
    ∃ t : ℚ, 0 < t ∧ t < ε ∧ ∀ f : Fin r → Fin n, Function.Injective f →
      Matrix.det (fun i j => rationalPerturbation A t (f i) j) ≠ 0 := by
  classical
  let embeddings : Finset (Fin r → Fin n) := Finset.univ.filter Function.Injective
  let p : ℚ[X] := ∏ f ∈ embeddings, minorPolynomial A f
  have hp : p ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro f hf
    exact minor_polynomial_nonzero A f (Finset.mem_filter.mp hf).2
  obtain ⟨t, ht, hroot⟩ := (Set.Ioo_infinite hε).exists_not_mem_finite
    (Polynomial.finite_setOf_isRoot hp)
  refine ⟨t, ht.1, ht.2, ?_⟩
  intro f hf
  have heval : p.eval t ≠ 0 := hroot
  have hprod : (∏ g ∈ embeddings, (minorPolynomial A g).eval t) ≠ 0 := by
    simpa only [p, Polynomial.eval_prod] using heval
  rw [← evaluate_minor]
  exact Finset.prod_ne_zero_iff.mp hprod f (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩)

#print axioms minor_polynomial_nonzero
#print axioms arbitrarily_small_uniform

end
end ADKZPricing
