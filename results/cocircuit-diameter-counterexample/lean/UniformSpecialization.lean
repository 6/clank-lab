import KernelAssembly
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Vandermonde

namespace ADKZPricing
open Polynomial Matrix
noncomputable section

def integerVandermonde {n r : ℕ} : Matrix (Fin n) (Fin r) ℤ :=
  fun i j => ((i.val : ℤ) + 1) ^ j.val

theorem integer_minor_nonzero {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℤ)
    (f : Fin r → Fin n) (hf : Function.Injective f) :
    (linearMatrix (fun i j => A (f i) j)
      (fun i j => (integerVandermonde : Matrix (Fin n) (Fin r) ℤ) (f i) j)).det ≠ 0 := by
  let V : Matrix (Fin r) (Fin r) ℤ := Matrix.vandermonde (fun i => ((f i).val : ℤ) + 1)
  have hv : Function.Injective (fun i : Fin r => ((f i).val : ℤ) + 1) := by
    intro i j h
    apply hf
    apply Fin.ext
    have he : ((f i).val : ℤ) = ((f j).val : ℤ) := add_right_cancel h
    exact_mod_cast he
  have hdet : V.det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hv
  have heq : linearMatrix (fun i j => A (f i) j)
      (fun i j => (integerVandermonde : Matrix (Fin n) (Fin r) ℤ) (f i) j) =
      (X : ℤ[X]) • V.map C + Matrix.map (fun i j => A (f i) j) C := by
    ext i j
    simp [linearMatrix, linearEntry, V, integerVandermonde, Matrix.vandermonde_apply, add_comm]
  rw [heq]
  intro hz
  have hc := Polynomial.coeff_det_X_add_C_card V (fun i j => A (f i) j)
  rw [hz, Polynomial.coeff_zero] at hc
  exact hdet hc.symm

def specializedMatrix {n r : ℕ} (A D : Matrix (Fin n) (Fin r) ℤ) (t : ℚ) :
    Matrix (Fin n) (Fin r) ℚ := fun i j => (A i j : ℚ) + t * (D i j : ℚ)

theorem eval_integer_minor {n r : ℕ} (A D : Matrix (Fin n) (Fin r) ℤ)
    (f : Fin r → Fin n) (t : ℚ) :
    ((linearMatrix (fun i j => A (f i) j) (fun i j => D (f i) j)).det).eval₂
      (Int.castRingHom ℚ) t = Matrix.det (fun i j => specializedMatrix A D t (f i) j) := by
  change (Polynomial.eval₂RingHom (Int.castRingHom ℚ) t) (Matrix.det _) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  change (C (A (f i) j) + X * C (D (f i) j)).eval₂ (Int.castRingHom ℚ) t = _
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C]
  rfl

/-- A single explicit parameter makes all maximal minors nonzero. The
    parameter is also the one used for every cofactor/slack/chart bound. -/
theorem explicit_uniform_specialization {n r : ℕ} (hr : 0 < r)
    (A : Matrix (Fin n) (Fin r) ℤ) (B : ℤ) (hB : 1 ≤ B)
    (ha : ∀ i j, |A i j| ≤ B)
    (hd : ∀ i j, |(integerVandermonde : Matrix (Fin n) (Fin r) ℤ) i j| ≤ B) :
    ∀ f : Fin r → Fin n, Function.Injective f →
      Matrix.det (fun i j => specializedMatrix A integerVandermonde
        (commonParameter r B) (f i) j) ≠ 0 := by
  intro f hf
  rw [← eval_integer_minor]
  exact common_nonzero_polynomial r B (by omega) _ r (cofactorBound r B)
    (cofactorBound_nonnegative r B (by omega))
    (envelope_determinant _ _ B (by omega) (fun i j => ha (f i) j) (fun i j => hd (f i) j))
    (common_mass_covers_cofactor r hr B hB) (integer_minor_nonzero A f hf)

#print axioms integer_minor_nonzero
#print axioms explicit_uniform_specialization
end
end ADKZPricing
