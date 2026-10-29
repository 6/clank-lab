import Endpoint
import SecondPerturbation
set_option maxRecDepth 4096

namespace ADKZPricing
open Matrix

theorem selected_minor_as_lambda {n r : ℕ}
    (A : Matrix (Fin n) (Fin r) ℚ) (f : Fin r → Fin n) :
    (A.submatrix f id).det = Matrix.det (fun i j => A (f i) j) := rfl

theorem uniform_from_submatrices (A : Matrix (Fin 80) (Fin 41) ℚ)
    (h : ∀ f : Fin 41 → Fin 80, Function.Injective f → (A.submatrix f id).det ≠ 0) :
    Uniform A := by
  intro f hf
  rw [← selected_minor_as_lambda A f]
  exact h f hf

theorem second_uniform_lambda {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A) (h0 : 0 < C.chart 0) :
    ∀ f : Fin (d + d + 1) → Fin (n + n), Function.Injective f →
      Matrix.det (fun i j => secondPerturbedMatrix A C h0 (f i) j) ≠ 0 := by
  intro f hf
  rw [← selected_minor_as_lambda]
  exact (secondPerturbedMatrix_properties A C h0).1 f hf

/-- Keeping the dimension-polymorphic proposition folded prevents
    elaboration from expanding a concrete determinant during conversion. -/
def UniformAt {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℚ) : Prop :=
  ∀ f : Fin r → Fin n, Function.Injective f → Matrix.det (fun i j => A (f i) j) ≠ 0

theorem second_uniform_at {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A) (h0 : 0 < C.chart 0) :
    UniformAt (secondPerturbedMatrix A C h0) := second_uniform_lambda A C h0

theorem uniform_at_endpoint (A : Matrix (Fin 80) (Fin 41) ℚ) (h : UniformAt A) : Uniform A := h

theorem second_uniform_endpoint (A : Matrix (Fin 40) (Fin 21) ℤ)
    (C : IntegralStarChart A) (h0 : 0 < C.chart 0) :
    Uniform (secondPerturbedMatrix (n := 40) (d := 20) A C h0) :=
  uniform_at_endpoint _ (second_uniform_at (n := 40) (d := 20) A C h0)

#print axioms second_uniform_endpoint
#print axioms uniform_from_submatrices
end ADKZPricing
