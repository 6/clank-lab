import SignGeometry
import ProductCover
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option maxRecDepth 4096

namespace ADKZPricing
open Matrix Finset Module
noncomputable section

theorem rational_minor_cast {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℚ)
    (f : Fin r → Fin n) :
    ((Matrix.det (fun i j => A (f i) j) : ℚ) : ℝ) =
      Matrix.det (fun i j => (A (f i) j : ℝ)) := by
  have h := Rat.cast_det (F := ℝ) (A.submatrix f id)
  exact h

theorem uniform_real_minors (A : Matrix (Fin 80) (Fin 41) ℚ) (hu : Uniform A)
    (f : Fin 41 → Fin 80) (hf : Function.Injective f) :
    Matrix.det (fun i j => (A (f i) j : ℝ)) ≠ 0 := by
  rw [← rational_minor_cast]
  exact Rat.cast_ne_zero.mpr (hu f hf)

theorem rational_minor_injective {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℚ)
    (f : Fin r → Fin n) (hd : Matrix.det (fun i j => A (f i) j) ≠ 0) :
    Function.Injective (fun v : Fin r → ℝ => fun i : Fin n => ∑ j, (A i j : ℝ) * v j) := by
  let K : Matrix (Fin r) (Fin r) ℝ := fun i j => A (f i) j
  have hdet : K.det ≠ 0 := by
    rw [← rational_minor_cast]
    exact Rat.cast_ne_zero.mpr hd
  have hk := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det K).mpr (isUnit_iff_ne_zero.mpr hdet))
  intro v w he
  apply hk
  ext i
  exact congrArg (fun z : Fin n → ℝ => z (f i)) he

theorem uniform_real_injective (A : Matrix (Fin 80) (Fin 41) ℚ) (hu : Uniform A) :
    Function.Injective (fun v : Fin 41 → ℝ => fun i : Fin 80 => ∑ j, (A i j : ℝ) * v j) := by
  let f : Fin 41 → Fin 80 := Fin.castLE (by decide)
  exact rational_minor_injective A f (hu f (Fin.castLE_injective _))

theorem rational_uniform_zero_count {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℚ)
    (hu : ∀ f : Fin r → Fin n, Function.Injective f → Matrix.det (fun i j => A (f i) j) ≠ 0)
    (v : Fin r → ℝ) (hv : v ≠ 0) :
    (univ.filter (fun i => (∑ j, (A i j : ℝ) * v j) = 0)).card < r := by
  let R : Matrix (Fin n) (Fin r) ℝ := fun i j => A i j
  apply uniform_zero_count R _ v hv
  intro f hf
  change Matrix.det (fun i j => (A (f i) j : ℝ)) ≠ 0
  rw [← rational_minor_cast]
  exact Rat.cast_ne_zero.mpr (hu f hf)

/-- Every cocircuit of the frozen full graph has exactly forty zero rows.
    The lower bound comes from support minimality via the geometric
    boundary argument; the upper bound comes from global uniformity. -/
theorem uniform_cocircuit_zero_count (A : Matrix (Fin 80) (Fin 41) ℚ)
    (hu : Uniform A) (X : SignVector) (hc : Cocircuit A X) :
    (univ.filter (fun i => X i = 0)).card = 40 := by
  classical
  obtain ⟨v, hv⟩ := hc.1
  have hvne : v ≠ 0 := by
    intro he
    apply hc.2.1
    ext i
    simpa [he, realSign] using hv i
  let J := univ.filter (fun i => X i = 0)
  let K : Matrix J (Fin 41) ℝ := fun i j => A i.val j
  let L := K.mulVecLin
  have hker : LinearMap.ker L = Submodule.span ℝ {v} := by
    ext w
    constructor
    · intro hw
      have hline := cocircuit_kernel_line A X v w hc hv (uniform_real_injective A hu) (by
        intro i hi
        have hxi : X i = 0 := by rw [hv i, hi]; simp [realSign]
        have hrow := congrArg (fun z : J → ℝ => z ⟨i, mem_filter.mpr ⟨mem_univ _, hxi⟩⟩)
          (LinearMap.mem_ker.mp hw)
        exact hrow)
      obtain ⟨c, hcw⟩ := hline
      exact Submodule.mem_span_singleton.mpr ⟨c, hcw.symm⟩
    · intro hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      apply LinearMap.mem_ker.mpr
      ext i
      change ∑ j, (A i.val j : ℝ) * (c * v j) = 0
      have hxi : X i.val = 0 := (mem_filter.mp i.property).2
      rw [hv i.val] at hxi
      have hz := (realSign_zero_iff _).mp hxi
      calc
        (∑ j, (A i.val j : ℝ) * (c * v j)) = c * ∑ j, (A i.val j : ℝ) * v j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = 0 := by rw [hz, mul_zero]
  have hdim := L.finrank_range_add_finrank_ker
  rw [hker, finrank_span_singleton hvne] at hdim
  have hrange := Submodule.finrank_le (LinearMap.range L)
  have hlow : 40 ≤ J.card := by
    simp only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] at hdim hrange
    have hcard : Fintype.card J = J.card := Fintype.card_coe _
    omega
  have hupper := rational_uniform_zero_count A hu v hvne
  have heq : univ.filter (fun i => (∑ j, (A i j : ℝ) * v j) = 0) = J := by
    ext i
    simp only [mem_filter, mem_univ, true_and, J]
    rw [hv i]
    exact (realSign_zero_iff _).symm
  rw [heq] at hupper
  change J.card = 40
  omega

#print axioms uniform_real_minors
#print axioms uniform_real_injective
#print axioms uniform_cocircuit_zero_count
end
end ADKZPricing
