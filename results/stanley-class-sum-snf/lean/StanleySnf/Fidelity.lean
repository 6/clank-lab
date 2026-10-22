import StanleySnf.Defs

/-!
# Fidelity of the definitions

Checks, in Lean, that the definitions in `Defs.lean` mean what the claim says:

* `classSum_coeff`: `classSum n μ` has coefficient `1` at every permutation of cycle type
  `μ` and `0` elsewhere (each element of the class is counted once);
* `rep_spec`: `rep μ` has cycle type `μ`;
* `parts_eq_iff_isConj`: having cycle type `μ` is the same as being conjugate to `rep μ`,
  so the support of `classSum n μ` is exactly a conjugacy class;
* `M_structure`: `K_(n) * K_ν = ∑_μ M n μ ν • K_μ`, i.e. `M n` is the matrix of left
  multiplication by `K_(n)` on the span of the class sums, in the class-sum basis.
-/

open Equiv Finset

namespace StanleySnf

namespace Fid

theorem classSum_coeff {n : ℕ} (μ : n.Partition) (y : Perm (Fin n)) :
    (classSum n μ).coeff y = if y.partition.parts = μ.parts then 1 else 0 := by
  unfold classSum
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [sum_ite_eq']
  simp

theorem rep_spec {n : ℕ} (μ : n.Partition) : (rep μ).partition.parts = μ.parts :=
  Classical.choose_spec (exists_rep μ)

theorem parts_eq_iff_isConj {n : ℕ} (μ : n.Partition) (σ : Perm (Fin n)) :
    σ.partition.parts = μ.parts ↔ IsConj σ (rep μ) := by
  rw [Perm.partition_eq_of_isConj, Nat.Partition.ext_iff, rep_spec]

/-- The coefficient of `K_(n) * K_ν` at `y`. -/
theorem coeff_prod {n : ℕ} (hn : 0 < n) (ν : n.Partition) (y : Perm (Fin n)) :
    (classSum n (Nat.Partition.indiscrete n) * classSum n ν).coeff y =
      ∑ b ∈ univ.filter (fun b : Perm (Fin n) => b.partition.parts = ν.parts),
        if (y * b⁻¹).partition.parts = {n} then (1 : ℤ) else 0 := by
  rw [show classSum n ν = ∑ b ∈ univ.filter (fun b : Perm (Fin n) => b.partition.parts = ν.parts),
      MonoidAlgebra.single b (1 : ℤ) from rfl]
  rw [mul_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine sum_congr rfl fun b _ => ?_
  rw [MonoidAlgebra.coeff_mul_single_apply, classSum_coeff, Nat.Partition.indiscrete_parts hn.ne']
  split_ifs <;> simp

theorem partition_conj {n : ℕ} (g y : Perm (Fin n)) :
    (g * y * g⁻¹).partition = y.partition :=
  (Perm.partition_eq_of_isConj).mp (isConj_iff.mpr ⟨g⁻¹, by group⟩)

/-- Conjugation invariance of the coefficients of `K_(n) * K_ν`. -/
theorem coeff_prod_conj {n : ℕ} (hn : 0 < n) (ν : n.Partition) (g y : Perm (Fin n)) :
    (classSum n (Nat.Partition.indiscrete n) * classSum n ν).coeff (g * y * g⁻¹) =
      (classSum n (Nat.Partition.indiscrete n) * classSum n ν).coeff y := by
  rw [coeff_prod hn, coeff_prod hn]
  refine sum_nbij' (fun b => g⁻¹ * b * g) (fun b => g * b * g⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    rw [show g⁻¹ * b * g = g⁻¹ * b * g⁻¹⁻¹ by group, partition_conj, hb]
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    rw [partition_conj, hb]
  · intro b _; group
  · intro b _; group
  · intro b _
    rw [show g * y * g⁻¹ * b⁻¹ = g * (y * (g⁻¹ * b * g)⁻¹) * g⁻¹ by group, partition_conj]

/-- `M n` is the matrix of left multiplication by `K_(n)` in the class-sum basis. -/
theorem M_structure {n : ℕ} (hn : 0 < n) (ν : n.Partition) :
    classSum n (Nat.Partition.indiscrete n) * classSum n ν =
      ∑ μ : n.Partition, M n μ ν • classSum n μ := by
  ext y
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.coeff_smul_apply, classSum_coeff, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  -- the unique partition `μ₀` with the cycle type of `y`
  let μ₀ : n.Partition :=
    ⟨y.partition.parts, fun h => y.partition.parts_pos h, by
      rw [y.partition.parts_sum, Fintype.card_fin]⟩
  rw [sum_eq_single μ₀]
  · rw [if_pos rfl]
    obtain ⟨c, hc⟩ := isConj_iff.mp ((parts_eq_iff_isConj μ₀ y).mp rfl)
    unfold M
    rw [← hc, coeff_prod_conj hn]
  · intro μ _ hμ
    rw [if_neg]
    intro h
    exact hμ (Nat.Partition.ext h.symm)
  · intro h; exact absurd (mem_univ _) h

end Fid

end StanleySnf
