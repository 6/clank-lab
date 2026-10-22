import P16c.StringRelations
import P16c.GroupDefs

namespace P16c
variable {K : Type*} [Field K] [CharP K 2]
open scoped CharTwo
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

private def dWord (a b : K) (ha : a ≠ 0) : Fin 8 → (Mat K)ˣ :=
  let x := generators a b ha 1
  let y := generators a b ha 2
  ![1, x*y, (x*y)^2, (x*y)^3, x, (x*y)*x, (x*y)^2*x, (x*y)^3*x]

private def dMatrix (b : K) : Fin 8 → Mat K :=
  ![!![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1],
    !![1,1,0,0; b,1,1,1; b,0,1,1; 0,b,0,1],
    !![1+b,0,1,1; b,1,0,1; 0,0,1,0; b^2,0,b,1+b],
    !![1,1,1,0; 0,1,1,0; b,0,1,1; 0,b,b,1],
    !![1,0,0,0; 0,1,1,0; 0,0,1,0; 0,0,0,1],
    !![1,1,1,0; b,1,0,1; b,0,1,1; 0,b,b,1],
    !![1+b,0,1,1; b,1,1,1; 0,0,1,0; b^2,0,b,1+b],
    !![1,1,0,0; 0,1,0,0; b,0,1,1; 0,b,0,1]]

private def dMul : Fin 8 → Fin 8 → Fin 8 :=
  ![![0,1,2,3,4,5,6,7],
    ![1,2,3,0,5,6,7,4],
    ![2,3,0,1,6,7,4,5],
    ![3,0,1,2,7,4,5,6],
    ![4,7,6,5,0,3,2,1],
    ![5,4,7,6,1,0,3,2],
    ![6,5,4,7,2,1,0,3],
    ![7,6,5,4,3,2,1,0]]

private def dInv : Fin 8 → Fin 8 := ![0,3,2,1,4,5,6,7]

private lemma dWord_val (a b : K) (ha : a ≠ 0) (i : Fin 8) :
    ↑(dWord a b ha i) = dMatrix b i := by
  fin_cases i <;>
    simp only [dWord, Units.val_one, Units.val_mul, Units.val_pow_eq_pow_val,
      generators_one, generators_two] <;>
    ext j k <;> fin_cases j <;> fin_cases k <;>
    simp [dMatrix, r, r₁, Matrix.mul_apply, Fin.sum_univ_succ, pow_succ] <;>
    ring_nf <;> simp

private lemma dRow0 (b : K) (j : Fin 8) :
    dMatrix b 0 * dMatrix b j = dMatrix b (dMul 0 j) := by
  fin_cases j <;> ext k l <;> fin_cases k <;> fin_cases l <;>
    simp [dMatrix, dMul, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp

private lemma dRow1 (b : K) (j : Fin 8) :
    dMatrix b 1 * dMatrix b j = dMatrix b (dMul 1 j) := by
  fin_cases j <;> ext k l <;> fin_cases k <;> fin_cases l <;>
    simp [dMatrix, dMul, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp

private lemma dRow2 (b : K) (j : Fin 8) :
    dMatrix b 2 * dMatrix b j = dMatrix b (dMul 2 j) := by
  fin_cases j <;> ext k l <;> fin_cases k <;> fin_cases l <;>
    simp [dMatrix, dMul, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp

private lemma dRow3 (b : K) (j : Fin 8) :
    dMatrix b 3 * dMatrix b j = dMatrix b (dMul 3 j) := by
  fin_cases j <;> ext k l <;> fin_cases k <;> fin_cases l <;>
    simp [dMatrix, dMul, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp

private lemma dRow4 (b : K) (j : Fin 8) :
    dMatrix b 4 * dMatrix b j = dMatrix b (dMul 4 j) := by
  fin_cases j <;> ext k l <;> fin_cases k <;> fin_cases l <;>
    simp [dMatrix, dMul, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp

private lemma dRow5 (b : K) (j : Fin 8) :
    dMatrix b 5 * dMatrix b j = dMatrix b (dMul 5 j) := by
  fin_cases j <;> ext k l <;> fin_cases k <;> fin_cases l <;>
    simp [dMatrix, dMul, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp

private lemma dRow6 (b : K) (j : Fin 8) :
    dMatrix b 6 * dMatrix b j = dMatrix b (dMul 6 j) := by
  fin_cases j <;> ext k l <;> fin_cases k <;> fin_cases l <;>
    simp [dMatrix, dMul, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp

private lemma dRow7 (b : K) (j : Fin 8) :
    dMatrix b 7 * dMatrix b j = dMatrix b (dMul 7 j) := by
  fin_cases j <;> ext k l <;> fin_cases k <;> fin_cases l <;>
    simp [dMatrix, dMul, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp

private lemma dWord_mul (a b : K) (ha : a ≠ 0) (i j : Fin 8) :
    dWord a b ha i * dWord a b ha j = dWord a b ha (dMul i j) := by
  apply Units.ext
  simp only [Units.val_mul, dWord_val]
  fin_cases i
  · exact dRow0 b j
  · exact dRow1 b j
  · exact dRow2 b j
  · exact dRow3 b j
  · exact dRow4 b j
  · exact dRow5 b j
  · exact dRow6 b j
  · exact dRow7 b j

private lemma dWord_inv (a b : K) (ha : a ≠ 0) (i : Fin 8) :
    (dWord a b ha i)⁻¹ = dWord a b ha (dInv i) := by
  apply inv_eq_of_mul_eq_one_right
  rw [dWord_mul]
  fin_cases i <;> rfl

private lemma dWord_injective (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    Function.Injective (dWord a b ha) := by
  intro i j h
  have hm : dMatrix b i = dMatrix b j := by simpa only [dWord_val] using congrArg Units.val h
  have h00 := congrArg (fun M : Mat K => M 0 0) hm
  have h01 := congrArg (fun M : Mat K => M 0 1) hm
  have h02 := congrArg (fun M : Mat K => M 0 2) hm
  have h12 := congrArg (fun M : Mat K => M 1 2) hm
  fin_cases i <;> fin_cases j <;> first | rfl | simp_all [dMatrix]

/-- The common dihedral subgroup has exactly eight elements. -/
theorem d_card (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) : Nat.card (D a b ha) = 8 := by
  let H : Subgroup (Mat K)ˣ :=
    { carrier := Set.range (dWord a b ha)
      one_mem' := ⟨0, rfl⟩
      mul_mem' := by
        rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
        exact ⟨dMul i j, (dWord_mul a b ha i j).symm⟩
      inv_mem' := by
        rintro _ ⟨i, rfl⟩
        exact ⟨dInv i, (dWord_inv a b ha i).symm⟩ }
  have hD : D a b ha = H := by
    apply le_antisymm
    · apply (Subgroup.closure_le _).mpr
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact ⟨4, rfl⟩
      · refine ⟨7, ?_⟩
        apply Units.ext
        simp only [dWord_val]
        simp [dMatrix, r]
    · rintro g ⟨i, rfl⟩
      have hx : generators a b ha 1 ∈ D a b ha := Subgroup.subset_closure (by simp)
      have hy : generators a b ha 2 ∈ D a b ha := Subgroup.subset_closure (by simp)
      fin_cases i <;> simp only [dWord, Matrix.cons_val_zero, Matrix.cons_val_succ] <;>
        first | exact (D a b ha).one_mem | exact hx | exact hy |
          exact (D a b ha).mul_mem hx hy |
          exact (D a b ha).pow_mem ((D a b ha).mul_mem hx hy) _ |
          exact (D a b ha).mul_mem ((D a b ha).mul_mem hx hy) hx |
          exact (D a b ha).mul_mem ((D a b ha).pow_mem ((D a b ha).mul_mem hx hy) _) hx
  rw [hD]
  exact (Nat.card_congr (Equiv.ofInjective (dWord a b ha) (dWord_injective a b ha hb)).symm).trans (by simp)
end P16c
