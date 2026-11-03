import GR22.Spec

/-!
# Unit B: Schur functions at the alphabet `1 - x - y`

(unit B). From the Jacobi–Trudi definition of `schur`, assuming only
the values of `h_n[1 - x - y]` (`AtAComplete`, unit A's statement, taken as a hypothesis):

* hook+column `(α, 2^β, 1^γ)` with `α ≥ 2`: subtract each column from the next, expand along
  the first row (now `(Q, 0, …, 0)`), peel off the `β` rows with diagonal `xy`, and solve the
  remaining tridiagonal determinant by its three-term recurrence;
* second part `≥ 3`: the first two rows are both constantly `Q`;
* the column `(1^N)` at `x = 1`: the matrix is lower triangular with diagonal `-y`.
-/

noncomputable section
namespace GR22

open MvPolynomial Matrix

/-- `h_n[1 - x - y]` for an integer index. -/
def unitB_H (n : ℤ) : XY := atA (completeZ n)

/-- The column difference `h_n[A] - h_(n-1)[A]`. -/
def unitB_D (n : ℤ) : XY := unitB_H n - unitB_H (n - 1)

/-- The Jacobi–Trudi matrix `(f (ν_i - i + j))` of a list `ν`. -/
def unitB_jt (f : ℤ → XY) (ν : List ℕ) : Matrix (Fin ν.length) (Fin ν.length) XY :=
  fun i j => f ((ν.get i : ℤ) - (i.val : ℤ) + (j.val : ℤ))

/-- The tridiagonal determinant `det (D (1 - i + j))` of size `n`. -/
def unitB_T (n : ℕ) : XY :=
  Matrix.det (Matrix.of fun i j : Fin n => unitB_D (1 - (i.val : ℤ) + j.val))

theorem unitB_atA_schur (ν : List ℕ) : atA (schur ν) = (unitB_jt unitB_H ν).det := by
  exact AlgHom.map_det atA _

section values

variable (hA : AtAComplete)
include hA

omit hA in
theorem unitB_H_neg (n : ℤ) (h : n < 0) : unitB_H n = 0 := by
  simp [unitB_H, completeZ, not_le.mpr h]

theorem unitB_H_zero : unitB_H 0 = 1 := by
  simp [unitB_H, completeZ, hA.1]

theorem unitB_H_one : unitB_H 1 = 1 - x - y := by
  simp [unitB_H, completeZ, hA.2.1]

theorem unitB_H_ge_two (n : ℤ) (h : 2 ≤ n) : unitB_H n = Q := by
  simp only [unitB_H, completeZ, show (0 : ℤ) ≤ n by omega, ↓reduceIte]
  exact hA.2.2 _ (by omega)

theorem unitB_D_zero : unitB_D 0 = 1 := by
  simp [unitB_D, unitB_H_zero hA, unitB_H_neg (-1) (by norm_num)]

theorem unitB_D_one : unitB_D 1 = -(x + y) := by
  simp only [unitB_D, sub_self, unitB_H_one hA, unitB_H_zero hA]
  ring

theorem unitB_D_two : unitB_D 2 = x * y := by
  rw [unitB_D, unitB_H_ge_two hA 2 le_rfl, show (2 : ℤ) - 1 = 1 by norm_num, unitB_H_one hA, Q]
  ring

theorem unitB_D_ge_three (n : ℤ) (h : 3 ≤ n) : unitB_D n = 0 := by
  rw [unitB_D, unitB_H_ge_two hA n (by omega), unitB_H_ge_two hA (n - 1) (by omega), sub_self]

omit hA in
theorem unitB_D_neg (n : ℤ) (h : n < 0) : unitB_D n = 0 := by
  rw [unitB_D, unitB_H_neg n h, unitB_H_neg (n - 1) (by omega), sub_self]

end values

/-- Laplace expansion along a first row of the form `(a, 0, …, 0)`. -/
theorem unitB_det_row0 {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) XY)
    (h : ∀ j : Fin n, A 0 j.succ = 0) : A.det = A 0 0 * (A.submatrix Fin.succ Fin.succ).det := by
  rw [det_succ_row_zero, Fin.sum_univ_succ]
  simp [h]

/-- Jacobi–Trudi: if row 0 vanishes past its first entry, peel it off. -/
theorem unitB_det_cons (f : ℤ → XY) (a : ℕ) (l : List ℕ)
    (h : ∀ j : ℕ, 1 ≤ j → f ((a : ℤ) + j) = 0) :
    (unitB_jt f (a :: l)).det = f a * (unitB_jt f l).det := by
  have hsub : (unitB_jt f (a :: l)).submatrix (Fin.succ (n := l.length)) Fin.succ =
      unitB_jt f l := Matrix.ext fun i j => by
    simp only [unitB_jt, submatrix_apply, List.get_eq_getElem, Fin.val_succ,
      List.getElem_cons_succ]
    congr 1
    push_cast
    ring
  refine (unitB_det_row0 (n := l.length) (unitB_jt f (a :: l)) fun j => ?_).trans ?_
  · simpa [unitB_jt] using h (j.val + 1) (by omega)
  · rw [hsub]
    simp [unitB_jt]

/-- Jacobi–Trudi: subtract each column from the next; if row 0 becomes `(f a, 0, …, 0)`, the
determinant is `f a` times the Jacobi–Trudi determinant of the differences on the tail. -/
theorem unitB_det_cons_diff (f : ℤ → XY) (a : ℕ) (l : List ℕ)
    (h : ∀ j : ℕ, 1 ≤ j → f ((a : ℤ) + j) - f ((a : ℤ) + j - 1) = 0) :
    (unitB_jt f (a :: l)).det = f a * (unitB_jt (fun n => f n - f (n - 1)) l).det := by
  let A : Matrix (Fin (l.length + 1)) (Fin (l.length + 1)) XY := unitB_jt f (a :: l)
  let B : Matrix (Fin (l.length + 1)) (Fin (l.length + 1)) XY := Matrix.of fun i j =>
    Fin.cases (A i 0) (fun j' : Fin l.length => A i j'.succ - A i j'.castSucc) j
  have hAB : A.det = B.det :=
    det_eq_of_forall_col_eq_smul_add_pred (fun _ => 1) (fun i => rfl) (fun i j => by
      simp [B])
  have hsub : B.submatrix Fin.succ Fin.succ = unitB_jt (fun n => f n - f (n - 1)) l :=
    Matrix.ext fun i j => by
      simp only [B, A, unitB_jt, submatrix_apply, of_apply, Fin.cases_succ,
        List.get_eq_getElem, Fin.val_succ, Fin.val_castSucc, List.getElem_cons_succ]
      congr 2 <;> push_cast <;> ring
  have hrow : ∀ j : Fin l.length, B 0 j.succ = 0 := fun j => by
    have := h (j.val + 1) (by omega)
    simp only [B, A, unitB_jt, of_apply, Fin.cases_succ, List.get_eq_getElem, Fin.val_zero,
      Fin.val_succ, Fin.val_castSucc, List.getElem_cons_zero] at this ⊢
    convert this using 3 <;> push_cast <;> ring
  change A.det = _
  rw [hAB, unitB_det_row0 B hrow, hsub]
  simp [B, A, unitB_jt]

/-- Determinants of equal matrices on equal-sized index types. -/
theorem unitB_det_congr {m n : ℕ} (hmn : m = n) (A : Matrix (Fin m) (Fin m) XY)
    (B : Matrix (Fin n) (Fin n) XY) (hAB : ∀ i j, A i j = B (Fin.cast hmn i) (Fin.cast hmn j)) :
    A.det = B.det := by
  subst hmn
  exact congrArg Matrix.det (Matrix.ext fun i j => by simpa using hAB i j)

section main

variable (hA : AtAComplete)
include hA

theorem unitB_twos (β : ℕ) (l : List ℕ) :
    (unitB_jt unitB_D (List.replicate β 2 ++ l)).det = (x * y) ^ β * (unitB_jt unitB_D l).det := by
  induction β with
  | zero => simp
  | succ β ih =>
    rw [List.replicate_succ, List.cons_append,
      unitB_det_cons _ _ _ (fun j hj => unitB_D_ge_three hA _ (by push_cast; omega)), ih,
      show ((2 : ℕ) : ℤ) = 2 by norm_num, unitB_D_two hA]
    ring

omit hA in
theorem unitB_ones (γ : ℕ) :
    (unitB_jt unitB_D (List.replicate γ 1)).det = unitB_T γ :=
  unitB_det_congr (List.length_replicate) _ _ (fun i j => by
    simp [unitB_jt])

theorem unitB_T_rec (n : ℕ) :
    unitB_T (n + 2) = -(x + y) * unitB_T (n + 1) - x * y * unitB_T n := by
  let M : Matrix (Fin (n + 2)) (Fin (n + 2)) XY :=
    Matrix.of fun i j => unitB_D (1 - (i.val : ℤ) + j.val)
  have hM : ∀ i j, M i j = unitB_D (1 - (i.val : ℤ) + j.val) := fun _ _ => rfl
  have hs : ∀ i : Fin n, ((Fin.succ (0 : Fin (n + 1))).succAbove i.succ).val = i.val + 2 :=
    fun i => by simp
  have h0 : (M.submatrix (Fin.succAbove 0) Fin.succ).det = unitB_T (n + 1) := by
    rw [unitB_T]
    refine congrArg Matrix.det (Matrix.ext fun i j => ?_)
    simp only [submatrix_apply, Fin.succAbove_zero, hM, of_apply, Fin.val_succ]
    refine congrArg unitB_D ?_
    push_cast
    ring
  have h1 : (M.submatrix (Fin.succAbove (Fin.succ 0)) Fin.succ).det = x * y * unitB_T n := by
    rw [unitB_det_row0 _ fun j => ?_]
    · simp only [submatrix_apply, Fin.succAbove_ne_zero_zero (Fin.succ_ne_zero _), hM,
        Fin.val_zero, Fin.val_succ]
      have e : (1 : ℤ) - ((0 : ℕ) : ℤ) + ((0 + 1 : ℕ) : ℤ) = 2 := by norm_num
      have hT : ((M.submatrix (Fin.succ 0).succAbove Fin.succ).submatrix Fin.succ Fin.succ).det =
          unitB_T n := by
        rw [unitB_T]
        refine congrArg Matrix.det (Matrix.ext fun i j => ?_)
        simp only [submatrix_apply, hM, of_apply, hs, Fin.val_succ]
        refine congrArg unitB_D ?_
        push_cast
        ring
      rw [e, unitB_D_two hA, hT]
    · simp only [submatrix_apply, Fin.succAbove_ne_zero_zero (Fin.succ_ne_zero _), hM,
        Fin.val_zero, Fin.val_succ]
      exact unitB_D_ge_three hA _ (by push_cast; omega)
  change M.det = _
  rw [det_succ_column_zero, Fin.sum_univ_succ, Fin.sum_univ_succ, h0, h1]
  have hrest : ∀ i : Fin n, M i.succ.succ 0 = 0 := fun i =>
    unitB_D_neg _ (by simp; omega)
  simp only [hrest, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, hM, Fin.val_zero,
    Fin.val_succ]
  rw [show (1 : ℤ) - ((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ) = 1 by norm_num,
    show (1 : ℤ) - (((0 : ℕ) + 1 : ℕ) : ℤ) + ((0 : ℕ) : ℤ) = 0 by norm_num,
    unitB_D_one hA, unitB_D_zero hA]
  ring

omit hA in
theorem unitB_twoComplete_succ (n : ℕ) : twoComplete (n + 1) = x ^ (n + 1) + y * twoComplete n := by
  rw [twoComplete, Finset.sum_range_succ, twoComplete, Finset.mul_sum, Nat.sub_self, pow_zero,
    mul_one, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
  ring

theorem unitB_T_eq (n : ℕ) : unitB_T n = (-1) ^ n * twoComplete n := by
  suffices ∀ n, unitB_T n = (-1) ^ n * twoComplete n ∧
      unitB_T (n + 1) = (-1) ^ (n + 1) * twoComplete (n + 1) from (this n).1
  intro n
  induction n with
  | zero =>
    refine ⟨by simp [unitB_T, twoComplete], ?_⟩
    rw [unitB_T, det_fin_one, of_apply, unitB_twoComplete_succ]
    simp only [Fin.val_zero, Nat.cast_zero, sub_zero, add_zero, unitB_D_one hA]
    simp [twoComplete]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [unitB_T_rec hA, ih.1, ih.2, unitB_twoComplete_succ (n + 1), unitB_twoComplete_succ n]
    ring

/-- Unit B, part 1: hook+column shapes with first part `α ≥ 2`. -/
theorem unitB_hook (α β γ : ℕ) (hα : 2 ≤ α) :
    atA (schur (α :: (List.replicate β 2 ++ List.replicate γ 1))) =
      (-1) ^ γ * Q * (x * y) ^ β * twoComplete γ := by
  rw [unitB_atA_schur, unitB_det_cons_diff unitB_H α _ fun j hj => by
    rw [unitB_H_ge_two hA _ (by omega), unitB_H_ge_two hA _ (by omega), sub_self],
    unitB_H_ge_two hA α (by omega)]
  change Q * (unitB_jt unitB_D _).det = _
  rw [unitB_twos hA, unitB_ones, unitB_T_eq hA]
  ring

/-- Unit B, part 2: partitions whose second part is at least `3`. -/
theorem unitB_vanish (N : ℕ) (μ : List ℕ) (hμ : IsPartitionOf N μ) (h3 : 3 ≤ μ.getD 1 0) :
    atA (schur μ) = 0 := by
  rcases μ with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp at h3
  · simp at h3
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h3
  have hba : b ≤ a := (List.pairwise_cons.1 hμ.1).1 b (by simp)
  rw [unitB_atA_schur]
  refine det_zero_of_row_eq (i := 0) (j := 1) (by simp) (funext fun j => ?_)
  simp only [unitB_jt, List.get_eq_getElem, Fin.val_zero, Fin.val_one, List.getElem_cons_zero,
    List.getElem_cons_succ]
  rw [unitB_H_ge_two hA _ (by omega), unitB_H_ge_two hA _ (by omega)]

/-- Unit B, part 3: the column `(1^N)` at `x = 1`. -/
theorem unitB_column (N : ℕ) : atXOne (atA (schur (List.replicate N 1))) = (-y) ^ N := by
  have hx : atXOne x = 1 := by simp [atXOne, x]
  have hy : atXOne y = y := by simp [atXOne, y]
  rw [unitB_atA_schur, AlgHom.map_det, AlgHom.mapMatrix_apply, det_of_isLowerTriangular]
  · simp only [map_apply, unitB_jt, List.get_eq_getElem, List.getElem_replicate, sub_add_cancel,
      Nat.cast_one]
    rw [unitB_H_one hA, map_sub, map_sub, map_one, hx, hy, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, List.length_replicate]
    ring
  · intro i j hij
    rw [OrderDual.toDual_lt_toDual] at hij
    simp only [map_apply, unitB_jt, List.get_eq_getElem, List.getElem_replicate]
    rw [unitB_H_ge_two hA _ (by omega), Q, map_mul, map_sub, map_sub, map_one, hx, hy]
    ring

end main

/-- Unit B: Schur functions at `1 - x - y`, given `h_n[1 - x - y]` (unit A's statement). -/
theorem schur_atA_of (hA : AtAComplete) : SchurAtA :=
  ⟨unitB_hook hA, unitB_vanish hA, unitB_column hA⟩

end GR22

#print axioms GR22.schur_atA_of
