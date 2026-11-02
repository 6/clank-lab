import BaseREhrhart.Geometry
import BaseREhrhart.Data

/-! Complete integer quotient decomposition.
All inequalities below are derived from the actual convex hull in Geometry. -/
noncomputable section
open scoped BigOperators
namespace BaseREhrhart

/-- Last barycentric numerator, an integer determined by the actual point. -/
def numerator (t : ℕ) (x : Fin 5 → ℤ) : ℤ := (t : ℤ) - ∑ i, x i

def IntegerCone (t : ℕ) (x : Fin 5 → ℤ) : Prop :=
  0 ≤ numerator t x ∧ ∀ i, 0 ≤ (D : ℤ) * x i + coefficients i * numerator t x

lemma coefficients_sum_real : (∑ i : Fin 5, (coefficients i : ℝ)) + 1 = (D : ℝ) := by
  exact_mod_cast c_sum

lemma mem_dilate_iff_integerCone (t : ℕ) (x : Fin 5 → ℤ) :
    (fun i => (x i : ℝ)) ∈ dilate t ↔ IntegerCone t x := by
  rw [mem_dilate_iff]
  have hD : (0 : ℝ) < D := by exact_mod_cast D_pos
  have hD0 : (D : ℝ) ≠ 0 := ne_of_gt hD
  have hnum : (numerator t x : ℝ) = (t : ℝ) - ∑ i, (x i : ℝ) := by
    simp [numerator]
  constructor
  · rintro ⟨μ, hμ, hs, hx⟩
    have hsum : ∑ i : Fin 5, (x i : ℝ) =
        (∑ i : Fin 5, μ i.succ) - (∑ i : Fin 5, (coefficients i : ℝ)) * μ 0 := by
      simp_rw [hx, Finset.sum_sub_distrib, ← Finset.sum_mul]
    have hμ0 : (D : ℝ) * μ 0 = numerator t x := by
      rw [Fin.sum_univ_succ] at hs
      rw [hnum, hsum]
      linear_combination hs - μ 0 * coefficients_sum_real
    constructor
    · exact_mod_cast (show (0 : ℝ) ≤ (numerator t x : ℝ) by rw [← hμ0]; exact mul_nonneg hD.le (hμ 0))
    · intro i
      have hi : (0 : ℝ) ≤ (D : ℝ) * x i + (coefficients i : ℝ) * numerator t x := by
        rw [hx, ← hμ0]
        nlinarith [hμ i.succ]
      exact_mod_cast hi
  · rintro ⟨hk, hi⟩
    let a : ℝ := (numerator t x : ℝ) / D
    let μ : Fin 6 → ℝ := Fin.cons a (fun i => (x i : ℝ) + (coefficients i : ℝ) * a)
    have ha : (0 : ℝ) ≤ a := div_nonneg (by exact_mod_cast hk) hD.le
    have hDa : (D : ℝ) * a = numerator t x := by dsimp [a]; field_simp
    refine ⟨μ, ?_, ?_, ?_⟩
    · intro j
      refine Fin.cases ha (fun i => ?_) j
      change 0 ≤ (x i : ℝ) + (coefficients i : ℝ) * a
      have hiR : (0 : ℝ) ≤ (D : ℝ) * x i + (coefficients i : ℝ) * numerator t x := by
        exact_mod_cast hi i
      apply (mul_nonneg_iff_of_pos_left hD).mp
      calc
        0 ≤ (D : ℝ) * x i + (coefficients i : ℝ) * numerator t x := hiR
        _ = (D : ℝ) * ((x i : ℝ) + (coefficients i : ℝ) * a) := by
          rw [← hDa]
          ring
    · rw [Fin.sum_univ_succ]
      change a + ∑ i : Fin 5, ((x i : ℝ) + (coefficients i : ℝ) * a) = t
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      rw [hnum] at hDa
      linear_combination hDa + a * coefficients_sum_real
    · intro i
      simp [μ]

/-- Integer quotient and remainder for a certified residue. -/
def quotient (b : Fin D) (i : Fin 5) : ℤ := coefficients i * (b.val : ℤ) / D

def remainder (b : Fin D) (i : Fin 5) : ℤ := coefficients i * (b.val : ℤ) % D

def heightZ (b : Fin D) : ℤ := b.val - ∑ i, quotient b i

lemma residue_euclidean (b : Fin D) (i : Fin 5) :
    remainder b i + (D : ℤ) * quotient b i = coefficients i * b.val :=
  Int.emod_add_ediv _ _

lemma remainder_bounds (b : Fin D) (i : Fin 5) :
    0 ≤ remainder b i ∧ remainder b i < (D : ℤ) := by
  have hD : (0 : ℤ) < D := by exact_mod_cast D_pos
  exact ⟨Int.emod_nonneg _ (ne_of_gt hD), Int.emod_lt_of_pos _ hD⟩

lemma heightZ_identity (b : Fin D) :
    (D : ℤ) * heightZ b = b.val + ∑ i, remainder b i := by
  have he : ∑ i, remainder b i + (D : ℤ) * ∑ i, quotient b i =
      (∑ i, coefficients i) * b.val := by
    simpa [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      using Finset.sum_congr rfl
        (fun i _ => residue_euclidean b i)
  dsimp [heightZ]
  nlinarith [c_sum]

lemma heightZ_nonneg (b : Fin D) : 0 ≤ heightZ b := by
  have hD : (0 : ℤ) < D := by exact_mod_cast D_pos
  have hs : 0 ≤ ∑ i, remainder b i := Finset.sum_nonneg (fun i _ => (remainder_bounds b i).1)
  have := heightZ_identity b
  have hb : (0 : ℤ) ≤ b.val := Nat.cast_nonneg _
  nlinarith

lemma height_cast (b : Fin D) : (height b : ℤ) = heightZ b := by
  have hr : ∀ i, ((cNat i * b.val) % D : ℤ) = remainder b i := by
    intro i
    simp [remainder, Int.natCast_mod, Nat.cast_mul, cNat_cast]
  have hh : ((b.val + ∑ i, (cNat i * b.val) % D : ℕ) : ℤ) =
      (D : ℤ) * heightZ b := by
    simpa [Nat.cast_add, Nat.cast_sum, hr] using (heightZ_identity b).symm
  have hD : (D : ℤ) ≠ 0 := by norm_num [D]
  change (((b.val + ∑ i, (cNat i * b.val) % D) / D : ℕ) : ℤ) = _
  rw [Int.natCast_ediv, hh, Int.mul_ediv_cancel_left _ hD]

/-- Complete quotient cover: every residue appears, with no omitted class. -/
def Pieces (t : ℕ) :=
  {p : Fin D × (Fin 6 → ℕ) // height p.1 + ∑ j, p.2 j = t}

def reconstruct (b : Fin D) (n : Fin 6 → ℕ) : Fin 5 → ℤ :=
  fun i => (n i.succ : ℤ) - coefficients i * (n 0 : ℤ) - quotient b i

lemma reconstruct_numerator (t : ℕ) (b : Fin D) (n : Fin 6 → ℕ)
    (ht : height b + ∑ j, n j = t) :
    numerator t (reconstruct b n) = (D : ℤ) * n 0 + b.val := by
  have hn : (height b : ℤ) + ((n 0 : ℕ) : ℤ) + ∑ i : Fin 5, (n i.succ : ℤ) = t := by
    have := congrArg (fun k : ℕ => (k : ℤ)) ht
    simpa only [Nat.cast_add, Nat.cast_sum, Fin.sum_univ_succ, add_assoc] using this
  have hh := height_cast b
  dsimp [heightZ] at hh
  dsimp [numerator, reconstruct]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
  linear_combination -hn + hh + (n 0 : ℤ) * c_sum

lemma reconstruct_cone (t : ℕ) (b : Fin D) (n : Fin 6 → ℕ)
    (ht : height b + ∑ j, n j = t) : IntegerCone t (reconstruct b n) := by
  have hD : (0 : ℤ) ≤ D := by norm_num [D]
  constructor
  · rw [reconstruct_numerator _ _ _ ht]
    positivity
  · intro i
    rw [reconstruct_numerator _ _ _ ht]
    change 0 ≤ (D : ℤ) * ((n i.succ : ℤ) - coefficients i * (n 0 : ℤ) - quotient b i) +
      coefficients i * ((D : ℤ) * n 0 + b.val)
    have he := residue_euclidean b i
    have hr := (remainder_bounds b i).1
    nlinarith [mul_nonneg hD (Nat.cast_nonneg (n i.succ))]

/-- This map's codomain refers to the original convex hull, not digit semantics. -/
def toLattice (t : ℕ) (p : Pieces t) : LatticePoints t :=
  ⟨reconstruct p.val.1 p.val.2,
    (mem_dilate_iff_integerCone _ _).mpr (reconstruct_cone _ _ _ p.property)⟩

lemma toLattice_injective (t : ℕ) : Function.Injective (toLattice t) := by
  rintro ⟨⟨b, n⟩, hn⟩ ⟨⟨b', n'⟩, hn'⟩ heq
  have hx : reconstruct b n = reconstruct b' n' := congrArg Subtype.val heq
  have hk : (D : ℤ) * n 0 + b.val = (D : ℤ) * n' 0 + b'.val := by
    rw [← reconstruct_numerator _ _ _ hn, ← reconstruct_numerator _ _ _ hn', hx]
  change (537824 : ℤ) * (n 0 : ℤ) + b.val = 537824 * (n' 0 : ℤ) + b'.val at hk
  have hb : b = b' := by
    have hblt : (b.val : ℤ) < D := by exact_mod_cast b.isLt
    have hb'lt : (b'.val : ℤ) < D := by exact_mod_cast b'.isLt
    have hD : (D : ℤ) = 537824 := rfl
    have hz : (b.val : ℤ) = b'.val := by omega
    exact Fin.ext (by exact_mod_cast hz)
  subst b'
  have hn0 : n 0 = n' 0 := by
    have hD : (D : ℤ) = 537824 := rfl
    omega
  have hntail : ∀ i : Fin 5, n i.succ = n' i.succ := by
    intro i
    have hi := congrFun hx i
    dsimp [reconstruct] at hi
    rw [hn0] at hi
    omega
  have hnn : n = n' := by
    funext j
    exact Fin.cases hn0 hntail j
  subst n'
  rfl

lemma toLattice_surjective (t : ℕ) : Function.Surjective (toLattice t) := by
  rintro ⟨x, hx⟩
  obtain ⟨hk0, hcone⟩ := (mem_dilate_iff_integerCone t x).mp hx
  let k : ℤ := numerator t x
  let q : ℤ := k / D
  have hD : (0 : ℤ) < D := by exact_mod_cast D_pos
  have hr0 : 0 ≤ k % D := Int.emod_nonneg _ (ne_of_gt hD)
  have hrlt : k % D < (D : ℤ) := Int.emod_lt_of_pos _ hD
  let b : Fin D := ⟨(k % D).toNat, by omega⟩
  have hb : (b.val : ℤ) = k % D := Int.toNat_of_nonneg hr0
  have hk : k = (D : ℤ) * q + b.val := by
    rw [hb]
    exact (Int.emod_add_ediv k D).symm.trans (add_comm _ _)
  let nz : Fin 6 → ℤ := Fin.cons q (fun i => x i + coefficients i * q + quotient b i)
  have hnz : ∀ j, 0 ≤ nz j := by
    intro j
    refine Fin.cases (Int.ediv_nonneg hk0 hD.le) (fun i => ?_) j
    change 0 ≤ x i + coefficients i * q + quotient b i
    have hi : 0 ≤ (D : ℤ) * (x i + coefficients i * q + quotient b i) + remainder b i := by
      calc
        0 ≤ (D : ℤ) * x i + coefficients i * k := hcone i
        _ = (D : ℤ) * (x i + coefficients i * q + quotient b i) + remainder b i := by
          rw [hk]
          linear_combination -residue_euclidean b i
    have hr := (remainder_bounds b i).2
    change remainder b i < (537824 : ℤ) at hr
    change 0 ≤ (537824 : ℤ) * (x i + coefficients i * q + quotient b i) + remainder b i at hi
    omega
  let n : Fin 6 → ℕ := fun j => (nz j).toNat
  have hn : ∀ j, (n j : ℤ) = nz j := fun j => Int.toNat_of_nonneg (hnz j)
  have hsum : height b + ∑ j, n j = t := by
    have hsZ : (height b : ℤ) + ∑ j, (n j : ℤ) = (t : ℤ) := by
      simp_rw [hn]
      rw [height_cast, Fin.sum_univ_succ]
      change heightZ b + (q + ∑ i : Fin 5, (x i + coefficients i * q + quotient b i)) = t
      dsimp [heightZ]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]
      have hkt : k = (t : ℤ) - ∑ i, x i := rfl
      linear_combination -hk + hkt + q * c_sum
    exact_mod_cast hsZ
  refine ⟨⟨(b, n), hsum⟩, ?_⟩
  apply Subtype.ext
  funext i
  change (n i.succ : ℤ) - coefficients i * (n 0 : ℤ) - quotient b i = x i
  rw [hn, hn]
  dsimp [nz]
  simp only [Fin.cons_succ, Fin.cons_zero]
  ring

/-- The complete, unconditional semantic bridge at every dilation parameter. -/
noncomputable def latticeEquivPieces (t : ℕ) : LatticePoints t ≃ Pieces t :=
  (Equiv.ofBijective (toLattice t) ⟨toLattice_injective t, toLattice_surjective t⟩).symm

end BaseREhrhart
