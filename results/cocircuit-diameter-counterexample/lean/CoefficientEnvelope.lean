import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.Polynomial.Eval.Degree

/- Uniform, deliberately loose coefficient envelopes. All bounds depend
   on dimension and entry size, never on enumerating bases. -/
namespace ADKZPricing
open Polynomial Finset
noncomputable section

def linearEntry (a d : ℤ) : Polynomial ℤ := C a + X * C d

def CoeffEnvelope (p : Polynomial ℤ) (D : ℕ) (B : ℤ) : Prop :=
  (∀ k, D < k → p.coeff k = 0) ∧ (∀ k, |p.coeff k| ≤ B)

theorem envelope_one : CoeffEnvelope (1 : Polynomial ℤ) 0 1 := by
  constructor
  · intro k hk
    simp [Polynomial.coeff_one, Nat.ne_of_gt hk]
  · intro k
    simp only [Polynomial.coeff_one]
    split_ifs <;> norm_num

theorem linear_mul_coeff_zero (a d : ℤ) (p : Polynomial ℤ) :
    (linearEntry a d * p).coeff 0 = a * p.coeff 0 := by
  simp [linearEntry, add_mul, mul_assoc]

theorem linear_mul_coeff_succ (a d : ℤ) (p : Polynomial ℤ) (k : ℕ) :
    (linearEntry a d * p).coeff (k + 1) =
      a * p.coeff (k + 1) + d * p.coeff k := by
  simp [linearEntry, add_mul, mul_assoc]

theorem envelope_linear_mul (a d : ℤ) (p : Polynomial ℤ) (N : ℕ) (B H : ℤ)
    (hB : 0 ≤ B) (hH : 0 ≤ H) (ha : |a| ≤ B) (hd : |d| ≤ B)
    (hp : CoeffEnvelope p N H) :
    CoeffEnvelope (linearEntry a d * p) (N + 1) (2 * B * H) := by
  constructor
  · intro k hk
    cases k with
    | zero => omega
    | succ k =>
      rw [linear_mul_coeff_succ, hp.1 _ (by omega), hp.1 _ (by omega)]
      ring
  · intro k
    cases k with
    | zero =>
      rw [linear_mul_coeff_zero, abs_mul]
      have h := mul_le_mul ha (hp.2 0) (abs_nonneg _) hB
      nlinarith
    | succ k =>
      rw [linear_mul_coeff_succ]
      calc
        |a * p.coeff (k + 1) + d * p.coeff k| ≤
            |a| * |p.coeff (k + 1)| + |d| * |p.coeff k| := by
          simpa only [abs_mul] using abs_add_le (a * p.coeff (k + 1)) (d * p.coeff k)
        _ ≤ B * H + B * H := add_le_add
          (mul_le_mul ha (hp.2 _) (abs_nonneg _) hB)
          (mul_le_mul hd (hp.2 _) (abs_nonneg _) hB)
        _ = 2 * B * H := by ring

theorem envelope_linear_product {ι : Type*} (s : Finset ι) (a d : ι → ℤ)
    (B : ℤ) (hB : 0 ≤ B) (ha : ∀ i ∈ s, |a i| ≤ B)
    (hd : ∀ i ∈ s, |d i| ≤ B) :
    CoeffEnvelope (∏ i ∈ s, linearEntry (a i) (d i)) s.card ((2 * B) ^ s.card) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using envelope_one
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_not_mem hi]
    have hs := ih (fun j hj => ha j (mem_insert_of_mem hj))
      (fun j hj => hd j (mem_insert_of_mem hj))
    have h := envelope_linear_mul (a i) (d i) _ s.card B ((2 * B) ^ s.card)
      hB (pow_nonneg (by omega) _) (ha i (mem_insert_self _ _))
      (hd i (mem_insert_self _ _)) hs
    simpa only [pow_succ, mul_comm] using h

theorem envelope_signed (p : Polynomial ℤ) (N : ℕ) (B : ℤ) (u : ℤˣ)
    (hp : CoeffEnvelope p N B) : CoeffEnvelope (u • p) N B := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simpa using hp
  · simpa [CoeffEnvelope, Polynomial.coeff_smul, Units.smul_def] using hp

theorem envelope_sum {ι : Type*} (s : Finset ι) (p : ι → Polynomial ℤ)
    (N : ℕ) (B : ℤ) (hp : ∀ i ∈ s, CoeffEnvelope (p i) N B) :
    CoeffEnvelope (∑ i ∈ s, p i) N (s.card * B) := by
  constructor
  · intro k hk
    simp only [Polynomial.finset_sum_coeff]
    exact Finset.sum_eq_zero (fun i hi => (hp i hi).1 k hk)
  · intro k
    rw [Polynomial.finset_sum_coeff]
    calc
      |∑ i ∈ s, (p i).coeff k| ≤ ∑ i ∈ s, |(p i).coeff k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ s, B := Finset.sum_le_sum (fun i hi => (hp i hi).2 k)
      _ = s.card * B := by simp

theorem envelope_determinant {r : ℕ} (A D : Matrix (Fin r) (Fin r) ℤ)
    (B : ℤ) (hB : 0 ≤ B) (ha : ∀ i j, |A i j| ≤ B) (hd : ∀ i j, |D i j| ≤ B) :
    CoeffEnvelope (Matrix.det (fun i j => linearEntry (A i j) (D i j))) r
      (Nat.factorial r * (2 * B) ^ r) := by
  rw [Matrix.det_apply]
  have h := envelope_sum Finset.univ
    (fun σ : Equiv.Perm (Fin r) => Equiv.Perm.sign σ •
      ∏ i, linearEntry (A (σ i) i) (D (σ i) i)) r ((2 * B) ^ r) (by
        intro σ _
        apply envelope_signed
        simpa using envelope_linear_product Finset.univ
          (fun i => A (σ i) i) (fun i => D (σ i) i) B hB
          (fun i _ => ha (σ i) i) (fun i _ => hd (σ i) i))
  simpa only [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] using h

def linearMatrix {n r : ℕ} (A D : Matrix (Fin n) (Fin r) ℤ) :
    Matrix (Fin n) (Fin r) (Polynomial ℤ) :=
  fun i j => linearEntry (A i j) (D i j)

theorem envelope_adjugate {r : ℕ} (A D : Matrix (Fin r) (Fin r) ℤ)
    (B : ℤ) (hB : 1 ≤ B) (ha : ∀ i j, |A i j| ≤ B) (hd : ∀ i j, |D i j| ≤ B)
    (j b : Fin r) :
    CoeffEnvelope ((linearMatrix A D).adjugate j b) r
      (Nat.factorial r * (2 * B) ^ r) := by
  rw [Matrix.adjugate_apply]
  let A' := A.updateRow b (Pi.single j 1)
  let D' := D.updateRow b 0
  have heq : (linearMatrix A D).updateRow b (Pi.single j 1) = linearMatrix A' D' := by
    ext i k
    by_cases hi : i = b
    · subst i
      by_cases hk : k = j <;> simp [linearMatrix, linearEntry, A', D', hk, Pi.single_apply]
    · simp [linearMatrix, A', D', Matrix.updateRow_apply, hi]
  rw [heq]
  apply envelope_determinant A' D' B (by omega)
  · intro i k
    by_cases hi : i = b
    · subst i
      by_cases hk : k = j <;>
        simp [A', hk, Pi.single_apply, show (0 : ℤ) ≤ B by omega, hB]
    · simpa [A', Matrix.updateRow_apply, hi] using ha i k
  · intro i k
    by_cases hi : i = b
    · subst i
      simp [D', show (0 : ℤ) ≤ B by omega]
    · simpa [D', Matrix.updateRow_apply, hi] using hd i k

theorem envelope_remove_common_power (Z W : Polynomial ℤ) (m N : ℕ) (H : ℤ)
    (hf : Z = X ^ m * W) (hZ : CoeffEnvelope Z N H) : CoeffEnvelope W N H := by
  have hc (k : ℕ) : W.coeff k = Z.coeff (k + m) := by
    rw [hf, Polynomial.coeff_X_pow_mul]
  constructor
  · intro k hk
    rw [hc]
    exact hZ.1 _ (by omega)
  · intro k
    rw [hc]
    exact hZ.2 _

theorem envelope_slack {r : ℕ} (a d : Fin r → ℤ) (W : Fin r → Polynomial ℤ)
    (N : ℕ) (B H : ℤ) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (ha : ∀ j, |a j| ≤ B) (hd : ∀ j, |d j| ≤ B)
    (hW : ∀ j, CoeffEnvelope (W j) N H) :
    CoeffEnvelope (∑ j, linearEntry (a j) (d j) * W j) (N + 1)
      (r * (2 * B * H)) := by
  simpa only [Finset.card_univ, Fintype.card_fin] using
    envelope_sum Finset.univ (fun j => linearEntry (a j) (d j) * W j) (N + 1)
      (2 * B * H) (fun j _ => envelope_linear_mul _ _ _ _ _ _ hB hH (ha j) (hd j) (hW j))

/-- The envelope includes every sign choice on a slack, and either
    orientation of a kernel. No sign patterns are enumerated. -/
theorem envelope_neg (p : Polynomial ℤ) (N : ℕ) (H : ℤ)
    (hp : CoeffEnvelope p N H) : CoeffEnvelope (-p) N H := by
  simpa [CoeffEnvelope] using hp

theorem envelope_weaken (p : Polynomial ℤ) (N : ℕ) (H K : ℤ)
    (hp : CoeffEnvelope p N H) (hHK : H ≤ K) : CoeffEnvelope p N K :=
  ⟨hp.1, fun k => (hp.2 k).trans hHK⟩

theorem envelope_add (p q : Polynomial ℤ) (N : ℕ) (H K : ℤ)
    (hp : CoeffEnvelope p N H) (hq : CoeffEnvelope q N K) :
    CoeffEnvelope (p + q) N (H + K) := by
  constructor
  · intro k hk
    simp [Polynomial.coeff_add, hp.1 k hk, hq.1 k hk]
  · intro k
    rw [Polynomial.coeff_add]
    exact (abs_add_le _ _).trans (add_le_add (hp.2 k) (hq.2 k))

theorem envelope_tail_mass (p : Polynomial ℤ) (N : ℕ) (H : ℤ)
    (hH : 0 ≤ H) (hp : CoeffEnvelope p N H) :
    (∑ k ∈ range p.natDegree, |(p.coeff (k + 1) : ℚ)|) ≤ (N : ℚ) * H := by
  have hdeg : p.natDegree ≤ N := Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hp.1
  calc
    (∑ k ∈ range p.natDegree, |(p.coeff (k + 1) : ℚ)|) ≤
        ∑ _k ∈ range p.natDegree, (H : ℚ) := by
      apply Finset.sum_le_sum
      intro k _
      exact_mod_cast hp.2 (k + 1)
    _ = (p.natDegree : ℚ) * H := by simp
    _ ≤ (N : ℚ) * H := mul_le_mul_of_nonneg_right
      (by exact_mod_cast hdeg) (by exact_mod_cast hH)

#print axioms envelope_determinant
#print axioms envelope_adjugate
#print axioms envelope_remove_common_power
#print axioms envelope_slack
#print axioms envelope_tail_mass
end
end ADKZPricing
