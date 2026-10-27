import Shared
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-! Uniform existence of the frozen Shared.normalForm, over polynomial coefficients.
No positivity condition on p is needed. Only the three minor relations are used. -/
namespace Makonzi
open scoped BigOperators
noncomputable section

abbrev NFQuotient (p : Fin 3 → ℕ) := SourceRing p ⧸ minorIdeal p

def nfQuot (p : Fin 3 → ℕ) : SourceRing p →+* NFQuotient p :=
  Ideal.Quotient.mk (minorIdeal p)

def nfCoeff (p : Fin 3 → ℕ) : CoeffRing p →+* NFQuotient p :=
  (nfQuot p).comp (coeffEmbed p)

local instance (p : Fin 3 → ℕ) : Algebra (CoeffRing p) (NFQuotient p) :=
  (nfCoeff p).toAlgebra

def nfW (p : Fin 3 → ℕ) (i : Fin 3) : NFQuotient p := nfQuot p (W p i)

def nfSpan (p : Fin 3 → ℕ) : Submodule (CoeffRing p) (NFQuotient p) :=
  Submodule.span (CoeffRing p) (Set.range fun t : Fin 3 × ℕ => nfW p t.1 ^ t.2)

lemma nfCoeff_arm (p : Fin 3 → ℕ) (i : Fin 3) :
    nfCoeff p (armCoeff p i) = nfQuot p (V p i) := by
  simp [nfCoeff, coeffEmbed, armCoeff, V, MvPolynomial.rename_X]

lemma nf_xy (p : Fin 3 → ℕ) :
    nfW p 0 * nfW p 1 = nfCoeff p (armCoeff p 0 * armCoeff p 1) := by
  have h : W p 1 * W p 0 - V p 0 * V p 1 ∈ minorIdeal p :=
    Ideal.subset_span (by simp)
  have h' := (Ideal.Quotient.eq_zero_iff_mem).2 h
  change nfQuot p (W p 1 * W p 0 - V p 0 * V p 1) = 0 at h'
  simpa [map_sub, map_mul, sub_eq_zero, nfW, mul_comm, nfCoeff_arm] using h'

lemma nf_xz (p : Fin 3 → ℕ) :
    nfW p 0 * nfW p 2 =
      nfCoeff p (armCoeff p 1) * nfW p 2 +
      nfCoeff p (armCoeff p 1 * armCoeff p 2) := by
  have h : W p 2 * W p 0 - (W p 2 + V p 2) * V p 1 ∈ minorIdeal p :=
    Ideal.subset_span (by simp)
  have h' := (Ideal.Quotient.eq_zero_iff_mem).2 h
  change nfQuot p (W p 2 * W p 0 - (W p 2 + V p 2) * V p 1) = 0 at h'
  have he := sub_eq_zero.mp (by simpa only [map_sub, map_mul, map_add] using h')
  simpa [nfW, map_mul, nfCoeff_arm, add_mul, mul_add, mul_comm] using he

lemma nf_yz (p : Fin 3 → ℕ) :
    nfW p 1 * nfW p 2 =
      nfCoeff p (armCoeff p 0) * nfW p 2 - nfCoeff p (armCoeff p 2) * nfW p 1 := by
  have h : W p 1 * (W p 2 + V p 2) - V p 0 * W p 2 ∈ minorIdeal p :=
    Ideal.subset_span (by simp)
  have h' := (Ideal.Quotient.eq_zero_iff_mem).2 h
  change nfQuot p (W p 1 * (W p 2 + V p 2) - V p 0 * W p 2) = 0 at h'
  have he := sub_eq_zero.mp (by simpa only [map_sub, map_mul, map_add] using h')
  have he' : nfW p 1 * (nfW p 2 + nfCoeff p (armCoeff p 2)) =
      nfCoeff p (armCoeff p 0) * nfW p 2 := by simpa [nfW, nfCoeff_arm] using he
  linear_combination he'

lemma nf_power_mem (p : Fin 3 → ℕ) (i : Fin 3) (n : ℕ) :
    nfW p i ^ n ∈ nfSpan p :=
  Submodule.subset_span ⟨(i,n), rfl⟩

/-- A mixed-power induction using an actual minor relation; no degree bound. -/
lemma nf_mixed_power (p : Fin 3 → ℕ) (i j : Fin 3) (α β γ : CoeffRing p)
    (h : nfW p i * nfW p j =
      nfCoeff p α * nfW p i + nfCoeff p β * nfW p j + nfCoeff p γ) (n : ℕ) :
    nfW p i * nfW p j ^ n ∈ nfSpan p := by
  induction n with
  | zero => simpa using nf_power_mem p i 1
  | succ n ih =>
    have hα := (nfSpan p).smul_mem α ih
    have hβ := (nfSpan p).smul_mem β (nf_power_mem p j (n+1))
    have hγ := (nfSpan p).smul_mem γ (nf_power_mem p j n)
    have he : nfW p i * nfW p j ^ (n+1) =
        nfCoeff p α * (nfW p i * nfW p j ^ n) +
        nfCoeff p β * nfW p j ^ (n+1) + nfCoeff p γ * nfW p j ^ n := by
      calc
        _ = (nfW p i * nfW p j) * nfW p j ^ n := by ring
        _ = _ := by rw [h]; ring
    rw [he]
    exact (nfSpan p).add_mem ((nfSpan p).add_mem hα hβ) hγ

lemma nf_mul_power_mem (p : Fin 3 → ℕ) (i j : Fin 3) (n : ℕ) :
    nfW p i * nfW p j ^ n ∈ nfSpan p := by
  fin_cases i <;> fin_cases j
  · simpa [← pow_succ'] using nf_power_mem p 0 (n+1)
  · exact nf_mixed_power p 0 1 0 0 (armCoeff p 0 * armCoeff p 1) (by simpa using nf_xy p) n
  · exact nf_mixed_power p 0 2 0 (armCoeff p 1) (armCoeff p 1 * armCoeff p 2)
      (by simpa using nf_xz p) n
  · exact nf_mixed_power p 1 0 0 0 (armCoeff p 0 * armCoeff p 1)
      (by simpa [mul_comm] using nf_xy p) n
  · simpa [← pow_succ'] using nf_power_mem p 1 (n+1)
  · exact nf_mixed_power p 1 2 (-armCoeff p 2) (armCoeff p 0) 0
      (by simpa [sub_eq_add_neg, add_comm] using nf_yz p) n
  · exact nf_mixed_power p 2 0 (armCoeff p 1) 0 (armCoeff p 1 * armCoeff p 2)
      (by simpa [mul_comm] using nf_xz p) n
  · exact nf_mixed_power p 2 1 (armCoeff p 0) (-armCoeff p 2) 0
      (by simpa [sub_eq_add_neg, add_comm, mul_comm] using nf_yz p) n
  · simpa [← pow_succ'] using nf_power_mem p 2 (n+1)

lemma nf_mul_mem (p : Fin 3 → ℕ) (i : Fin 3) {q : NFQuotient p}
    (hq : q ∈ nfSpan p) : nfW p i * q ∈ nfSpan p := by
  induction hq using Submodule.span_induction with
  | mem q hq =>
    rcases hq with ⟨⟨j,n⟩, rfl⟩
    exact nf_mul_power_mem p i j n
  | zero => simp
  | add a b ha hb ia ib => simpa [mul_add] using (nfSpan p).add_mem ia ib
  | smul a q hq ih =>
    simpa [Algebra.smul_def, mul_left_comm] using (nfSpan p).smul_mem a ih

/-- Arbitrary source polynomials lie in the coefficient span of pure powers. -/
lemma nf_source_mem (p : Fin 3 → ℕ) (f : SourceRing p) : nfQuot p f ∈ nfSpan p := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have h := (nfSpan p).smul_mem (MvPolynomial.C a) (nf_power_mem p 0 0)
    change nfCoeff p (MvPolynomial.C a) * nfW p 0 ^ 0 ∈ nfSpan p at h
    simpa [nfCoeff, coeffEmbed] using h
  | add f g hf hg => simpa using (nfSpan p).add_mem hf hg
  | mul_X f v hf =>
    cases v with
    | inl i => simpa [nfW, mul_comm] using nf_mul_mem p i hf
    | inr e =>
      have h := (nfSpan p).smul_mem (MvPolynomial.X e) hf
      change nfCoeff p (MvPolynomial.X e) * nfQuot p f ∈ nfSpan p at h
      simpa [nfCoeff, coeffEmbed, MvPolynomial.rename_X, mul_comm] using h

/-- A finite support supplies one common exponent bound for all three arms. -/
lemma nf_bounded_mem (p : Fin 3 → ℕ) (q : NFQuotient p) (hq : q ∈ nfSpan p) :
    ∃ N : ℕ, q ∈ Submodule.span (CoeffRing p)
      (Set.range fun t : Fin 3 × Fin (N+1) => nfW p t.1 ^ t.2.val) := by
  classical
  obtain ⟨d, hd⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hq
  let N := d.support.sup (fun t => t.2)
  refine ⟨N, ?_⟩
  rw [← hd]
  apply Submodule.sum_mem
  intro t ht
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨(t.1, ⟨t.2, Nat.lt_succ_of_le (Finset.le_sup ht)⟩), rfl⟩

/-- Uniform normal-form existence, with coefficient polynomials in C[v].
The existential N is unbounded; even empty arms are permitted. -/
theorem normalForm_exists (p : Fin 3 → ℕ) (f : SourceRing p) :
    ∃ (N : ℕ) (r : CoeffRing p) (a b c : Fin N → CoeffRing p),
      f - normalForm p N r a b c ∈ minorIdeal p := by
  classical
  obtain ⟨N, hN⟩ := nf_bounded_mem p (nfQuot p f) (nf_source_mem p f)
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun (CoeffRing p)).mp hN
  refine ⟨N, d (0,0) + d (1,0) + d (2,0),
    (fun k => d (0,k.succ)), (fun k => d (1,k.succ)), (fun k => d (2,k.succ)), ?_⟩
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  change nfQuot p (f - normalForm p N _ _ _ _) = 0
  rw [map_sub, sub_eq_zero]
  change (∑ t : Fin 3 × Fin (N+1),
    nfCoeff p (d t) * nfW p t.1 ^ t.2.val) = nfQuot p f at hd
  simp only [Fintype.sum_prod_type] at hd
  rw [Fin.sum_univ_three] at hd
  simp only [Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ] at hd
  have hn : nfQuot p (normalForm p N (d (0,0) + d (1,0) + d (2,0))
      (fun k => d (0,k.succ)) (fun k => d (1,k.succ)) (fun k => d (2,k.succ))) =
      nfCoeff p (d (0,0)) + nfCoeff p (d (1,0)) + nfCoeff p (d (2,0)) +
      (∑ k : Fin N, nfCoeff p (d (0,k.succ)) * nfW p 0 ^ (k.val+1)) +
      (∑ k : Fin N, nfCoeff p (d (1,k.succ)) * nfW p 1 ^ (k.val+1)) +
      (∑ k : Fin N, nfCoeff p (d (2,k.succ)) * nfW p 2 ^ (k.val+1)) := by
    simp [normalForm, nfCoeff, nfW]
  rw [hn]
  calc
    _ = _ := hd.symm
    _ = _ := by ring

#print axioms normalForm_exists
end
end Makonzi
