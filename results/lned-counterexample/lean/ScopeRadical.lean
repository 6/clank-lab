import ScopeIdeal

namespace LNEDScope
open Polynomial LNEDExtension
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]

lemma low_degree_vanish (a : K[X]) (d N : ℕ)
    (hgen : ∀ i : ℕ, i < d → ∀ m : ℕ, N ≤ m → F ((X : K[X]) ^ i * a ^ m) = 0)
    (p : K[X]) (hp : p.natDegree < d) (m : ℕ) (hm : N ≤ m) : F (p * a ^ m) = 0 := by
  have he : p * a ^ m = ∑ i ∈ p.support, p.coeff i • ((X : K[X]) ^ i * a ^ m) := by
    conv_lhs => rw [← p.sum_C_mul_X_pow_eq]
    simp only [Polynomial.sum_def, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [smul_eq_C_mul]
    ring
  rw [he, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_smul, hgen i (lt_of_le_of_lt (le_natDegree_of_mem_supp i hi) hp) m hm]
  simp

/-- Division induction implements finite generation over K[a] without assuming a uniform threshold. -/
lemma generators_vanish_all (a : K[X]) (ha : a.natDegree ≠ 0) (N : ℕ)
    (hgen : ∀ i : ℕ, i < a.natDegree → ∀ m : ℕ, N ≤ m → F ((X : K[X]) ^ i * a ^ m) = 0) :
    ∀ p : K[X], ∀ m : ℕ, N ≤ m → F (p * a ^ m) = 0 := by
  have hall : ∀ n : ℕ, ∀ p : K[X], p.natDegree = n →
      ∀ m : ℕ, N ≤ m → F (p * a ^ m) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hpn m hm
      have hrem := low_degree_vanish a a.natDegree N hgen (p % a) (natDegree_mod_lt p ha) m hm
      have hquot : F ((p / a) * a ^ (m + 1)) = 0 := by
        by_cases hq : p / a = 0
        · simp [hq]
        · have hp0 : p ≠ 0 := by intro hp0; apply hq; simp [hp0]
          have hdpos : 0 < a.degree := natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero ha)
          have hlt : (p / a).natDegree < n := by
            have ht := natDegree_lt_natDegree hq (degree_div_lt hp0 hdpos)
            omega
          exact ih _ hlt _ rfl (m + 1) (by omega)
      have he : p * a ^ m = (p % a) * a ^ m + (p / a) * a ^ (m + 1) := by
        have hdiv := EuclideanDomain.mod_add_div p a
        calc
          p * a ^ m = ((p % a) + a * (p / a)) * a ^ m := congrArg (fun q => q * a ^ m) hdiv.symm
          _ = _ := by rw [pow_succ]; ring
      rw [he, map_add, hrem, hquot, add_zero]
  intro p
  exact hall p.natDegree p rfl

lemma strong_radical_constant (c : K) (hc : (C c : K[X]) ∈ StrongRadical (image (1 : K))) : c = 0 := by
  obtain ⟨N, hN⟩ := hc 1
  have h := (mem_image_iff _).mp (hN N le_rfl)
  simp only [one_mul, ← map_pow, F_C] at h
  exact pow_eq_zero h

lemma strong_radical_uniform_generators (a : K[X]) (ha : a ∈ StrongRadical (image (1 : K))) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ i : ℕ, i < a.natDegree →
      ∀ m : ℕ, N ≤ m → F ((X : K[X]) ^ i * a ^ m) = 0 := by
  classical
  choose Ns hNs using (fun i : ℕ => ha ((X : K[X]) ^ i))
  let N := max 1 ((Finset.range a.natDegree).sup Ns)
  refine ⟨N, le_max_left _ _, ?_⟩
  intro i hi m hm
  apply (mem_image_iff _).mp
  apply hNs i m
  have hle : Ns i ≤ (Finset.range a.natDegree).sup Ns := Finset.le_sup (Finset.mem_range.mpr hi)
  exact le_trans hle (le_trans (le_max_right _ _) hm)

theorem strong_radical_eq_zero : StrongRadical (image (1 : K)) = {0} := by
  ext a
  constructor
  · intro ha
    change a = 0
    by_cases hd : a.natDegree = 0
    · have he := eq_C_of_natDegree_eq_zero hd
      have hc := strong_radical_constant (a.coeff 0) (by rwa [← he])
      rw [he, hc, C_0]
    · obtain ⟨N, hN, hgen⟩ := strong_radical_uniform_generators a ha
      have hall := generators_vanish_all a hd N hgen
      have hcontained : ((Ideal.span {a ^ N} : Ideal K[X]) : Set K[X]) ⊆ image (1 : K) := by
        intro p hp
        obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hp
        apply (mem_image_iff _).mpr
        simpa only [mul_comm] using hall q N le_rfl
      have hbot := no_nonzero_contained_ideal (Ideal.span {a ^ N}) hcontained
      have hmem : a ^ N ∈ (Ideal.span {a ^ N} : Ideal K[X]) := Ideal.subset_span (by simp)
      rw [hbot, Ideal.mem_bot] at hmem
      exact pow_eq_zero hmem
  · rintro rfl b
    refine ⟨1, ?_⟩
    intro m hm
    apply (mem_image_iff _).mpr
    simp [zero_pow (show m ≠ 0 by omega)]

theorem scope_endpoint : ScopeEndpoint K := ⟨no_nonzero_contained_ideal, strong_radical_eq_zero⟩

/-- Exact ideal-span/difference endpoint, with every multiplier and threshold visible. -/
theorem scope_literal :
    let V : Set K[X] := (fun f : K[X] => f - f.comp (X + 1)) ''
      ((Ideal.span {(X : K[X]) * (X - C (1 / 2 : K))} : Ideal K[X]) : Set K[X])
    (∀ J : Ideal K[X], (J : Set K[X]) ⊆ V → J = ⊥) ∧
    {a : K[X] | ∀ b : K[X], ∃ N : ℕ, ∀ m : ℕ, N ≤ m → b * a ^ m ∈ V} = {0} := by
  simpa only [ScopeEndpoint, StrongRadical, image, ideal, half_eq, one_mul, diff, shift, C_1] using
    (scope_endpoint (K := K))

#print axioms strong_radical_eq_zero
#print axioms scope_endpoint
#print axioms scope_literal
end LNEDScope
