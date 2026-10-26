import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Tactic
namespace Donkin
/-- The uniform local lemma's small-prime congruence hypotheses can be met
    by arbitrarily large auxiliary primes, using the actual Dirichlet theorem. -/
theorem auxiliary_prime (n B : ℕ) :
    ∃ q : ℕ, B < q ∧ q.Prime ∧
      ∀ ell : ℕ, ell.Prime → ell ≤ n → (q : ZMod ell) = 1 := by
  classical
  let small := (Finset.range (n + 1)).filter Nat.Prime
  let M := ∏ ell ∈ small, ell
  have hM : M ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro ell hell
    exact (Finset.mem_filter.mp hell).2.ne_zero
  obtain ⟨q, hqB, hqp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq B hM (Nat.coprime_one_left M)
  refine ⟨q, hqB, hqp, ?_⟩
  intro ell hell hle
  have hel : ell ∈ small := by
    simp only [small, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hell⟩
  have hd : ell ∣ M := Finset.dvd_prod_of_mem id hel
  have hlocal : q ≡ 1 [MOD ell] := hmod.of_dvd hd
  exact_mod_cast (ZMod.natCast_eq_natCast_iff q 1 ell).mpr hlocal

#check Nat.chineseRemainderOfFinset
#check Nat.forall_exists_prime_gt_and_modEq
#print axioms Donkin.auxiliary_prime
/-- Nonzero residues at finitely many distinct primes lift to arbitrarily
    large PRIME seeds; no primality of a specific CRT representative assumed. -/
theorem prime_seed_lift (t : Finset ℕ) (a : ℕ → ℕ)
    (ht : ∀ ell ∈ t, ell.Prime)
    (ha : ∀ ell ∈ t, ¬ ell ∣ a ell) (B : ℕ) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧ ∀ ell ∈ t, p ≡ a ell [MOD ell] := by
  classical
  let M := ∏ ell ∈ t, ell
  have hM : M ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun ell hel => (ht ell hel).ne_zero)
  have hpair : Set.Pairwise (t : Set ℕ) (Function.onFun Nat.Coprime id) := by
    intro i hi j hj hij
    exact (Nat.coprime_primes (ht i hi) (ht j hj)).mpr hij
  obtain ⟨A, hA⟩ := Nat.chineseRemainderOfFinset a id t
    (fun ell hel => (ht ell hel).ne_zero) hpair
  have hcop : A.Coprime M := by
    apply Nat.coprime_prod_right_iff.mpr
    intro ell hel
    apply Nat.Coprime.symm
    apply (ht ell hel).coprime_iff_not_dvd.mpr
    intro hd
    apply ha ell hel
    exact Nat.modEq_zero_iff_dvd.mp ((hA ell hel).symm.trans (Nat.modEq_zero_iff_dvd.mpr hd))
  obtain ⟨p, hpB, hpp, hpA⟩ := Nat.forall_exists_prime_gt_and_modEq B hM hcop
  refine ⟨p, hpB, hpp, ?_⟩
  intro ell hel
  exact (hpA.of_dvd (Finset.dvd_prod_of_mem id hel)).trans (hA ell hel)

#print axioms Donkin.prime_seed_lift

end Donkin
