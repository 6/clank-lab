import EKG.Bootstrap
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith

namespace EKG

theorem primeStructure_prime_Ioc_card (a b : ℕ) (hab : a ≤ b) :
    ((Finset.Ioc a b).filter Nat.Prime).card =
      Nat.primeCounting b - Nat.primeCounting a := by
  classical
  let A := (Finset.range (a+1)).filter Nat.Prime
  let B := (Finset.Ioc a b).filter Nat.Prime
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxB
    have ha := Finset.mem_range.mp (Finset.mem_filter.mp hxA).1
    have hb := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hxB).1).1
    omega
  have hun : A ∪ B = (Finset.range (b+1)).filter Nat.Prime := by
    ext x
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_range,
      Finset.mem_Ioc]
    constructor
    · rintro (⟨hx, hprime⟩ | ⟨⟨ha, hb⟩, hprime⟩)
      · exact ⟨by omega, hprime⟩
      · exact ⟨by omega, hprime⟩
    · rintro ⟨hx, hprime⟩
      by_cases ha : x ≤ a
      · exact Or.inl ⟨by omega, hprime⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, hprime⟩
  have hc := Finset.card_union_of_disjoint hdis
  rw [hun] at hc
  have hA : A.card = Nat.primeCounting a := by
    exact (Nat.count_eq_card_filter_range Nat.Prime (a+1)).symm
  have hB : ((Finset.range (b+1)).filter Nat.Prime).card = Nat.primeCounting b := by
    exact (Nat.count_eq_card_filter_range Nat.Prime (b+1)).symm
  rw [hA, hB] at hc
  change B.card = _
  omega

theorem primeStructure_prime_Ioc_sieve (a b : ℕ) (hab : a ≤ b) :
    Nat.primeCounting b - Nat.primeCounting a ≤ 48*((b-a)/210+1)+4 := by
  rw [← primeStructure_prime_Ioc_card a b hab]
  have he : Finset.Ioc a b = Finset.Ico (a+1) (a+1+(b-a)) := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [he]
  exact prime_interval_sieve (a+1) (b-a)

theorem primeStructure_sqrt_bound {p : ℕ} (hp : 4096 ≤ p) :
    32 * Nat.sqrt (2*p) ≤ p := by
  have hs := Nat.sqrt_le (2*p)
  by_contra hnot
  have hlt : p < 32 * Nat.sqrt (2*p) := by omega
  have hsq := Nat.mul_self_lt_mul_self hlt
  have hlarge : 4096*p ≤ p*p := Nat.mul_le_mul_right p hp
  nlinarith

/-- A purely arithmetic closing inequality, valid for every p >= 4096.
It uses the proved modulus-210 sieve, not an analytic prime estimate. -/
theorem primeStructure_large_count {p : ℕ} (hp : 4096 ≤ p) :
    Nat.primeCounting (Nat.sqrt (2*p)) +
      (Nat.primeCounting (p-1) - Nat.primeCounting (2*p/3)) <
      (p-1)/2 - p/3 + 1 := by
  have hs := primeStructure_sqrt_bound hp
  have hcount : Nat.primeCounting (Nat.sqrt (2*p)) ≤ Nat.sqrt (2*p)+1 := by
    exact Nat.count_le Nat.Prime
  have hint := primeStructure_prime_Ioc_sieve (2*p/3) (p-1) (by omega)
  omega

end EKG
