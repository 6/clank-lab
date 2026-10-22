import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Linarith

/-! Zero-based EKG: a(0)=1, a(1)=2. All prime factors, including 2,
are eligible. This is a new specification, not the odd-prime A373698 rule. -/
namespace EKG

def SharedPrime (x y : ℕ) : Prop :=
  ∃ q : ℕ, q.Prime ∧ q ∣ x ∧ q ∣ y

theorem sharedPrime_iff_gcd {x y : ℕ} (hx : 0 < x) :
    SharedPrime x y ↔ 1 < Nat.gcd x y := by
  unfold SharedPrime
  rw [← Nat.Prime.not_coprime_iff_dvd]
  change ¬ (Nat.gcd x y = 1) ↔ 1 < Nat.gcd x y
  have hpos := Nat.gcd_pos_of_pos_left y hx
  omega

def UsedBefore (a : ℕ → ℕ) (n m : ℕ) : Prop := ∃ i < n, a i = m

structure GreedySeq where
  a : ℕ → ℕ
  seed_zero : a 0 = 1
  seed_one : a 1 = 2
  positive : ∀ n, 0 < a n
  injective : Function.Injective a
  eligible : ∀ n, 2 ≤ n → SharedPrime (a (n-1)) (a n)
  minimal : ∀ n, 2 ≤ n → ∀ m, 0 < m →
    ¬ UsedBefore a n m → SharedPrime (a (n-1)) m → a n ≤ m

def NextCandidate {n : ℕ} (f : Fin n → ℕ) (b m : ℕ) : Prop :=
  0 < m ∧ (∀ i, f i ≠ m) ∧ SharedPrime b m

noncomputable def chooseNext {n : ℕ} (f : Fin n → ℕ) (b : ℕ) : ℕ := by
  classical
  exact if h : ∃ m, NextCandidate f b m then Nat.find h else 2

theorem nextCandidate_exists {n b : ℕ} (f : Fin n → ℕ)
    (hb : ∃ r, r.Prime ∧ r ∣ b) : ∃ m, NextCandidate f b m := by
  classical
  obtain ⟨r, hr, hrb⟩ := hb
  let M := Finset.univ.sup f
  have hbound : ∀ i, f i ≤ M := fun i => Finset.le_sup (Finset.mem_univ i)
  have hrpos := hr.pos
  refine ⟨r*(M+1), Nat.mul_pos hrpos (by omega), ?_, ?_⟩
  · intro i he
    have := hbound i
    nlinarith
  · exact ⟨r, hr, hrb, Nat.dvd_mul_right r (M+1)⟩

theorem chooseNext_spec {n b : ℕ} (f : Fin n → ℕ)
    (hb : ∃ r, r.Prime ∧ r ∣ b) : NextCandidate f b (chooseNext f b) := by
  classical
  unfold chooseNext
  have hex := nextCandidate_exists f hb
  simp only [dif_pos hex]
  exact Nat.find_spec hex

theorem chooseNext_le {n b m : ℕ} (f : Fin n → ℕ)
    (hm : NextCandidate f b m) : chooseNext f b ≤ m := by
  classical
  unfold chooseNext
  have hex : ∃ k, NextCandidate f b k := ⟨m, hm⟩
  simp only [dif_pos hex]
  exact Nat.find_min' hex hm

end EKG
