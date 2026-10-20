import EKG.Basic

namespace EKG

noncomputable def actualA (n : ℕ) : ℕ :=
  if n = 0 then 1 else if n = 1 then 2 else
  chooseNext (fun i : Fin n => actualA i.val) (actualA (n-1))
termination_by n
decreasing_by all_goals omega

@[simp] theorem actualA_zero : actualA 0 = 1 := by rw [actualA]; simp
@[simp] theorem actualA_one : actualA 1 = 2 := by rw [actualA]; simp

theorem actualA_step (n : ℕ) (hn : 2 ≤ n) :
    actualA n = chooseNext (fun i : Fin n => actualA i.val) (actualA (n-1)) := by
  rw [actualA]
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  simp [h0, h1]

theorem actualA_properties (n : ℕ) :
    0 < actualA n ∧ (1 ≤ n → ∃ r, r.Prime ∧ r ∣ actualA n) ∧
    ∀ i < n, actualA i ≠ actualA n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : 2 ≤ n
    · have hprev := ih (n-1) (by omega)
      have hspec := chooseNext_spec (fun i : Fin n => actualA i.val)
        (hprev.2.1 (by omega))
      rw [← actualA_step n hn] at hspec
      refine ⟨hspec.1, ?_, ?_⟩
      · intro _
        obtain ⟨r, hr, _, hrc⟩ := hspec.2.2
        exact ⟨r, hr, hrc⟩
      · intro i hi
        exact hspec.2.1 ⟨i, hi⟩
    · have hc : n = 0 ∨ n = 1 := by omega
      rcases hc with hc | hc
      · subst n
        refine ⟨by simp, ?_, ?_⟩ <;> intros <;> omega
      · subst n
        refine ⟨by simp, ?_, ?_⟩
        · intro _
          exact ⟨2, Nat.prime_two, by simp⟩
        · intro i hi
          have : i = 0 := by omega
          subst i
          simp

theorem actualA_injective : Function.Injective actualA := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hc | hc
  · exact (actualA_properties j).2.2 i hc hij
  · exact (actualA_properties i).2.2 j hc hij.symm

theorem actualA_eligible (n : ℕ) (hn : 2 ≤ n) :
    SharedPrime (actualA (n-1)) (actualA n) := by
  have hspec := chooseNext_spec (fun i : Fin n => actualA i.val)
    ((actualA_properties (n-1)).2.1 (by omega))
  rw [← actualA_step n hn] at hspec
  exact hspec.2.2

theorem actualA_minimal (n : ℕ) (hn : 2 ≤ n) (m : ℕ) (hm : 0 < m)
    (hfree : ¬ UsedBefore actualA n m)
    (helig : SharedPrime (actualA (n-1)) m) : actualA n ≤ m := by
  rw [actualA_step n hn]
  apply chooseNext_le
  refine ⟨hm, ?_, helig⟩
  intro i he
  exact hfree ⟨i.val, i.isLt, he⟩

noncomputable def canonical : GreedySeq where
  a := actualA
  seed_zero := actualA_zero
  seed_one := actualA_one
  positive := fun n => (actualA_properties n).1
  injective := actualA_injective
  eligible := actualA_eligible
  minimal := actualA_minimal

theorem actualA_gcd_rule (n : ℕ) (hn : 2 ≤ n) :
    1 < Nat.gcd (actualA (n-1)) (actualA n) :=
  (sharedPrime_iff_gcd (actualA_properties (n-1)).1).mp (actualA_eligible n hn)

theorem actualA_gcd_minimal (n : ℕ) (hn : 2 ≤ n) (m : ℕ) (hm : 0 < m)
    (hfree : ¬ UsedBefore actualA n m)
    (helig : 1 < Nat.gcd (actualA (n-1)) m) : actualA n ≤ m :=
  actualA_minimal n hn m hm hfree
    ((sharedPrime_iff_gcd (actualA_properties (n-1)).1).mpr helig)

theorem GreedySeq.unique (s t : GreedySeq) : s.a = t.a := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : 2 ≤ n
    · have hprev : s.a (n-1) = t.a (n-1) := ih (n-1) (by omega)
      have hsfree : ¬ UsedBefore s.a n (t.a n) := by
        rintro ⟨i, hi, hei⟩
        rw [ih i hi] at hei
        have := t.injective hei
        omega
      have htfree : ¬ UsedBefore t.a n (s.a n) := by
        rintro ⟨i, hi, hei⟩
        rw [← ih i hi] at hei
        have := s.injective hei
        omega
      have hst : SharedPrime (s.a (n-1)) (t.a n) := by
        rw [hprev]
        exact t.eligible n hn
      have hts : SharedPrime (t.a (n-1)) (s.a n) := by
        rw [← hprev]
        exact s.eligible n hn
      exact le_antisymm
        (s.minimal n hn (t.a n) (t.positive n) hsfree hst)
        (t.minimal n hn (s.a n) (s.positive n) htfree hts)
    · have hc : n = 0 ∨ n = 1 := by omega
      rcases hc with hc | hc <;> subst n
      · simp only [s.seed_zero, t.seed_zero]
      · simp only [s.seed_one, t.seed_one]

end EKG
