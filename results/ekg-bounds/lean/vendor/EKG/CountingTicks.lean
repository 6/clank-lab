import EKG.CountingOccurrences
import EKG.EarlyEvens

/-! The exact finite tick count. The completed and late prime sets partition
the literal open interval P2; their cardinalities are proved from actual
prime introductions and the canonical sequence's injectivity. -/
namespace EKG.CanonicalCounting

open Classical

noncomputable def completedTickPrimes (u : ℕ) : Finset ℕ := by
  classical
  exact (P2 u).filter (fun p => UsedBefore canonical.a (u+1) (3*p))

theorem mem_P2_odd {u p : ℕ} (hu : 8 ≤ u) (hp : p ∈ P2 u) :
    p.Prime ∧ p ≠ 2 := by
  classical
  obtain ⟨hbelow, hlo, hhi⟩ := Finset.mem_filter.mp hp
  have hprime := (Nat.mem_primesBelow.mp hbelow).2
  have he : 14 ≤ e u := frontier_ge_fourteen canonical hu
  exact ⟨hprime, by intro h; subst p; omega⟩

theorem tickAbove_eq_image_completed (u : ℕ) (hu : 8 ≤ u) :
    Clock.tickAbove canonical u spanTickValue =
      (completedTickPrimes u).image (fun p => 3*p) := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨hoddAbove, htick⟩ := Finset.mem_filter.mp hw
    obtain ⟨hused, hodd, habove⟩ := Finset.mem_filter.mp hoddAbove
    obtain ⟨p, hp, hp2, rfl⟩ := htick
    have hused' := (Clock.mem_usedValues canonical u (3*p)).mp hused
    obtain ⟨i, hi, hval⟩ := hused'
    have hhalf : 2*p < e u :=
      used_tick_prime_below_frontier canonical hp hp2 hval (by omega)
    have hpP2 : p ∈ P2 u := by
      apply Finset.mem_filter.mpr
      exact ⟨Nat.mem_primesBelow.mpr ⟨by omega, hp⟩, habove, hhalf⟩
    apply Finset.mem_image.mpr
    exact ⟨p, Finset.mem_filter.mpr ⟨hpP2, ⟨i, hi, hval⟩⟩, rfl⟩
  · intro hw
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hpP2, hused⟩ := Finset.mem_filter.mp hp
    obtain ⟨hprime, hp2⟩ := mem_P2_odd hu hpP2
    have habove := (Finset.mem_filter.mp hpP2).2.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_, ?_, habove⟩, ?_⟩
    · exact (Clock.mem_usedValues canonical u (3*p)).mpr hused
    · exact primeStructure_tick_not_two_dvd hprime hp2
    · exact ⟨p, hprime, hp2, rfl⟩

theorem tickAbove_card_eq_completed (u : ℕ) (hu : 8 ≤ u) :
    (Clock.tickAbove canonical u spanTickValue).card =
      (completedTickPrimes u).card := by
  classical
  rw [tickAbove_eq_image_completed u hu]
  apply Finset.card_image_of_injective
  intro p q hpq
  dsimp at hpq
  omega

/-- A P2 prime has already been introduced. Its tick is missing precisely
when that actual introduction is at one of the last two prefix indices. -/
theorem P2_tick_missing_iff_late {u p : ℕ} (hu : 8 ≤ u)
    (hpP2 : p ∈ P2 u) :
    (¬ UsedBefore canonical.a (u+1) (3*p)) ↔
      NewPrimeAt canonical (u-1) p ∨ NewPrimeAt canonical u p := by
  classical
  obtain ⟨hp, hp2⟩ := mem_P2_odd hu hpP2
  obtain ⟨n, hn⟩ := every_prime_introduced canonical hp
  have hhalf : 2*p < frontier canonical u :=
    (Finset.mem_filter.mp hpP2).2.2
  have hnu : n ≤ u := (introduction_le_iff_twice_lt_frontier hn hp2).mpr hhalf
  rw [tick_used_iff hn hp2]
  constructor
  · intro hlate
    have hcases : n = u-1 ∨ n = u := by omega
    rcases hcases with h | h
    · exact Or.inl (h ▸ hn)
    · exact Or.inr (h ▸ hn)
  · intro hlate
    rcases hlate with h | h
    · have hindex : n = u-1 := introduction_unique hn h
      omega
    · have hindex : n = u := introduction_unique hn h
      omega

theorem lateTickPrimes_eq_missing (u : ℕ) (hu : 8 ≤ u) :
    lateTickPrimes u =
      (P2 u).filter (fun p => ¬ UsedBefore canonical.a (u+1) (3*p)) := by
  classical
  ext p
  simp only [lateTickPrimes, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hlate⟩
    exact ⟨hp, (P2_tick_missing_iff_late hu hp).mpr hlate⟩
  · rintro ⟨hp, hmissing⟩
    exact ⟨hp, (P2_tick_missing_iff_late hu hp).mp hmissing⟩

theorem tickAbove_card_add_theta2 (u : ℕ) (hu : 8 ≤ u) :
    (Clock.tickAbove canonical u spanTickValue).card + theta2 u =
      (P2 u).card := by
  classical
  rw [tickAbove_card_eq_completed u hu, theta2,
    lateTickPrimes_eq_missing u hu, completedTickPrimes]
  exact Finset.card_filter_add_card_filter_not (fun p => UsedBefore canonical.a (u+1) (3*p))

/-- Two odd-prime introductions cannot occur at adjacent indices, and
at one index the actual value 2p determines the introduced prime. -/
theorem theta2_le_one (u : ℕ) (hu : 8 ≤ u) : theta2 u ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro p hp q hq
  obtain ⟨hpP2, hplate⟩ := Finset.mem_filter.mp hp
  obtain ⟨hqP2, hqlate⟩ := Finset.mem_filter.mp hq
  obtain ⟨hpprime, hp2⟩ := mem_P2_odd hu hpP2
  obtain ⟨hqprime, hq2⟩ := mem_P2_odd hu hqP2
  have hsame : ∀ n m : ℕ, (n = u-1 ∨ n = u) →
      (m = u-1 ∨ m = u) → NewPrimeAt canonical n p →
      NewPrimeAt canonical m q → p = q := by
    intro n m hn hm hnp hmq
    have hnm : n = m := by
      rcases lt_trichotomy n m with hlt | heq | hgt
      · have hsep := prime_introductions_separated canonical hnp hp2 hmq hq2 hlt
        rcases hn with hn | hn <;> rcases hm with hm | hm <;> omega
      · exact heq
      · have hsep := prime_introductions_separated canonical hmq hq2 hnp hp2 hgt
        rcases hn with hn | hn <;> rcases hm with hm | hm <;> omega
    have hpval := firstMultiple_eq_twice canonical hnp hp2
    have hqval := firstMultiple_eq_twice canonical hmq hq2
    rw [hnm] at hpval
    omega
  rcases hplate with hpnew | hpnew <;> rcases hqlate with hqnew | hqnew
  · exact hsame (u-1) (u-1) (Or.inl rfl) (Or.inl rfl) hpnew hqnew
  · exact hsame (u-1) u (Or.inl rfl) (Or.inr rfl) hpnew hqnew
  · exact hsame u (u-1) (Or.inr rfl) (Or.inl rfl) hpnew hqnew
  · exact hsame u u (Or.inr rfl) (Or.inr rfl) hpnew hqnew

end EKG.CanonicalCounting
