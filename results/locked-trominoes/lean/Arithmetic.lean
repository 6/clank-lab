import Geometry

namespace LockedTromino

/-- Every allowed height is a sum of 6s and 9s, including the smallest cases. -/
theorem height_six_nine (m : Nat) (hm : 6 ≤ m) (hd : 3 ∣ m) :
    ∃ a b : Nat, m = 6 * a + 9 * b := by
  have hmod : m % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
  by_cases he : (m / 3) % 2 = 0
  · refine ⟨(m / 3) / 2, 0, ?_⟩
    omega
  · refine ⟨((m / 3) - 3) / 2, 1, ?_⟩
    omega

/-- Frobenius threshold for the proposed 8/9-width palette. -/
theorem width_eight_nine (n : Nat) (hn : 56 ≤ n) :
    ∃ a b : Nat, n = 8 * a + 9 * b := by
  refine ⟨n / 8 - n % 8, n % 8, ?_⟩
  omega

/-- Proposed exceptional width-5 palette: the only omitted allowed heights
are precisely 6 and 15. This does not assert that any blocks exist. -/
theorem height_nine_twelve (m : Nat) (hm : 6 ≤ m) (hd : 3 ∣ m)
    (h6 : m ≠ 6) (h15 : m ≠ 15) :
    ∃ a b : Nat, m = 9 * a + 12 * b := by
  have hmod : m % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
  refine ⟨m / 3 / 3 - (m / 3) % 3, (m / 3) % 3, ?_⟩
  omega

/-- A concrete list of strips: `a` copies of `u` followed by copies of `v`. -/
def TwoSizes (a u v : Nat) (i : Nat) : Nat := if i < a then u else v

theorem twoSizes_positive {a u v : Nat} (hu : 0 < u) (hv : 0 < v) :
    ∀ i, 0 < TwoSizes a u v i := by
  intro i
  unfold TwoSizes
  split <;> assumption

theorem prefix_first (a u v n : Nat) (hn : n ≤ a) :
    Prefix (TwoSizes a u v) n = (n : Int) * u := by
  induction n with
  | zero => simp [Prefix]
  | succ n ih =>
    rw [Prefix, ih (by omega)]
    simp only [TwoSizes, ite_eq_left (show n < a by omega)]
    simp [Int.add_mul]

theorem prefix_twoSizes (a b u v : Nat) :
    Prefix (TwoSizes a u v) (a + b) = (a : Int) * u + (b : Int) * v := by
  induction b with
  | zero => simpa using prefix_first a u v a (Nat.le_refl a)
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 by omega, Prefix, ih]
    simp only [TwoSizes, ite_eq_right (show ¬ a + b < a by omega)]
    simp [Int.add_mul, Int.add_assoc]

end LockedTromino
