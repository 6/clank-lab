import Uniform5.CaseBInputs

/-! Exact angle-budget consequences used in the paired case analysis. -/

noncomputable section

namespace Uniform5.CaseB

noncomputable def angleBudget (c : List ℕ) : ℝ := (c.map (fun (q : ℕ) => 1 - 2 / (q : ℝ))).sum

theorem polygon_angle_lower {q : ℕ} (hq : 3 ≤ q) :
    (1 / 3 : ℝ) ≤ 1 - 2 / (q : ℝ) := by
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hdiv : (2 : ℝ) / q ≤ 2 / 3 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hq'
  linarith

theorem polygon_angle_four_lower {q : ℕ} (hq : 4 ≤ q) :
    (1 / 2 : ℝ) ≤ 1 - 2 / (q : ℝ) := by
  have hq' : (4 : ℝ) ≤ q := by exact_mod_cast hq
  have hdiv : (2 : ℝ) / q ≤ 2 / 4 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hq'
  linarith

theorem angleBudget_lower {c : List ℕ} (hc : ∀ q ∈ c, 3 ≤ q) :
    c.length / 3 ≤ angleBudget c := by
  induction c with
  | nil => simp [angleBudget]
  | cons q c ih =>
    have hq := polygon_angle_lower (hc q (by simp))
    have hi := ih (fun t ht => hc t (by simp [ht]))
    simp only [angleBudget, List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
      Nat.cast_one] at *
    linarith

theorem angleBudget_lower_of_four {c : List ℕ} (hc : ∀ q ∈ c, 3 ≤ q)
    (hfour : ∃ q ∈ c, 4 ≤ q) :
    (c.length - 1) / 3 + 1 / 2 ≤ angleBudget c := by
  induction c with
  | nil => simp at hfour
  | cons q c ih =>
    have hc' : ∀ t ∈ c, 3 ≤ t := fun t ht => hc t (by simp [ht])
    obtain ⟨t, ht, ht4⟩ := hfour
    rcases List.mem_cons.mp ht with rfl | ht
    · have hi := angleBudget_lower hc'
      have hq := polygon_angle_four_lower ht4
      simp only [angleBudget, List.map_cons, List.sum_cons, List.length_cons,
        Nat.cast_add, Nat.cast_one] at *
      linarith
    · have hi := ih hc' ⟨t, ht, ht4⟩
      have hq := polygon_angle_lower (hc q (by simp))
      simp only [angleBudget, List.map_cons, List.sum_cons, List.length_cons,
        Nat.cast_add, Nat.cast_one] at *
      linarith

/-- A paired type-(i) fan has three rays, or four with the other three
polygon sizes all equal to three. This is the exact integer argument in
the opening paragraph of the paired theorem. -/
theorem paired_angle_cases {m : ℝ} {c : List ℕ} (hm : 17 ≤ m)
    (hc : ∀ q ∈ c, 3 ≤ q) (hlen : 2 ≤ c.length)
    (hangle : (1 - 2 / m) + angleBudget c < 2) :
    c.length = 2 ∨ c = [3, 3, 3] := by
  have hm0 : 0 < m := by linarith
  have hmdiv : 2 / m ≤ (2 / 17 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm
  have hlo := angleBudget_lower hc
  have hlen3 : c.length ≤ 3 := by
    by_contra h
    have hc4 : (4 : ℝ) ≤ c.length := by exact_mod_cast (show 4 ≤ c.length by omega)
    linarith
  rcases Nat.eq_or_lt_of_le hlen with heq | hgt
  · exact Or.inl heq.symm
  have hlenEq : c.length = 3 := by omega
  have hall : ∀ q ∈ c, q = 3 := by
    intro q hq
    by_contra hn
    have hq4 : 4 ≤ q := by have := hc q hq; omega
    have hstrong := angleBudget_lower_of_four hc ⟨q, hq, hq4⟩
    rw [hlenEq] at hstrong
    norm_num at hstrong
    linarith
  right
  rcases c with _ | ⟨a, c⟩ <;> simp only [List.length_nil, List.length_cons] at hlenEq
  · contradiction
  rcases c with _ | ⟨b, c⟩ <;> simp only [List.length_nil, List.length_cons] at hlenEq
  · contradiction
  rcases c with _ | ⟨d, c⟩ <;> simp only [List.length_nil, List.length_cons] at hlenEq
  · contradiction
  have hnil : c = [] := List.length_eq_zero_iff.mp (by omega)
  subst c
  have ha := hall a (by simp)
  have hb := hall b (by simp)
  have hd := hall d (by simp)
  simp [ha, hb, hd]

/-- Two large entries already exceed the permitted budget, even with a
single third polygon. Thus the partner in a type-(i) fan is unique. -/
theorem two_large_angles_impossible {n m : ℝ} {q : ℕ}
    (hn : 17 ≤ n) (hm : 17 ≤ m) (hq : 3 ≤ q) :
    ¬ ((1 - 2 / n) + (1 - 2 / m) + (1 - 2 / (q : ℝ)) < 2) := by
  have hn' : 2 / n ≤ (2 / 17 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn
  have hm' : 2 / m ≤ (2 / 17 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm
  have hq' := polygon_angle_lower hq
  linarith

/-- The two-entry tail of a paired three-ray cycle has first entry 3 or 4,
and exactly the upper ranges used by the paper's finite partner filter. -/
theorem paired_three_angle_candidates {m a b : ℕ}
    (hm : 17 ≤ m) (ha : 3 ≤ a) (hab : a ≤ b)
    (hangle : (1 - 2 / (m : ℝ)) + (1 - 2 / (a : ℝ)) +
      (1 - 2 / (b : ℝ)) < 2) :
    (a = 3 ∧ b ≤ 9) ∨ (a = 4 ∧ b ≤ 5) := by
  have hm' : (17 : ℝ) ≤ m := by exact_mod_cast hm
  have hmdiv : 2 / (m : ℝ) ≤ 2 / 17 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm'
  have ha4 : a ≤ 4 := by
    by_contra h
    have ha5 : (5 : ℝ) ≤ a := by exact_mod_cast (show 5 ≤ a by omega)
    have hb5 : (5 : ℝ) ≤ b := by exact_mod_cast (show 5 ≤ b by omega)
    have hadiv : 2 / (a : ℝ) ≤ 2 / 5 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) ha5
    have hbdiv : 2 / (b : ℝ) ≤ 2 / 5 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hb5
    linarith
  have hae : a = 3 ∨ a = 4 := by omega
  rcases hae with rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    by_contra h
    have hb10 : (10 : ℝ) ≤ b := by exact_mod_cast (show 10 ≤ b by omega)
    have hbdiv : 2 / (b : ℝ) ≤ 2 / 10 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hb10
    norm_num at hangle
    linarith
  · right
    refine ⟨rfl, ?_⟩
    by_contra h
    have hb6 : (6 : ℝ) ≤ b := by exact_mod_cast (show 6 ≤ b by omega)
    have hbdiv : 2 / (b : ℝ) ≤ 2 / 6 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hb6
    norm_num at hangle
    linarith

/-- With the proved acute criterion, these are exactly the canonical tails
passed to the partner-radius comparison. The integer cutoffs are derived
from the strict angle sum, including 41/23/17/19. -/
theorem paired_three_partner_tail {m a b : ℕ}
    (hm : 17 ≤ m) (ha : 3 ≤ a) (hab : a ≤ b)
    (hangle : (1 - 2 / (m : ℝ)) + (1 - 2 / (a : ℝ)) +
      (1 - 2 / (b : ℝ)) < 2)
    (hacute : chord m ^ 2 < chord a ^ 2 + chord b ^ 2) :
    PartnerTail m [a, b] := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmreal : (17 : ℝ) ≤ m := by exact_mod_cast hm
  have hcases := paired_three_angle_candidates hm ha hab hangle
  rcases hcases with ⟨rfl, hb9⟩ | ⟨rfl, hb5⟩
  · have hb6 : 6 ≤ b := by
      by_contra h
      have hb5 : (b : ℝ) ≤ 5 := by exact_mod_cast (show b ≤ 5 by omega)
      have h := paired_small_triangle_obtuse hmreal (by exact_mod_cast hab) hb5
      norm_num only [Nat.cast_ofNat] at hacute
      linarith
    interval_cases b
    · exact Or.inl (by simp)
    · right
      refine ⟨hm, Or.inl ⟨rfl, ?_⟩⟩
      have hdiv : (1 / 21 : ℝ) < 2 / m := by norm_num at hangle; linarith
      have hlt : (m : ℝ) < 42 := by
        have := (lt_div_iff₀ hm0).mp hdiv
        linarith
      have : m < 42 := by exact_mod_cast hlt
      omega
    · right
      refine ⟨hm, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩
      have hdiv : (1 / 12 : ℝ) < 2 / m := by norm_num at hangle; linarith
      have hlt : (m : ℝ) < 24 := by
        have := (lt_div_iff₀ hm0).mp hdiv
        linarith
      have : m < 24 := by exact_mod_cast hlt
      omega
    · right
      refine ⟨hm, Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))⟩
      have hdiv : (1 / 9 : ℝ) < 2 / m := by norm_num at hangle; linarith
      have hlt : (m : ℝ) < 18 := by
        have := (lt_div_iff₀ hm0).mp hdiv
        linarith
      have : m < 18 := by exact_mod_cast hlt
      omega
  · interval_cases b
    · exact Or.inl (by simp)
    · right
      refine ⟨hm, Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))⟩
      have hdiv : (1 / 10 : ℝ) < 2 / m := by norm_num at hangle; linarith
      have hlt : (m : ℝ) < 20 := by
        have := (lt_div_iff₀ hm0).mp hdiv
        linarith
      have : m < 20 := by exact_mod_cast hlt
      omega

end Uniform5.CaseB
