import Mathlib

/-!
# Shape Lemma, generic part

`SLCW α p v r` and `Exc α p v` are the bodies of `Harborth.SLCWitness` and
`Harborth.Exceptional`, stated for an arbitrary finite type `α` of classes. This file proves
that both are invariant under relabeling the classes, and gives the two rules of Section 4 of the paper:

* rule H(ρ) (`hcap`): `slcw_hcap` reduces SLC to a spread bound on the layers of `v` and a
  weight bound;
* rule B (`bval`): `slcw_ruleB` reduces SLC to a bound on the first layer.
-/

namespace Harborth.ShapeAux

open Finset

/-- The SLC hypotheses for profile `v` and depths `r` on the classes `α`
(the body of `Harborth.SLCWitness`). -/
def SLCW (α : Type*) [Fintype α] (p : ℕ) (v r : α → ℕ) : Prop :=
  (∀ g, r g ≤ v g) ∧ (∀ g, r g % 2 = v g % 2) ∧
  (∑ g, ((r g : ℤ)) ^ 2 ≤ ∑ g, ((v g : ℤ) - 2) ^ 2) ∧
  p - 1 ≤ ∑ i ∈ Finset.range p, (Finset.univ.filter (fun g => i + 1 ≤ r g)).card ^ 2 / 4

/-- The exceptional shapes (the body of `Harborth.Exceptional`). -/
def Exc (α : Type*) (p : ℕ) (v : α → ℕ) : Prop :=
  ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ v a = p - 1 ∧ v b + v c = p ∧
    1 ≤ v c ∧ v c ≤ 3 ∧ ∀ g, g ≠ a → g ≠ b → g ≠ c → v g = 0

/-- The shape conclusion. -/
def ShapeConcl (α : Type*) [Fintype α] (p : ℕ) (v : α → ℕ) : Prop :=
  (∃ r : α → ℕ, SLCW α p v r) ∨ Exc α p v

section Relabel

variable {α β : Type*} [Fintype α] [Fintype β]

theorem card_filter_comp_equiv (e : β ≃ α) (P : α → Prop) [DecidablePred P] :
    (univ.filter (fun b => P (e b))).card = (univ.filter P).card := by
  rw [Finset.card_filter, Finset.card_filter]
  exact Equiv.sum_comp e (fun a => if P a then 1 else 0)

theorem slcw_comp_equiv (e : β ≃ α) {p : ℕ} {v r : α → ℕ} :
    SLCW β p (v ∘ e) (r ∘ e) → SLCW α p v r := by
  rintro ⟨h1, h2, h3, h4⟩
  refine ⟨fun a => by simpa using h1 (e.symm a), fun a => by simpa using h2 (e.symm a), ?_, ?_⟩
  · have e1 := Equiv.sum_comp e (fun a => ((r a : ℤ)) ^ 2)
    have e2 := Equiv.sum_comp e (fun a => ((v a : ℤ) - 2) ^ 2)
    simp only [Function.comp] at h3
    rw [e1, e2] at h3
    exact h3
  · have hc : ∀ i, (univ.filter (fun x => i + 1 ≤ r (e x))).card =
        (univ.filter (fun g => i + 1 ≤ r g)).card :=
      fun i => card_filter_comp_equiv e (fun a => i + 1 ≤ r a)
    simp only [Function.comp, hc] at h4
    exact h4

omit [Fintype α] [Fintype β] in
theorem exc_comp_equiv (e : β ≃ α) {p : ℕ} {v : α → ℕ} : Exc β p (v ∘ e) → Exc α p v := by
  rintro ⟨a, b, c, hab, hac, hbc, ha, hbc', hc1, hc3, h0⟩
  refine ⟨e a, e b, e c, by simpa using hab, by simpa using hac, by simpa using hbc, ha, hbc',
    hc1, hc3, fun g hga hgb hgc => ?_⟩
  have := h0 (e.symm g) (by rintro rfl; simp at hga) (by rintro rfl; simp at hgb)
    (by rintro rfl; simp at hgc)
  simpa using this

theorem shapeConcl_comp_equiv (e : β ≃ α) {p : ℕ} {v : α → ℕ} :
    ShapeConcl β p (v ∘ e) → ShapeConcl α p v := by
  rintro (⟨r, hr⟩ | h)
  · left
    refine ⟨r ∘ e.symm, slcw_comp_equiv e ?_⟩
    have : (r ∘ e.symm) ∘ e = r := by funext x; simp
    rw [this]
    exact hr
  · exact Or.inr (exc_comp_equiv e h)

end Relabel

section Layers

variable {α : Type*} [Fintype α]

/-- Layer count `N(i) = #{g | i ≤ v g}`. -/
def lay (v : α → ℕ) (i : ℕ) : ℕ := (univ.filter (fun g => i ≤ v g)).card

theorem lay_anti (v : α → ℕ) {i j : ℕ} (h : i ≤ j) : lay v j ≤ lay v i := by
  unfold lay
  exact Finset.card_le_card (fun g => by simp only [mem_filter, mem_univ, true_and]; omega)

theorem lay_le_card (v : α → ℕ) (i : ℕ) : lay v i ≤ Fintype.card α := by
  unfold lay
  exact (Finset.card_le_card (subset_univ _)).trans_eq (card_univ)

theorem lay_eq_sum (v : α → ℕ) (i : ℕ) : lay v i = ∑ g, if i ≤ v g then 1 else 0 := by
  unfold lay
  rw [Finset.card_filter]

/-- `∑ min (v g) k = ∑_{i<k} N(i+1)`. -/
theorem sum_min_eq (v : α → ℕ) (k : ℕ) :
    ∑ g, min (v g) k = ∑ i ∈ range k, lay v (i + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ← ih, lay_eq_sum, ← sum_add_distrib]
    refine sum_congr rfl (fun g _ => ?_)
    split_ifs <;> omega

theorem sum_eq_layers (v : α → ℕ) (K : ℕ) (hK : ∀ g, v g ≤ K) :
    ∑ g, v g = ∑ i ∈ range K, lay v (i + 1) := by
  rw [← sum_min_eq]
  exact sum_congr rfl (fun g _ => by rw [min_eq_left (hK g)])

theorem nat_le_sq_div_four_add_one (a : ℕ) : a ≤ a ^ 2 / 4 + 1 := by
  rcases Nat.lt_or_ge a 2 with h | h
  · omega
  · have : (a - 1) * 4 ≤ a ^ 2 := by
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
      rw [show b + 2 - 1 = b + 1 by omega]
      nlinarith
    have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2 this
    omega

theorem sq_le_four_mul_sq_div_four_add_one (a : ℕ) : a ^ 2 ≤ 4 * (a ^ 2 / 4) + 1 := by
  have h := Nat.div_add_mod (a ^ 2) 4
  have : a ^ 2 % 4 ≤ 1 := by
    rcases Nat.even_or_odd a with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · rw [show (b + b) ^ 2 = 4 * (b * b) by ring]; simp
    · rw [show (2 * b + 1) ^ 2 = 4 * (b * b + b) + 1 by ring]; omega
  omega

end Layers

section Weight

variable {α : Type*} [Fintype α]

theorem sum_sub_two_sq (p : ℕ) (hcard : Fintype.card α = p) (v : α → ℕ)
    (hsum : ∑ g, v g = 2 * p - 1) (hp : 1 ≤ p) :
    ∑ g, ((v g : ℤ) - 2) ^ 2 = ∑ g, ((v g : ℤ)) ^ 2 - 4 * p + 4 := by
  have hs : ∑ g, ((v g : ℤ)) = 2 * p - 1 := by
    rw [← Nat.cast_sum, hsum]; push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * p)]; ring
  have : ∀ g, ((v g : ℤ) - 2) ^ 2 = (v g : ℤ) ^ 2 - 4 * (v g : ℤ) + 4 := fun g => by ring
  simp only [this, sum_add_distrib, sum_sub_distrib, ← mul_sum, hs, sum_const, card_univ,
    hcard, nsmul_eq_mul]
  ring

/-- (W) from a weight bound `∑ (v² - r²) ≥ 4(p-1)`. -/
theorem weight_of (p : ℕ) (hcard : Fintype.card α = p) (v r : α → ℕ)
    (hsum : ∑ g, v g = 2 * p - 1) (hp : 1 ≤ p) (hr : ∀ g, r g ≤ v g)
    (hW : 4 * (p - 1) ≤ ∑ g, (v g ^ 2 - r g ^ 2)) :
    ∑ g, ((r g : ℤ)) ^ 2 ≤ ∑ g, ((v g : ℤ) - 2) ^ 2 := by
  rw [sum_sub_two_sq p hcard v hsum hp]
  have h1 : ((4 * (p - 1) : ℕ) : ℤ) ≤ ((∑ g, (v g ^ 2 - r g ^ 2) : ℕ) : ℤ) := by exact_mod_cast hW
  rw [Nat.cast_sum] at h1
  have h2 : ∀ g, (((v g ^ 2 - r g ^ 2 : ℕ)) : ℤ) = (v g : ℤ) ^ 2 - (r g : ℤ) ^ 2 := fun g => by
    rw [Nat.cast_sub (Nat.pow_le_pow_left (hr g) 2)]; push_cast; ring
  simp only [h2, sum_sub_distrib] at h1
  push_cast [Nat.cast_sub hp] at h1
  linarith

/-- `∑ C(v,2)` in terms of `∑ v²`. -/
theorem sum_sq_eq_choose (v : α → ℕ) :
    ∑ g, ((v g : ℤ)) ^ 2 = 2 * ((∑ g, (v g).choose 2 : ℕ) : ℤ) + ((∑ g, v g : ℕ) : ℤ) := by
  push_cast
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl (fun g _ => ?_)
  have h := Nat.choose_two_right (v g)
  have h2 : 2 * (v g).choose 2 = v g * (v g - 1) := by
    rw [h]; exact Nat.mul_div_cancel' (Nat.even_mul_pred_self (v g)).two_dvd
  rcases Nat.eq_zero_or_pos (v g) with h0 | h0
  · rw [h0]; simp
  · have : ((2 * (v g).choose 2 : ℕ) : ℤ) = (v g : ℤ) * ((v g : ℤ) - 1) := by
      rw [h2]; push_cast [Nat.cast_sub h0]; ring
    push_cast at this
    linear_combination -this

end Weight

section RuleH

variable {α : Type*} [Fintype α]

/-- Rule H(ρ): keep classes up to `ρ + 1`, cut larger ones to `ρ` or `ρ + 1` by parity. -/
def hcap (ρ x : ℕ) : ℕ := if x ≤ ρ + 1 then x else if (x - ρ) % 2 = 0 then ρ else ρ + 1

theorem hcap_le (ρ x : ℕ) : hcap ρ x ≤ x := by unfold hcap; split_ifs <;> omega

theorem hcap_mod (ρ x : ℕ) : hcap ρ x % 2 = x % 2 := by unfold hcap; split_ifs <;> omega

theorem hcap_le_succ (ρ x : ℕ) : hcap ρ x ≤ ρ + 1 ∨ x ≤ ρ + 1 := by unfold hcap; split_ifs <;> omega

theorem le_hcap_iff (ρ x i : ℕ) (hi : i ≤ ρ) : i ≤ hcap ρ x ↔ i ≤ x := by
  unfold hcap; split_ifs <;> omega

theorem lay_hcap (ρ : ℕ) (v : α → ℕ) (i : ℕ) (hi : i ≤ ρ) :
    lay (fun g => hcap ρ (v g)) i = lay v i := by
  unfold lay
  congr 1
  ext g
  simp [le_hcap_iff ρ (v g) i hi]

/-- Weight of one class under rule H(ρ), linear bound. -/
theorem hcap_weight_lin (ρ x : ℕ) : (2 * ρ + 3) * (x - (ρ + 1)) ≤ x ^ 2 - hcap ρ x ^ 2 := by
  rcases le_or_gt x (ρ + 1) with h | h
  · rw [Nat.sub_eq_zero_of_le h]; simp
  · obtain ⟨t, rfl⟩ : ∃ t, x = ρ + 2 + t := ⟨x - (ρ + 2), by omega⟩
    have hh : hcap ρ (ρ + 2 + t) ≤ ρ + 1 := by
      rcases hcap_le_succ ρ (ρ + 2 + t) with h' | h' <;> omega
    have hh2 : hcap ρ (ρ + 2 + t) ^ 2 ≤ (ρ + 1) ^ 2 := Nat.pow_le_pow_left hh 2
    rw [show ρ + 2 + t - (ρ + 1) = t + 1 by omega]
    apply Nat.le_sub_of_add_le
    nlinarith

/-- Weight of one class under rule H(ρ), parity-exact bound. -/
theorem hcap_weight_half (ρ x : ℕ) : 4 * ((x - ρ) / 2) * (ρ + 1) ≤ x ^ 2 - hcap ρ x ^ 2 := by
  rcases le_or_gt x (ρ + 1) with h | h
  · rw [show (x - ρ) / 2 = 0 by omega]; simp
  · unfold hcap
    simp only [show ¬ x ≤ ρ + 1 by omega, ↓reduceIte]
    obtain ⟨d, rfl⟩ : ∃ d, x = ρ + 1 + d := ⟨x - (ρ + 1), by omega⟩
    split_ifs with hpar
    · -- d odd, cut to ρ
      obtain ⟨e, he⟩ : ∃ e, d + 1 = 2 * e := ⟨(d + 1) / 2, by omega⟩
      rw [show (ρ + 1 + d - ρ) / 2 = e by omega]
      apply Nat.le_sub_of_add_le
      have : ρ + 1 + d = ρ + 2 * e := by omega
      rw [this]
      nlinarith
    · -- d even, cut to ρ + 1
      obtain ⟨e, he⟩ : ∃ e, d = 2 * e := ⟨d / 2, by omega⟩
      rw [show (ρ + 1 + d - ρ) / 2 = e by omega, he]
      apply Nat.le_sub_of_add_le
      nlinarith

/-- Rule H(ρ) gives an SLC witness once its spread and weight bounds hold. -/
theorem slcw_hcap (p : ℕ) (hcard : Fintype.card α = p) (v : α → ℕ)
    (hsum : ∑ g, v g = 2 * p - 1) (hp : 1 ≤ p) (ρ : ℕ) (hρ : ρ ≤ p)
    (hS : p - 1 ≤ ∑ i ∈ range ρ, lay v (i + 1) ^ 2 / 4)
    (hW : 4 * (p - 1) ≤ ∑ g, (v g ^ 2 - hcap ρ (v g) ^ 2)) :
    SLCW α p v (fun g => hcap ρ (v g)) := by
  refine ⟨fun g => hcap_le ρ (v g), fun g => hcap_mod ρ (v g),
    weight_of p hcard v _ hsum hp (fun g => hcap_le ρ (v g)) hW, ?_⟩
  refine hS.trans ?_
  calc ∑ i ∈ range ρ, lay v (i + 1) ^ 2 / 4
      = ∑ i ∈ range ρ, lay (fun g => hcap ρ (v g)) (i + 1) ^ 2 / 4 := by
        refine sum_congr rfl (fun i hi => ?_)
        rw [lay_hcap ρ v (i + 1) (by simp at hi; omega)]
    _ ≤ ∑ i ∈ range p, lay (fun g => hcap ρ (v g)) (i + 1) ^ 2 / 4 :=
        sum_le_sum_of_subset (range_subset_range.2 hρ)
    _ = _ := rfl

end RuleH

section RuleB

variable {α : Type*} [Fintype α]

/-- Rule B depth of a class of size `x ≠ 2`. -/
def bval (x : ℕ) : ℕ := if x = 0 then 0 else if x % 2 = 1 then 1 else 2

/-- Budget `(x-2)² - bval(x)²` of a class under rule B (`0` for classes of size 2). -/
def bslack (x : ℕ) : ℤ := if x = 2 then 0 else ((x : ℤ) - 2) ^ 2 - (bval x : ℤ) ^ 2

theorem bval_le (x : ℕ) : bval x ≤ x := by unfold bval; split_ifs <;> omega

theorem bval_mod (x : ℕ) : bval x % 2 = x % 2 := by unfold bval; split_ifs <;> omega

theorem bslack_nonneg (x : ℕ) : 0 ≤ bslack x := by
  unfold bslack bval
  rcases (by omega : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ 4 ≤ x) with h | h | h | h | h
  · subst h; norm_num
  · subst h; norm_num
  · subst h; norm_num
  · subst h; norm_num
  · have hx : (4 : ℤ) ≤ x := by exact_mod_cast h
    simp only [show x ≠ 2 by omega, show x ≠ 0 by omega, ↓reduceIte]
    split_ifs <;> push_cast <;> nlinarith

theorem four_dvd_bslack (x : ℕ) : (4 : ℤ) ∣ bslack x := by
  unfold bslack bval
  rcases Nat.even_or_odd' x with ⟨q, rfl | rfl⟩
  · rcases (by omega : q = 0 ∨ q = 1 ∨ 2 ≤ q) with h | h | h
    · subst h; norm_num
    · subst h; norm_num
    · simp only [show 2 * q ≠ 2 by omega, show 2 * q ≠ 0 by omega, show 2 * q % 2 ≠ 1 by omega,
        ↓reduceIte]
      exact ⟨q * q - 2 * q, by push_cast; ring⟩
  · simp only [show 2 * q + 1 ≠ 2 by omega, show 2 * q + 1 ≠ 0 by omega,
      show (2 * q + 1) % 2 = 1 by omega, ↓reduceIte]
    exact ⟨q * q - q, by push_cast; ring⟩

/-- Per-class key inequality of rule B (Section 4 of the paper, Case 1). -/
theorem bslack_key (x : ℕ) (hx : x ≠ 2) :
    ((x : ℤ) - 2) ^ 2 ≤ 4 * (if 1 ≤ bval x then 1 else 0) + bslack x := by
  unfold bslack
  simp only [hx, ↓reduceIte]
  unfold bval
  split_ifs <;> omega

theorem sum_sub_two_sq_ge (p : ℕ) (hcard : Fintype.card α = p) (v : α → ℕ)
    (hsum : ∑ g, v g = 2 * p - 1) (hp : 2 ≤ p) (hconc : 2 * p - 4 ≤ ∑ g, (v g).choose 2) :
    2 * (p : ℤ) - 5 ≤ ∑ g, ((v g : ℤ) - 2) ^ 2 := by
  rw [sum_sub_two_sq p hcard v hsum (by omega), sum_sq_eq_choose, hsum]
  have : ((2 * p - 4 : ℕ) : ℤ) ≤ ((∑ g, (v g).choose 2 : ℕ) : ℤ) := by exact_mod_cast hconc
  push_cast [Nat.cast_sub (by omega : 4 ≤ 2 * p), Nat.cast_sub (by omega : 1 ≤ 2 * p)] at this ⊢
  linarith

theorem nat_sq_div_four_of (p x : ℕ) (hp : 17 ≤ p) (hodd : p % 2 = 1) (hx : 2 * p ≤ 4 * x + 5) :
    p - 1 ≤ x ^ 2 / 4 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  obtain ⟨q, rfl⟩ : ∃ q, p = 2 * q + 1 := ⟨p / 2, by omega⟩
  have hq : q ≤ x := by omega
  have h8 : 8 ≤ q := by omega
  rw [show 2 * q + 1 - 1 = 2 * q by omega]
  nlinarith

/-- Rule B (Section 4 of the paper, Cases 1 and 2): if the support `N(1)` has `⌊N(1)²/4⌋ ≥ p - 1`, rule B
gives an SLC witness. -/
theorem slcw_ruleB (p : ℕ) (hcard : Fintype.card α = p) (v : α → ℕ)
    (hsum : ∑ g, v g = 2 * p - 1) (hconc : 2 * p - 4 ≤ ∑ g, (v g).choose 2)
    (hp : 17 ≤ p) (hodd : p % 2 = 1) (hm : p - 1 ≤ lay v 1 ^ 2 / 4) :
    ∃ r : α → ℕ, SLCW α p v r := by
  classical
  set D : ℤ := ∑ g, bslack (v g) with hD
  have hD0 : 0 ≤ D := sum_nonneg (fun g _ => bslack_nonneg (v g))
  have hD4 : (4 : ℤ) ∣ D := dvd_sum (fun g _ => four_dvd_bslack (v g))
  set twos := univ.filter (fun g => v g = 2) with htwos
  set k := min twos.card (D / 4).toNat with hk
  obtain ⟨K, hKs, hKc⟩ := Finset.exists_subset_card_eq (show k ≤ twos.card from min_le_left _ _)
  have hK2 : ∀ g ∈ K, v g = 2 := fun g hg => by simpa [htwos] using hKs hg
  have h4k : 4 * (k : ℤ) ≤ D := by
    have h1 : (k : ℤ) ≤ ((D / 4).toNat : ℤ) := by exact_mod_cast min_le_right _ _
    rw [Int.toNat_of_nonneg (Int.ediv_nonneg hD0 (by norm_num))] at h1
    have := Int.mul_ediv_cancel' hD4
    linarith
  set r : α → ℕ := fun g => if v g = 2 then (if g ∈ K then 2 else 0) else bval (v g) with hr
  have hrle : ∀ g, r g ≤ v g := fun g => by
    simp only [hr]; split_ifs with h1 h2 <;> first | omega | exact bval_le _
  refine ⟨r, hrle, fun g => ?_, ?_, ?_⟩
  · simp only [hr]; split_ifs with h1 h2 <;> first | omega | exact bval_mod _
  · -- weight: `∑ ((v-2)² - r²) = D - 4k ≥ 0`
    have hcl : ∀ g, ((v g : ℤ) - 2) ^ 2 - (r g : ℤ) ^ 2 =
        bslack (v g) - 4 * (if g ∈ K then 1 else 0) := fun g => by
      simp only [hr]
      by_cases h1 : v g = 2
      · simp only [h1, ↓reduceIte, bslack]
        split_ifs <;> norm_num
      · have : g ∉ K := fun hg => h1 (hK2 g hg)
        simp only [h1, this, ↓reduceIte, bslack]
        ring
    have hsumcl : ∑ g, (((v g : ℤ) - 2) ^ 2 - (r g : ℤ) ^ 2) = D - 4 * k := by
      rw [sum_congr rfl (fun g _ => hcl g), sum_sub_distrib, ← mul_sum, ← hD]
      congr 2
      rw [sum_boole]
      simp [hKc]
    rw [sum_sub_distrib] at hsumcl
    linarith
  · -- spread: the first layer alone suffices
    have hx1 : p - 1 ≤ (univ.filter (fun g => 0 + 1 ≤ r g)).card ^ 2 / 4 := by
      by_cases hkk : k = twos.card
      · have hKt : K = twos := Finset.eq_of_subset_of_card_le hKs (by omega)
        have : univ.filter (fun g => 0 + 1 ≤ r g) = univ.filter (fun g => 1 ≤ v g) := by
          ext g
          simp only [mem_filter, mem_univ, true_and, hr]
          by_cases h1 : v g = 2
          · have : g ∈ K := by rw [hKt]; simp [htwos, h1]
            simp [h1, this]
          · simp only [h1, ↓reduceIte, bval]
            split_ifs <;> omega
        rw [this]; exact hm
      · have hkD : 4 * (k : ℤ) = D := by
          have hk' : k = (D / 4).toNat := by omega
          rw [hk', Int.toNat_of_nonneg (Int.ediv_nonneg hD0 (by norm_num))]
          exact Int.mul_ediv_cancel' hD4
        have hkey : ∀ g, ((v g : ℤ) - 2) ^ 2 ≤
            4 * (if 0 + 1 ≤ r g then 1 else 0) + bslack (v g) - 4 * (if g ∈ K then 1 else 0) :=
          fun g => by
            by_cases h1 : v g = 2
            · simp only [hr, h1, ↓reduceIte, bslack]
              split_ifs <;> simp_all
            · have hg : g ∉ K := fun hg => h1 (hK2 g hg)
              have := bslack_key (v g) h1
              simp only [hr, h1, hg, ↓reduceIte, zero_add]
              linarith
        have hsk := sum_le_sum (fun g (_ : g ∈ univ) => hkey g)
        rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← hD, sum_boole, sum_boole]
          at hsk
        have hK' : ((univ.filter (fun g => g ∈ K)).card : ℤ) = k := by
          rw [← hKc]; congr 2; ext g; simp
        rw [hK'] at hsk
        have h25 := sum_sub_two_sq_ge p hcard v hsum (by omega) hconc
        apply nat_sq_div_four_of p _ hp hodd
        have : (2 * p : ℤ) ≤ 4 * ((univ.filter (fun g => 0 + 1 ≤ r g)).card : ℤ) + 5 := by
          push_cast at hsk ⊢; linarith
        exact_mod_cast this
    refine hx1.trans ?_
    exact single_le_sum (f := fun i => (univ.filter (fun g => i + 1 ≤ r g)).card ^ 2 / 4)
      (fun i _ => Nat.zero_le _) (mem_range.2 (by omega))

end RuleB

end Harborth.ShapeAux
