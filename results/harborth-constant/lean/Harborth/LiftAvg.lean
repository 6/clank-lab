import Harborth.LiftCore

/-! Directions and the averaging over them. -/

open Finset

namespace Harborth

variable {p : ℕ} [Fact p.Prime]

/-- The `p + 1` directions through `0`. -/
def dirOf : Option (ZMod p) → Dir p
  | none => ⟨Prod.fst, Prod.snd, (1, 0), (0, 1), fun x => Prod.ext (by simp) (by simp)⟩
  | some m => ⟨fun x => x.2 - m * x.1, Prod.fst, (0, 1), (1, m),
      fun x => Prod.ext (by simp) (by simp; ring)⟩

@[simp] lemma dirOf_none_φ (x : ZMod p × ZMod p) : (dirOf none).φ x = x.1 := rfl

@[simp] lemma dirOf_some_φ (m : ZMod p) (x : ZMod p × ZMod p) :
    (dirOf (some m)).φ x = x.2 - m * x.1 := rfl

lemma dir_pair (x y : ZMod p × ZMod p) (hxy : x ≠ y) :
    (univ.filter (fun i : Option (ZMod p) => (dirOf i).φ x = (dirOf i).φ y)).card = 1 := by
  obtain ⟨a, b⟩ := x
  obtain ⟨a', b'⟩ := y
  rw [card_eq_one]
  by_cases h : a = a'
  · subst h
    have hb : b ≠ b' := fun hb => hxy (by rw [hb])
    refine ⟨none, ?_⟩
    ext i
    rw [mem_filter, mem_singleton]
    cases i with
    | none => simp
    | some m =>
      simp only [mem_univ, true_and, reduceCtorEq, iff_false, dirOf_some_φ]
      intro h2
      exact hb (by linear_combination h2)
  · refine ⟨some ((b - b') / (a - a')), ?_⟩
    ext i
    rw [mem_filter, mem_singleton]
    cases i with
    | none => simp [h]
    | some m =>
      simp only [mem_univ, true_and, Option.some.injEq, dirOf_some_φ]
      rw [eq_div_iff (sub_ne_zero.2 h)]
      constructor
      · intro h2; linear_combination -h2
      · intro h2; linear_combination -h2

lemma two_choose (v : ℕ) : 2 * v.choose 2 = v * (v - 1) := by
  rw [Nat.choose_two_right]
  exact Nat.mul_div_cancel' (Nat.even_mul_pred_self v).two_dvd

lemma dir_count (D : Dir p) (S : Finset (ZMod p × ZMod p)) :
    ∑ g, (D.fib S g).card * ((D.fib S g).card - 1) =
      (S.offDiag.filter (fun z => D.φ z.1 = D.φ z.2)).card := by
  have hE : S.offDiag.filter (fun z => D.φ z.1 = D.φ z.2) =
      (univ : Finset (ZMod p)).biUnion (fun g => (D.fib S g).offDiag) := by
    ext z
    simp only [mem_filter, mem_offDiag, mem_biUnion, mem_univ, true_and, Dir.fib]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨D.φ z.1, ⟨h1, rfl⟩, ⟨h2, h4.symm⟩, h3⟩
    · rintro ⟨g, ⟨h1, h1'⟩, ⟨h2, h2'⟩, h3⟩
      exact ⟨⟨h1, h2, h3⟩, h1'.trans h2'.symm⟩
  rw [hE, card_biUnion]
  · refine sum_congr rfl fun g _ => ?_
    rw [offDiag_card]
    cases (D.fib S g).card <;> simp [Nat.mul_succ]
  · intro g _ g' _ hgg'
    rw [Function.onFun, disjoint_left]
    intro z hz hz'
    simp only [mem_offDiag, Dir.fib, mem_filter] at hz hz'
    exact hgg' (hz.1.2.symm.trans hz'.1.2)

lemma exists_dense_dir (hp : 11 ≤ p) (S : Finset (ZMod p × ZMod p)) (hS : S.card = 2 * p - 1) :
    ∃ i : Option (ZMod p),
      2 * p - 4 ≤ ∑ g, ((dirOf i).fib S g).card.choose 2 := by
  classical
  have h1 : ∀ i : Option (ZMod p),
      2 * ∑ g, ((dirOf i).fib S g).card.choose 2 =
        (S.offDiag.filter (fun z => (dirOf i).φ z.1 = (dirOf i).φ z.2)).card := by
    intro i
    rw [← dir_count, mul_sum]
    exact sum_congr rfl fun g _ => two_choose _
  have h2 : ∑ i : Option (ZMod p),
      (S.offDiag.filter (fun z => (dirOf i).φ z.1 = (dirOf i).φ z.2)).card =
        S.offDiag.card := by
    simp only [card_filter]
    rw [sum_comm]
    rw [card_eq_sum_ones]
    refine sum_congr rfl fun z hz => ?_
    have := dir_pair z.1 z.2 (mem_offDiag.1 hz).2.2
    rw [card_filter] at this
    exact this
  rw [offDiag_card] at h2
  by_contra hcon
  push Not at hcon
  have h3 : ∑ i : Option (ZMod p),
      (S.offDiag.filter (fun z => (dirOf i).φ z.1 = (dirOf i).φ z.2)).card ≤
      Fintype.card (Option (ZMod p)) • (2 * (2 * p - 5)) := by
    apply Finset.sum_le_card_nsmul
    intro i _
    rw [← h1]
    have := hcon i
    omega
  rw [h2, Fintype.card_option, ZMod.card, hS, smul_eq_mul] at h3
  have h4 : 2 * p - 1 = 2 * p - 2 + 1 := by omega
  obtain ⟨q, hq⟩ : ∃ q, p = q + 11 := ⟨p - 11, by omega⟩
  rw [hq] at h3
  have e1 : 2 * (q + 11) - 1 = 2 * q + 21 := by omega
  have e2 : 2 * (q + 11) - 5 = 2 * q + 17 := by omega
  rw [e1, e2] at h3
  have e3 : (2 * q + 21) * (2 * q + 21) - (2 * q + 21) = (2 * q + 21) * (2 * q + 20) := by
    exact Nat.sub_eq_of_eq_add (by ring)
  nlinarith

end Harborth
