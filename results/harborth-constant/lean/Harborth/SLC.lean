import Harborth.DSH
import Harborth.Shape
import Harborth.SLCAux

/-! Symmetric Layer Criterion and the exceptional shapes. -/

open Finset

namespace Harborth

/-- The conclusion of the Concentrated Profile Lemma for a profile `v`. -/
def CPLConclusion (p : ℕ) [NeZero p] (v : ZMod p → ℕ) : Prop :=
  ∃ t : ZMod p → ℕ, (∀ g, t g ≤ v g) ∧ ∑ g, t g = p ∧
    ∑ g, (t g : ZMod p) * g = 0 ∧ p - 1 ≤ ∑ g, t g * (v g - t g)

/-- SLC Lemma (Section 3 of the paper). -/
theorem slc {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (v r : ZMod p → ℕ)
    (hsum : ∑ g, v g = 2 * p - 1) (hw : SLCWitness p v r) : CPLConclusion p v := by
  obtain ⟨hrv, hpar, hW, hS⟩ := hw
  have hpp : p.Prime := Fact.out
  obtain ⟨N, hN⟩ : ∃ N, N = 2 * p := ⟨_, rfl⟩
  have hvle : ∀ g, v g ≤ 2 * p - 1 := fun g => by
    have := Finset.single_le_sum (f := v) (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)
    omega
  have hrN : ∀ g, r g ≤ N := fun g => by have := hrv g; have := hvle g; omega
  let L : ℕ → Finset (ZMod p) := fun i => univ.filter (fun g => i + 1 ≤ r g)
  let x : ℕ → ℕ := fun i => (L i).card
  let a : ZMod p → ℕ := fun g => (v g - r g) / 2
  have ha : ∀ g, 2 * a g + r g = v g := fun g => by
    have := hrv g; have := hpar g; simp only [a]; omega
  have hR : ∑ i ∈ range N, x i = ∑ g, r g := by
    simp only [x, L, card_filter]
    rw [sum_comm]
    refine sum_congr rfl fun g _ => ?_
    rw [← card_filter]
    have : (range N).filter (fun i => i + 1 ≤ r g) = range (r g) := by
      ext i; simp only [mem_filter, mem_range]; have := hrN g; omega
    rw [this]; simp
  have hsa : 2 * ∑ g, a g + ∑ g, r g = 2 * p - 1 := by
    rw [mul_sum, ← sum_add_distrib, ← hsum]
    exact sum_congr rfl fun g _ => ha g
  set T := (∑ g, r g + 1) / 2 with hT
  have hp3 : 3 ≤ p := hp
  have hlo : ∑ i ∈ range N, x i / 2 ≤ T := by
    have : 2 * ∑ i ∈ range N, x i / 2 ≤ ∑ i ∈ range N, x i := by
      rw [mul_sum]; exact sum_le_sum fun i _ => by omega
    omega
  have hhi : T ≤ ∑ i ∈ range N, (x i + 1) / 2 := by
    have : ∑ i ∈ range N, x i ≤ 2 * ∑ i ∈ range N, (x i + 1) / 2 := by
      rw [mul_sum]; exact sum_le_sum fun i _ => by omega
    omega
  obtain ⟨h, hh, hhs⟩ := exists_interval_sum (fun i => x i / 2) (fun i => (x i + 1) / 2)
    (fun i => by omega) N T hlo hhi
  have hhx : ∀ i, h i ≤ (L i).card := fun i => by
    have := (hh i).2; simp only [x] at *; omega
  obtain ⟨Z, hZ, hZB⟩ := layers_cover L h hhx N
  have hwsum : ∑ i ∈ range N, h i * ((L i).card - h i) = ∑ i ∈ range N, x i ^ 2 / 4 :=
    sum_congr rfl fun i _ => half_mul (x i) (h i) (hh i).1 (hh i).2
  have hS' : p - 1 ≤ ∑ i ∈ range N, x i ^ 2 / 4 :=
    le_trans hS (sum_le_sum_of_subset (range_mono (by omega)))
  rw [hwsum] at hZ
  have hZuniv : Z = univ := by
    apply Finset.eq_univ_of_card
    rw [ZMod.card]
    have : p ≤ Z.card := le_trans (by omega) hZ
    have := Finset.card_le_univ Z
    rw [ZMod.card] at this
    omega
  obtain ⟨B, hB, hBs⟩ := hZB (-(∑ g, (a g : ZMod p) * g)) (by rw [hZuniv]; exact mem_univ _)
  let k : ZMod p → ℕ := fun g => ∑ i ∈ range N, if g ∈ B i then 1 else 0
  have hk : ∀ g, k g ≤ r g := fun g => by
    simp only [k]
    rw [← card_filter]
    calc ((range N).filter (fun i => g ∈ B i)).card ≤ (range (r g)).card := by
          apply card_le_card
          intro i hi
          rw [mem_filter, mem_range] at hi
          have := (hB i hi.1).1 hi.2
          simp only [L, mem_filter] at this
          rw [mem_range]; omega
      _ = r g := by simp
  refine ⟨fun g => a g + k g, ?_, ?_, ?_, ?_⟩
  · intro g; show a g + k g ≤ v g; have := ha g; have := hk g; omega
  · have hkk : ∑ g, k g = ∑ i ∈ range N, h i := by
      simp only [k]
      rw [sum_comm]
      refine sum_congr rfl fun i hi => ?_
      rw [← (hB i (mem_range.1 hi)).2]
      simp
    rw [sum_add_distrib, hkk, hhs]
    omega
  · have : ∀ g, (((a g + k g : ℕ)) : ZMod p) * g
        = (a g : ZMod p) * g + ∑ i ∈ range N, if g ∈ B i then g else 0 := fun g => by
      simp only [k]
      push_cast
      rw [add_mul, sum_mul]
      congr 1
      exact sum_congr rfl fun i _ => by split_ifs <;> simp
    rw [sum_congr rfl (fun g _ => this g), sum_add_distrib, sum_comm]
    have h2 : ∑ i ∈ range N, ∑ g, (if g ∈ B i then g else 0) = ∑ i ∈ range N, ∑ g ∈ B i, g :=
      sum_congr rfl fun i _ => by rw [Finset.sum_ite_mem]; simp
    rw [h2, hBs]; ring
  · -- weight
    have hcard : (Fintype.card (ZMod p) : ℤ) = p := by rw [ZMod.card]
    have hvZ : ∑ g, (v g : ℤ) = 2 * p - 1 := by
      have := congrArg (Nat.cast : ℕ → ℤ) hsum
      push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * p)] at this
      exact this
    have hpt : ∀ g, ((v g : ℤ) ^ 2 - (r g : ℤ) ^ 2) ≤
        4 * ((((a g + k g) * (v g - (a g + k g)) : ℕ)) : ℤ) := fun g => by
      have h1 := ha g
      have h2 := hk g
      have h3 : a g + k g ≤ v g := by omega
      rw [Nat.cast_mul, Nat.cast_sub h3]
      have e : (v g : ℤ) = 2 * a g + r g := by exact_mod_cast h1.symm
      push_cast
      rw [e]
      have : (k g : ℤ) ≤ r g := by exact_mod_cast h2
      nlinarith [mul_nonneg (Int.natCast_nonneg (k g)) (sub_nonneg.2 this)]
    have hsq : ∑ g, ((v g : ℤ) ^ 2 - ((v g : ℤ) - 2) ^ 2) = 4 * (2 * (p : ℤ) - 1) - 4 * p := by
      have : ∀ g, ((v g : ℤ) ^ 2 - ((v g : ℤ) - 2) ^ 2) = 4 * (v g : ℤ) - 4 := fun g => by ring
      rw [sum_congr rfl (fun g _ => this g), sum_sub_distrib, ← mul_sum, hvZ]
      simp [hcard]; ring
    have hsum2 : ∑ g, ((v g : ℤ) ^ 2 - (r g : ℤ) ^ 2) ≥ 4 * ((p : ℤ) - 1) := by
      rw [sum_sub_distrib]
      rw [sum_sub_distrib] at hsq
      linarith
    have hfin : 4 * ((p : ℤ) - 1) ≤ 4 * ((∑ g, (a g + k g) * (v g - (a g + k g)) : ℕ) : ℤ) := by
      have e : (4 : ℤ) * ((∑ g, (a g + k g) * (v g - (a g + k g)) : ℕ) : ℤ)
          = ∑ g, 4 * ((((a g + k g) * (v g - (a g + k g)) : ℕ)) : ℤ) := by
        rw [Nat.cast_sum, mul_sum]
      rw [e]
      exact le_trans hsum2 (sum_le_sum fun g _ => hpt g)
    have h4 : (p : ℤ) - 1 ≤ ((∑ g, (a g + k g) * (v g - (a g + k g)) : ℕ) : ℤ) := by linarith
    exact (by omega : p - 1 ≤ ∑ g, (a g + k g) * (v g - (a g + k g)))


lemma sum_three {p : ℕ} [NeZero p] {M : Type*} [AddCommMonoid M] (a b c : ZMod p)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : ZMod p → M)
    (hf : ∀ g, g ≠ a → g ≠ b → g ≠ c → f g = 0) : ∑ g, f g = f a + f b + f c := by
  have h1 : ∑ g ∈ ({a, b, c} : Finset (ZMod p)), f g = ∑ g, f g :=
    Finset.sum_subset (subset_univ _) (fun g _ hg => by
      simp only [mem_insert, mem_singleton, not_or] at hg
      exact hf g hg.1 hg.2.1 hg.2.2)
  rw [← h1, sum_insert (by simp [hab, hac]), sum_insert (by simp [hbc]), sum_singleton, add_assoc]

lemma exc_mk {p : ℕ} [Fact p.Prime] (v : ZMod p → ℕ) (a b c : ZMod p)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hother : ∀ g, g ≠ a → g ≠ b → g ≠ c → v g = 0)
    (x y w : ℕ) (hx : x ≤ v a) (hy : y ≤ v b) (hw : w ≤ v c) (hs : x + y + w = p)
    (hcong : (y : ZMod p) * (b - a) + w * (c - a) = 0)
    (hW : p - 1 ≤ x * (v a - x) + y * (v b - y) + w * (v c - w)) : CPLConclusion p v := by
  classical
  let t : ZMod p → ℕ := fun g => if g = a then x else if g = b then y else if g = c then w else 0
  have ta : t a = x := by simp [t]
  have tb : t b = y := by simp [t, hab.symm]
  have tc : t c = w := by simp [t, hac.symm, hbc.symm]
  have t0 : ∀ g, g ≠ a → g ≠ b → g ≠ c → t g = 0 := fun g h1 h2 h3 => by simp [t, h1, h2, h3]
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · intro g
    by_cases h1 : g = a
    · subst h1; rw [ta]; exact hx
    by_cases h2 : g = b
    · subst h2; rw [tb]; exact hy
    by_cases h3 : g = c
    · subst h3; rw [tc]; exact hw
    rw [t0 g h1 h2 h3]; exact Nat.zero_le _
  · rw [sum_three a b c hab hac hbc t t0, ta, tb, tc]; exact hs
  · rw [sum_three a b c hab hac hbc (fun g => (t g : ZMod p) * g)
      (fun g h1 h2 h3 => by simp [t0 g h1 h2 h3]), ta, tb, tc]
    have h0 : (x : ZMod p) + y + w = 0 := by
      have := congrArg (Nat.cast : ℕ → ZMod p) hs
      push_cast at this
      rw [this]; exact ZMod.natCast_self p
    linear_combination hcong + a * h0
  · rw [sum_three a b c hab hac hbc (fun g => t g * (v g - t g))
      (fun g h1 h2 h3 => by simp [t0 g h1 h2 h3]), ta, tb, tc]
    exact hW

/-- The exceptional shapes (Section 5 of the paper). -/
theorem exceptional_cpl {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (v : ZMod p → ℕ)
    (hsum : ∑ g, v g = 2 * p - 1) (he : Exceptional p v) : CPLConclusion p v := by
  obtain ⟨a, b, c, hab, hac, hbc, hva, hvbc, h1, h3, hother⟩ := he
  have hpp : p.Prime := Fact.out
  set z : ZMod p := (c - a) / (b - a) with hzdef
  have hba : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  have hz : z * (b - a) = c - a := div_mul_cancel₀ _ hba
  have hz0 : z ≠ 0 := fun h => hac (by rw [h, zero_mul] at hz; exact (sub_eq_zero.1 hz.symm).symm)
  have hz1 : z ≠ 1 := fun h => hbc (by rw [h, one_mul] at hz; exact (sub_left_inj.1 hz))
  set β : ℕ := (-z).val with hβdef
  have hβ : (β : ZMod p) = -z := ZMod.natCast_zmod_val _
  have hβlt : β < p := ZMod.val_lt _
  have hβ0 : β ≠ 0 := fun h => hz0 (by rw [h] at hβ; simpa using hβ.symm)
  have hβ1 : β ≠ p - 1 := fun h => hz1 (by
    rw [h, Nat.cast_sub (by omega), ZMod.natCast_self] at hβ
    simp at hβ
    first | exact hβ | exact hβ.symm)
  have hvb : v b = p - v c := by omega
  have hcong : (β : ZMod p) * (b - a) + (1 : ℕ) * (c - a) = 0 := by
    push_cast
    linear_combination (b - a) * hβ - hz
  have hb2 : β ≤ p - 2 := by omega
  obtain ⟨d, hd⟩ : ∃ d, d + β = p - 1 := ⟨p - 1 - β, by omega⟩
  have e1 : p - 1 - β = d := by omega
  have e2 : p - 1 - d = β := by omega
  have hdβ : 1 ≤ d ∧ 1 ≤ β := by omega
  have hc : v c = 1 ∨ v c = 2 ∨ v c = 3 := by omega
  rcases hc with hc | hc | hc
  · have hvb' : v b = p - 1 := by omega
    refine exc_mk v a b c hab hac hbc hother d β 1 (by omega) (by omega) (by omega)
      (by omega) hcong ?_
    rw [hva, hvb', hc, e2, e1]
    nlinarith [hdβ.1, hdβ.2]
  · have hvb' : v b = p - 2 := by omega
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    refine exc_mk v a b c hab hac hbc hother (d' + 1) β 1 (by omega) (by omega) (by omega)
      (by omega) hcong ?_
    have e3 : p - 2 - β = d' := by omega
    rw [hva, hvb', hc, e2, e3]
    nlinarith [hdβ.1, hdβ.2]
  · have hvb' : v b = p - 3 := by omega
    by_cases hbp : β = p - 2
    · have hz2 : z = 2 := by
        rw [hbp, Nat.cast_sub (by omega), ZMod.natCast_self] at hβ
        push_cast at hβ
        linear_combination hβ
      refine exc_mk v a b c hab hac hbc hother 2 (p - 4) 2 (by omega) (by omega) (by omega)
        (by omega) ?_ ?_
      · have h4 : ((p - 4 : ℕ) : ZMod p) = -4 := by
          rw [Nat.cast_sub (by omega), ZMod.natCast_self]; push_cast; ring
        rw [h4]
        push_cast
        linear_combination (-2) * hz + 2 * (b - a) * hz2
      · have e4 : p - 3 - (p - 4) = 1 := by omega
        rw [hva, hvb', hc, e4]
        omega
    · obtain ⟨d', rfl⟩ : ∃ d', d = d' + 2 := ⟨d - 2, by omega⟩
      refine exc_mk v a b c hab hac hbc hother (d' + 2) β 1 (by omega) (by omega) (by omega)
        (by omega) hcong ?_
      have e3 : p - 3 - β = d' := by omega
      have e5 : p - 1 - (d' + 2) = β := by omega
      rw [hva, hvb', hc, e5, e3]
      have h6 := Nat.mul_le_mul_left (d' + 1) hdβ.2
      nlinarith [h6, Nat.zero_le (β * d')]

end Harborth
