import Harborth.ShapeDefs

/-!
# Shape Lemma for odd `p ≥ 17`

The argument is Section 4 of the paper with integer inequalities in place of the square roots:

* if `⌊N(1)²/4⌋ ≥ p - 1` for the support `N(1)`, rule B works (`slcw_ruleB`);
* otherwise take the least `ρ = y + 1` with `∑_{i ≤ ρ} ⌊N(i)²/4⌋ ≥ p - 1` and rule H(ρ):
  - for `2y ≤ p - 3` (case 3a) Cauchy–Schwarz on the first `y` layers and the polynomial
    inequality `G p y ≥ 0` give the weight;
  - for `2y ≥ p - 1` (case 3b) there are exactly two classes of size `≥ y`, and the weight
    bound fails only for the exceptional shapes.
-/

namespace Harborth.ShapeAux

open Finset

/-- The polynomial inequality behind case 3a (it replaces the paper's `F(p, y) ≥ 0`). -/
theorem G_nonneg (p y : ℤ) (hp : 17 ≤ p) (hy : 1 ≤ y) (h2y : 2 * y ≤ p - 3) :
    (y + 2) ^ 2 * (2 * y + 5) ^ 2 * (4 * p - 8 + y) ≤
      y * ((4 * y + 6) * p - (2 * y + 1)) ^ 2 := by
  rcases (by omega : y ≤ 5 ∨ 6 ≤ y) with h | h
  · obtain ⟨q, rfl⟩ : ∃ q : ℕ, p = 17 + q := ⟨(p - 17).toNat, by omega⟩
    have hq : (0 : ℤ) ≤ q := by positivity
    interval_cases y <;> nlinarith [mul_nonneg hq hq]
  · obtain ⟨z, rfl⟩ : ∃ z : ℕ, y = 6 + z := ⟨(y - 6).toNat, by omega⟩
    obtain ⟨q, rfl⟩ : ∃ q : ℕ, p = 2 * (6 + z) + 3 + q := ⟨(p - 2 * (6 + z) - 3).toNat, by omega⟩
    rw [← sub_nonneg]
    have : ((6 + (z : ℤ)) * ((4 * (6 + z) + 6) * (2 * (6 + z) + 3 + q) - (2 * (6 + z) + 1)) ^ 2 -
        (6 + z + 2) ^ 2 * (2 * (6 + z) + 5) ^ 2 * (4 * (2 * (6 + z) + 3 + q) - 8 + (6 + z))) =
        28 * z ^ 5 + 48 * z ^ 4 * q + 852 * z ^ 4 + 16 * z ^ 3 * q ^ 2 + 1280 * z ^ 3 * q +
        9891 * z ^ 3 + 336 * z ^ 2 * q ^ 2 + 12588 * z ^ 2 * q + 53130 * z ^ 2 +
        2340 * z * q ^ 2 + 53772 * z * q + 122689 * z + 5400 * q ^ 2 + 83336 * q + 73046 := by
      ring
    rw [this]
    positivity

/-- Integer core of case 3a: `S'` is the sum of the first `y` layers, `A` the `y`-th layer and
`L` the sum of the first `y + 2` layers. -/
theorem ineq3a (p y S' A L : ℤ) (hp : 17 ≤ p) (hy : 1 ≤ y) (h2y : 2 * y ≤ p - 3)
    (hS'0 : 0 ≤ S') (hcs : S' ^ 2 ≤ y * (4 * (p - 2) + y)) (hya : y * A ≤ S')
    (hL : L ≤ S' + 2 * A) : 4 * (p - 1) ≤ (2 * y + 5) * (2 * p - 1 - L) := by
  have hG := G_nonneg p y hp hy h2y
  set R := (4 * y + 6) * p - (2 * y + 1) with hR
  have hR0 : 0 ≤ R := by nlinarith
  have hc0 : 0 ≤ (y + 2) * (2 * y + 5) * S' := by positivity
  have hsq : ((y + 2) * (2 * y + 5) * S') ^ 2 ≤ (y * R) ^ 2 := by
    have h1 : ((y + 2) * (2 * y + 5) * S') ^ 2 = (y + 2) ^ 2 * (2 * y + 5) ^ 2 * S' ^ 2 := by ring
    have h2 : (y + 2) ^ 2 * (2 * y + 5) ^ 2 * S' ^ 2 ≤
        (y + 2) ^ 2 * (2 * y + 5) ^ 2 * (y * (4 * (p - 2) + y)) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    have h3 : (y + 2) ^ 2 * (2 * y + 5) ^ 2 * (y * (4 * (p - 2) + y)) ≤ y * (y * R ^ 2) := by
      have : (y + 2) ^ 2 * (2 * y + 5) ^ 2 * (y * (4 * (p - 2) + y)) =
          y * ((y + 2) ^ 2 * (2 * y + 5) ^ 2 * (4 * p - 8 + y)) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hG (by omega)
    nlinarith
  have hcs' : (y + 2) * (2 * y + 5) * S' ≤ y * R :=
    (pow_le_pow_iff_left₀ hc0 (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).1 hsq
  have hyL : y * L ≤ (y + 2) * S' := by nlinarith
  have key : y * (4 * (p - 1)) ≤ y * ((2 * y + 5) * (2 * p - 1 - L)) := by nlinarith
  exact le_of_mul_le_mul_left key (by omega)

section Cases

variable {α : Type*} [Fintype α]

/-- Spread of the first `ρ` layers of `v`. -/
def spr (v : α → ℕ) (ρ : ℕ) : ℕ := ∑ i ∈ range ρ, lay v (i + 1) ^ 2 / 4

theorem spr_mono (v : α → ℕ) {a b : ℕ} (h : a ≤ b) : spr v a ≤ spr v b :=
  sum_le_sum_of_subset (range_subset_range.2 h)

theorem sum_lay_le_spr (v : α → ℕ) (y : ℕ) :
    ∑ i ∈ range y, lay v (i + 1) ≤ spr v y + y := by
  unfold spr
  calc ∑ i ∈ range y, lay v (i + 1) ≤ ∑ i ∈ range y, (lay v (i + 1) ^ 2 / 4 + 1) :=
        sum_le_sum (fun i _ => nat_le_sq_div_four_add_one _)
    _ = _ := by rw [sum_add_distrib]; simp

theorem sum_sub_add_min (v : α → ℕ) (k : ℕ) :
    ∑ g, (v g - k) + ∑ i ∈ range k, lay v (i + 1) = ∑ g, v g := by
  rw [← sum_min_eq, ← sum_add_distrib]
  exact sum_congr rfl (fun g _ => by omega)

/-- Case 3a: the weight bound of rule H(y+1). -/
theorem weight3a (p : ℕ) (v : α → ℕ)
    (hsum : ∑ g, v g = 2 * p - 1) (hp : 17 ≤ p) (y : ℕ) (hy : 1 ≤ y) (h2y : 2 * y + 3 ≤ p)
    (hSy : spr v y ≤ p - 2) :
    4 * (p - 1) ≤ ∑ g, (v g ^ 2 - hcap (y + 1) (v g) ^ 2) := by
  -- the weight is at least `(2y+5) · ∑ (v - (y+2))`
  have hW : (2 * y + 5) * ∑ g, (v g - (y + 2)) ≤ ∑ g, (v g ^ 2 - hcap (y + 1) (v g) ^ 2) := by
    rw [mul_sum]
    exact sum_le_sum (fun g _ => by
      have := hcap_weight_lin (y + 1) (v g)
      rwa [show 2 * (y + 1) + 3 = 2 * y + 5 by ring, show y + 1 + 1 = y + 2 by ring] at this)
  have hsplit := sum_sub_add_min v (y + 2)
  rw [hsum] at hsplit
  set L := ∑ i ∈ range (y + 2), lay v (i + 1) with hL
  set S' := ∑ i ∈ range y, lay v (i + 1) with hS'
  set A := lay v y with hA
  have hL' : L = S' + lay v (y + 1) + lay v (y + 2) := by
    rw [hL, sum_range_succ, sum_range_succ]
  have hA1 : lay v (y + 1) ≤ A := lay_anti v (by omega)
  have hA2 : lay v (y + 2) ≤ A := lay_anti v (by omega)
  have hyA : y * A ≤ S' := by
    have : ∑ _i ∈ range y, A ≤ S' := sum_le_sum (fun i hi => lay_anti v (by simp at hi; omega))
    simpa using this
  have hcs : S' ^ 2 ≤ y * (4 * (p - 2) + y) := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := range y) (f := fun i => lay v (i + 1))
    simp only [card_range] at h1
    have h2 : ∑ i ∈ range y, lay v (i + 1) ^ 2 ≤ 4 * (p - 2) + y := by
      calc ∑ i ∈ range y, lay v (i + 1) ^ 2 ≤ ∑ i ∈ range y, (4 * (lay v (i + 1) ^ 2 / 4) + 1) :=
            sum_le_sum (fun i _ => sq_le_four_mul_sq_div_four_add_one _)
        _ = 4 * spr v y + y := by rw [sum_add_distrib, ← mul_sum]; simp [spr]
        _ ≤ 4 * (p - 2) + y := by omega
    exact h1.trans (Nat.mul_le_mul_left _ h2)
  have hineq := ineq3a p y S' A L (by exact_mod_cast hp) (by exact_mod_cast hy)
    (by omega) (by positivity)
    (by have h := (Nat.cast_le (α := ℤ)).2 hcs
        push_cast [Nat.cast_sub (by omega : 2 ≤ p)] at h
        exact h)
    (by exact_mod_cast hyA) (by push_cast [hL']; have := hA1; have := hA2; omega)
  set T := ∑ g, (v g - (y + 2)) with hT
  have hcast : ((4 * (p - 1) : ℕ) : ℤ) ≤ (((2 * y + 5) * T : ℕ) : ℤ) := by
    have e : (T : ℤ) = 2 * p - 1 - L := by
      have : (T : ℤ) + L = ((2 * p - 1 : ℕ) : ℤ) := by
        exact_mod_cast hsplit
      push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * p)] at this
      linarith
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)] at e ⊢
    rw [e]
    linarith
  exact (by exact_mod_cast hcast : 4 * (p - 1) ≤ (2 * y + 5) * T).trans hW

theorem sq_div_four_eq (u : ℕ) : (u + 2) ^ 2 / 4 = 1 + u + u ^ 2 / 4 := by
  rw [show (u + 2) ^ 2 = u ^ 2 + (u + 1) * 4 by ring, Nat.add_mul_div_right _ _ (by norm_num)]
  ring

/-- Case 3b (Section 4 of the paper, large regime): rule H(y+1) has enough weight, or `v` is exceptional. -/
theorem case3b (p : ℕ) (v : α → ℕ) (hv : ∀ g, v g ≤ p - 1)
    (hsum : ∑ g, v g = 2 * p - 1) (hp : 17 ≤ p) (y : ℕ) (h2y : p ≤ 2 * y + 1) (hyp : y + 1 ≤ p)
    (hSy : spr v y ≤ p - 2) (hSρ : p - 1 ≤ spr v (y + 1)) :
    4 * (p - 1) ≤ ∑ g, (v g ^ 2 - hcap (y + 1) (v g) ^ 2) ∨ Exc α p v := by
  classical
  -- exactly two classes reach level `y`
  have hle2 : lay v y ≤ 2 := by
    by_contra h
    have : 2 * y ≤ spr v y := by
      unfold spr
      calc 2 * y = ∑ _i ∈ range y, 2 := by simp [mul_comm]
        _ ≤ _ := sum_le_sum (fun i hi => by
            have h3' : 3 ≤ lay v y := by omega
            have h3 : 3 ≤ lay v (i + 1) := le_trans h3' (lay_anti v (by simp at hi; omega))
            rw [Nat.le_div_iff_mul_le (by norm_num)]
            nlinarith)
    omega
  have hge2 : 2 ≤ lay v y := by
    by_contra h
    have e1 := sum_eq_layers v (p - 1) hv
    rw [← sum_range_add_sum_Ico _ (show y - 1 ≤ p - 1 by omega), hsum] at e1
    have h1 := sum_lay_le_spr v (y - 1)
    have h2 := spr_mono v (show y - 1 ≤ y by omega)
    have h3 : ∑ i ∈ Ico (y - 1) (p - 1), lay v (i + 1) ≤ ∑ _i ∈ Ico (y - 1) (p - 1), 1 :=
      sum_le_sum (fun i hi => by
        have := lay_anti v (show y ≤ i + 1 by simp at hi; omega)
        omega)
    simp only [sum_const, Nat.card_Ico, smul_eq_mul, mul_one] at h3
    omega
  have hlay : (univ.filter (fun g => y ≤ v g)).card = 2 := by
    have := le_antisymm hle2 hge2; unfold lay at this; exact this
  obtain ⟨a, b, hab, hF⟩ := Finset.card_eq_two.1 hlay
  have ha : y ≤ v a := by
    have : a ∈ univ.filter (fun g => y ≤ v g) := by rw [hF]; simp
    simpa using this
  have hb : y ≤ v b := by
    have : b ∈ univ.filter (fun g => y ≤ v g) := by rw [hF]; simp
    simpa using this
  have hoth : ∀ g, g ≠ a → g ≠ b → v g < y := by
    intro g hga hgb
    by_contra hc
    have : g ∈ univ.filter (fun g => y ≤ v g) := by simp; omega
    rw [hF] at this
    simp at this
    tauto
  -- the layers below `y` are `2 + t i`
  have hlay2 : ∀ i ∈ range y, 2 ≤ lay v (i + 1) := fun i hi =>
    le_trans hge2 (lay_anti v (by simp at hi; omega))
  set s' := ∑ i ∈ range y, (lay v (i + 1) - 2) with hs'
  set Q := ∑ i ∈ range y, (lay v (i + 1) - 2) ^ 2 / 4 with hQ
  have hSdec : spr v y = y + s' + Q := by
    unfold spr
    rw [hs', hQ]
    have : ∀ i ∈ range y, lay v (i + 1) ^ 2 / 4 =
        1 + ((lay v (i + 1) - 2) + (lay v (i + 1) - 2) ^ 2 / 4) := fun i hi => by
      have := sq_div_four_eq (lay v (i + 1) - 2)
      rw [show lay v (i + 1) - 2 + 2 = lay v (i + 1) by have := hlay2 i hi; omega] at this
      rw [this]; ring
    rw [sum_congr rfl this, sum_add_distrib, sum_add_distrib]
    simp [add_assoc]
  have hsumlay : ∑ i ∈ range y, lay v (i + 1) = 2 * y + s' := by
    rw [hs']
    have : ∀ i ∈ range y, lay v (i + 1) = 2 + (lay v (i + 1) - 2) := fun i hi => by
      have := hlay2 i hi; omega
    rw [sum_congr rfl this, sum_add_distrib]
    simp [mul_comm]
  -- the spread is exactly `p - 2` below `ρ = y + 1`
  have hSeq : y + s' + Q = p - 2 := by
    have h1 : spr v (y + 1) = spr v y + lay v (y + 1) ^ 2 / 4 := by
      unfold spr; rw [sum_range_succ]
    have h2 : lay v (y + 1) ^ 2 / 4 ≤ 1 := by
      have : lay v (y + 1) ≤ 2 := le_trans (lay_anti v (by omega)) hle2
      have : lay v (y + 1) ^ 2 ≤ 4 := by nlinarith
      omega
    omega
  -- the two big classes and the tail
  have hab_sum : v a + v b + s' = 2 * p - 1 := by
    have h1 := sum_sub_add_min v y
    rw [Fintype.sum_eq_add a b hab (fun g ⟨hga, hgb⟩ => by have := hoth g hga hgb; omega),
      hsumlay, hsum] at h1
    omega
  -- weight of the two big classes
  have hWab : 4 * ((v a - (y + 1)) / 2) * (y + 1 + 1) + 4 * ((v b - (y + 1)) / 2) * (y + 1 + 1) ≤
      ∑ g, (v g ^ 2 - hcap (y + 1) (v g) ^ 2) := by
    refine le_trans (add_le_add (hcap_weight_half (y + 1) (v a)) (hcap_weight_half (y + 1) (v b)))
      ?_
    rw [← sum_pair hab (f := fun g => v g ^ 2 - hcap (y + 1) (v g) ^ 2)]
    exact sum_le_sum_of_subset (subset_univ _)
  have hva := hv a
  have hvb := hv b
  by_cases hc : 2 ≤ (v a - (y + 1)) / 2 + (v b - (y + 1)) / 2
  · left
    refine le_trans ?_ hWab
    set ca := (v a - (y + 1)) / 2
    set cb := (v b - (y + 1)) / 2
    calc 4 * (p - 1) ≤ 4 * (2 * (y + 1 + 1)) := by omega
      _ ≤ 4 * ((ca + cb) * (y + 1 + 1)) := by gcongr
      _ = _ := by ring
  · right
    have h3 : s' + 2 * Q ≤ 3 := by omega
    have hs1 : 1 ≤ s' := by omega
    have hy1 : 0 ∈ range y := by simp; omega
    have ht0 : lay v 1 - 2 ≤ s' :=
      single_le_sum (f := fun i => lay v (i + 1) - 2) (fun _ _ => Nat.zero_le _) hy1
    have hq0 : (lay v 1 - 2) ^ 2 / 4 ≤ Q :=
      single_le_sum (f := fun i => (lay v (i + 1) - 2) ^ 2 / 4) (fun _ _ => Nat.zero_le _) hy1
    have hl1 : lay v 1 ≤ 3 := by
      by_contra h
      have : 1 ≤ (lay v 1 - 2) ^ 2 / 4 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]
        have : 2 ≤ lay v 1 - 2 := by omega
        have := Nat.pow_le_pow_left this 2
        omega
      omega
    have hl1' : 3 ≤ lay v 1 := by
      by_contra h
      have : s' = 0 := by
        rw [hs']
        exact sum_eq_zero (fun i _ => by have := lay_anti v (show 1 ≤ i + 1 by omega); omega)
      omega
    have hQ0 : Q = 0 := by
      rw [hQ]
      exact sum_eq_zero (fun i _ => by
        have := lay_anti v (show 1 ≤ i + 1 by omega)
        have : lay v (i + 1) - 2 ≤ 1 := by omega
        have := Nat.pow_le_pow_left this 2
        simp only [one_pow] at this
        omega)
    -- the third class
    set F := univ.filter (fun g => 1 ≤ v g) with hFdef
    have hF3 : F.card = 3 := by have := le_antisymm hl1 hl1'; unfold lay at this; exact this
    have haF : a ∈ F := by simp [hFdef]; omega
    have hbF : b ∈ F.erase a := by simp [hFdef]; exact ⟨fun h => hab h.symm, by omega⟩
    have hc1 : ((F.erase a).erase b).card = 1 := by
      rw [card_erase_of_mem hbF, card_erase_of_mem haF, hF3]
    obtain ⟨c, hcF⟩ := Finset.card_eq_one.1 hc1
    have hcmem : c ∈ (F.erase a).erase b := by rw [hcF]; simp
    simp only [mem_erase, hFdef, mem_filter, mem_univ, true_and] at hcmem
    obtain ⟨hcb, hca, hc1'⟩ := hcmem
    have hzero : ∀ g, g ≠ a → g ≠ b → g ≠ c → v g = 0 := by
      intro g hga hgb hgc
      by_contra hg
      have : g ∈ (F.erase a).erase b := by simp [hFdef, hga, hgb]; omega
      rw [hcF] at this
      simp at this
      exact hgc this
    have hFeq : F = insert a (insert b {c}) := by
      rw [← hcF, insert_erase hbF, insert_erase haF]
    have hsumabc : ∑ g, v g = v a + v b + v c := by
      rw [← sum_subset (subset_univ F) (fun g _ hg => by simp [hFdef] at hg; omega), hFeq,
        sum_insert (by simp; exact ⟨hab, fun h => hca h.symm⟩),
        sum_insert (by simp; exact fun h => hcb h.symm), sum_singleton]
      ring
    have hvc : v c = s' := by omega
    rcases (by omega : (v a = p - 1 ∧ v b + v c = p) ∨ (v b = p - 1 ∧ v a + v c = p)) with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨a, b, c, hab, fun h => hca h.symm, fun h => hcb h.symm, h1, h2, by omega, by omega,
        hzero⟩
    · exact ⟨b, a, c, fun h => hab h.symm, fun h => hcb h.symm, fun h => hca h.symm, h1, h2,
        by omega, by omega, fun g h1 h2 h3 => hzero g h2 h1 h3⟩

theorem spr_full (p : ℕ) (v : α → ℕ) (hv : ∀ g, v g ≤ p - 1) (hsum : ∑ g, v g = 2 * p - 1) :
    p - 1 ≤ spr v p := by
  have h1 := sum_lay_le_spr v p
  rw [← sum_eq_layers v p (fun g => by have := hv g; omega), hsum] at h1
  omega

/-- The Shape Lemma for odd `p ≥ 17` (Section 4 of the paper, with Section 5 for `(p-2, p-2, 3)` built in). -/
theorem shape_large (p : ℕ) (hcard : Fintype.card α = p) (hp : 17 ≤ p) (hodd : p % 2 = 1)
    (v : α → ℕ) (hv : ∀ g, v g ≤ p - 1) (hsum : ∑ g, v g = 2 * p - 1)
    (hconc : 2 * p - 4 ≤ ∑ g, (v g).choose 2) : ShapeConcl α p v := by
  by_cases hm : p - 1 ≤ lay v 1 ^ 2 / 4
  · exact Or.inl (slcw_ruleB p hcard v hsum hconc hp hodd hm)
  have hex : ∃ ρ, p - 1 ≤ spr v ρ := ⟨p, spr_full p v hv hsum⟩
  have hρ : p - 1 ≤ spr v (Nat.find hex) := Nat.find_spec hex
  have hρp : Nat.find hex ≤ p := Nat.find_min' hex (spr_full p v hv hsum)
  have hρ2 : 2 ≤ Nat.find hex := by
    by_contra h
    rcases (by omega : Nat.find hex = 0 ∨ Nat.find hex = 1) with h0 | h0 <;>
      rw [h0] at hρ <;> simp [spr] at hρ <;> omega
  obtain ⟨y, hy⟩ : ∃ y, Nat.find hex = y + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hSy : spr v y ≤ p - 2 := by
    have := Nat.find_min hex (show y < Nat.find hex by omega)
    omega
  rw [hy] at hρ hρp
  have hS : p - 1 ≤ ∑ i ∈ range (y + 1), lay v (i + 1) ^ 2 / 4 := hρ
  by_cases h2y : 2 * y + 3 ≤ p
  · exact Or.inl ⟨_, slcw_hcap p hcard v hsum (by omega) (y + 1) hρp hS
      (weight3a p v hsum hp y (by omega) h2y hSy)⟩
  · rcases case3b p v hv hsum hp y (by omega) hρp hSy hρ with hW | hE
    · exact Or.inl ⟨_, slcw_hcap p hcard v hsum (by omega) (y + 1) hρp hS hW⟩
    · exact Or.inr hE

end Cases

end Harborth.ShapeAux
