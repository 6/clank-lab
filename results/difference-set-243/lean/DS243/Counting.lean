import DS243.Basic

/-!
# Counting arguments for a multiplier-fixed difference set

* A permutation of order dividing 3 fixes, modulo 3, as many points of an invariant set
  as the set has elements (`card_modEq_fixed`).
* Coset counts of an index-3 subgroup `ker (form a b c)` satisfy `∑ t = 121` and
  `∑ t² = 4921`; the only solutions are permutations of `(36, 40, 45)`.
* For a fixed difference set `D`, with `S = D ∩ H`: `|S| = 13`, and
  `diffCount S h ≡ 0 (mod 3)` for every nonzero `h ∈ H`.
* Every coset count and every cell count of a fixed set is congruent mod 3 to its
  intersection with `H`.
-/

namespace DS243

open Finset

/-- Orbit counting for a permutation of order dividing three. -/
theorem card_modEq_fixed {α : Type*} [DecidableEq α] (σ : α → α) (hσ : ∀ x, σ (σ (σ x)) = x)
    (T : Finset α) (hT : ∀ x ∈ T, σ x ∈ T) :
    T.card ≡ (T.filter fun x => σ x = x).card [MOD 3] := by
  have inj : Function.Injective σ := fun a b h => by rw [← hσ a, ← hσ b, h]
  induction T using Finset.strongInduction with
  | H T ih =>
  by_cases hall : ∀ x ∈ T, σ x = x
  · rw [filter_true_of_mem hall]
  obtain ⟨x, hx, hσx⟩ : ∃ x ∈ T, σ x ≠ x := by simpa using hall
  have h2 : σ (σ x) ≠ x := fun h => hσx (by simpa [h] using hσ x)
  have h3 : σ (σ x) ≠ σ x := fun h => hσx (inj h)
  -- remove the orbit `O = {x, σ x, σ² x}`
  set O : Finset α := {x, σ x, σ (σ x)} with hO
  have hOT : O ⊆ T := by
    intro y hy
    simp only [hO, mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact hx
    · exact hT _ hx
    · exact hT _ (hT _ hx)
  have hOc : O.card = 3 := card_eq_three.2 ⟨_, _, _, hσx.symm, h2.symm, h3.symm, rfl⟩
  have hsub : T \ O ⊂ T := by
    refine ⟨sdiff_subset, fun h => ?_⟩
    have := h hx
    simp [hO] at this
  have hT' : ∀ y ∈ T \ O, σ y ∈ T \ O := by
    intro y hy
    simp only [mem_sdiff, hO, mem_insert, mem_singleton, not_or] at hy ⊢
    obtain ⟨hyT, hyx, hyσ, hyσσ⟩ := hy
    refine ⟨hT y hyT, ?_, fun h => hyx (inj h), fun h => hyσ (inj h)⟩
    intro h; apply hyσσ; rw [← h, hσ]
  have hfil : (T \ O).filter (fun y => σ y = y) = T.filter (fun y => σ y = y) := by
    ext y
    simp only [mem_filter, mem_sdiff, hO, mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨hy, -⟩, h⟩; exact ⟨hy, h⟩
    · rintro ⟨hy, h⟩
      refine ⟨⟨hy, ?_⟩, h⟩
      rintro (rfl | rfl | rfl)
      · exact hσx h
      · exact h3 h
      · rw [hσ] at h; exact h2 h.symm
  have hc : T.card = (T \ O).card + 3 := by
    rw [card_sdiff_of_subset hOT, hOc]; have := card_le_card hOT; omega
  have := ih _ hsub hT'
  rw [hfil] at this
  unfold Nat.ModEq at *; omega

/-- Number of elements of `D` in the coset `form a b c = i`. -/
def cosetCount (D : Finset G) (a b c i : ZMod 3) : ℕ := (D.filter fun x => form a b c x = i).card

/-- Number of elements of `D` in the cell `q` of `Q = G / 3G`. -/
def cellCount (D : Finset G) (q : ZMod 3 × ZMod 3 × ZMod 3) : ℕ :=
  (D.filter fun x => cell x = q).card

/-! ### Finite facts about `G`, checked by evaluation -/

/-- Multiplication by `61` has order dividing three on `G`. -/
lemma smul61_cube (x : G) : (61 : ℕ) • (61 : ℕ) • (61 : ℕ) • x = x := by
  revert x; decide +kernel

/-- The fixed points of multiplication by `61` are exactly the points of `H`. -/
lemma smul61_eq_self (x : G) : (61 : ℕ) • x = x ↔ x ∈ H := by
  rw [mem_H]; revert x; decide +kernel

/-- Multiplication by `61` preserves cells. -/
lemma cell_smul61 (x : G) : cell ((61 : ℕ) • x) = cell x := by
  revert x; decide +kernel

/-- Multiplication by `61` preserves every linear form. -/
lemma form_smul61 (a b c : ZMod 3) (x : G) : form a b c ((61 : ℕ) • x) = form a b c x := by
  revert a b c x; decide +kernel

/-- A nonzero form has a kernel of index three. -/
lemma card_ker_form : ∀ a b c : ZMod 3, (a, b, c) ≠ (0, 0, 0) →
    (univ.filter fun x : G => form a b c x = 0).card = 81 := by
  decide +kernel

/-- Linear forms are additive. -/
lemma form_sub (a b c : ZMod 3) (x y : G) :
    form a b c (x - y) = form a b c x - form a b c y := by
  simp only [form, red, Prod.fst_sub, Prod.snd_sub, map_sub]; ring

/-- A sum over `ZMod 3`. -/
lemma sum_zmod3 (f : ZMod 3 → ℕ) : ∑ i, f i = f 0 + f 1 + f 2 := Fin.sum_univ_three f

lemma diffCount_zero (D : Finset G) : diffCount D 0 = D.card := by
  rw [diffCount_eq_card_filter]; simp

/-- Sum of the coset counts of `D`. -/
lemma sum_cosetCount (D : Finset G) (a b c : ZMod 3) :
    cosetCount D a b c 0 + cosetCount D a b c 1 + cosetCount D a b c 2 = D.card := by
  rw [card_eq_sum_card_fiberwise (f := form a b c) (t := univ) (fun _ _ => mem_univ _),
    sum_zmod3]
  rfl

/-- Orbit counting for the multiplier `61` on an invariant subset of a fixed set. -/
lemma card_modEq_H {D : Finset G} (hF : Fixed D) (p : G → Prop) [DecidablePred p]
    (hp : ∀ x, p ((61 : ℕ) • x) ↔ p x) :
    (D.filter p).card ≡ ((D.filter (· ∈ H)).filter p).card [MOD 3] := by
  have h := card_modEq_fixed (fun x : G => (61 : ℕ) • x) smul61_cube (D.filter p)
    (fun x hx => by
      simp only [mem_filter] at hx ⊢
      exact ⟨hF x hx.1, (hp x).2 hx.2⟩)
  convert h using 2
  ext x
  simp only [mem_filter, smul61_eq_self]
  tauto

theorem coset_sum {D : Finset G} (hD : IsDiffSet D) (a b c : ZMod 3) :
    cosetCount D a b c 0 + cosetCount D a b c 1 + cosetCount D a b c 2 = 121 := by
  rw [sum_cosetCount, hD.1]

theorem coset_sq_sum {D : Finset G} (hD : IsDiffSet D) (a b c : ZMod 3)
    (habc : (a, b, c) ≠ (0, 0, 0)) :
    cosetCount D a b c 0 ^ 2 + cosetCount D a b c 1 ^ 2 + cosetCount D a b c 2 ^ 2 = 4921 := by
  set K : Finset G := univ.filter fun x => form a b c x = 0 with hK
  -- `∑ tᵢ²` counts pairs in `D × D` with equal form values
  have hA : cosetCount D a b c 0 ^ 2 + cosetCount D a b c 1 ^ 2 + cosetCount D a b c 2 ^ 2 =
      ((D ×ˢ D).filter fun p => form a b c (p.1 - p.2) = 0).card := by
    rw [card_eq_sum_card_fiberwise (f := fun p : G × G => form a b c p.1) (t := univ)
      (fun _ _ => mem_univ _), sum_zmod3]
    have e : ∀ i, cosetCount D a b c i ^ 2 = (((D ×ˢ D).filter fun p =>
        form a b c (p.1 - p.2) = 0).filter fun p => form a b c p.1 = i).card := by
      intro i
      rw [cosetCount, sq, ← card_product]
      congr 1
      ext ⟨x, y⟩
      simp only [mem_filter, mem_product, form_sub, sub_eq_zero]
      constructor
      · rintro ⟨⟨hx, rfl⟩, hy, hxy⟩; exact ⟨⟨⟨hx, hy⟩, hxy.symm⟩, rfl⟩
      · rintro ⟨⟨⟨hx, hy⟩, hxy⟩, rfl⟩; exact ⟨⟨hx, rfl⟩, hy, hxy.symm⟩
    rw [e, e, e]
  -- group those pairs by their difference, which lies in `K`
  have hB : ((D ×ˢ D).filter fun p => form a b c (p.1 - p.2) = 0).card =
      ∑ g ∈ K, diffCount D g := by
    rw [card_eq_sum_card_fiberwise (f := fun p : G × G => p.1 - p.2) (t := K)
      (fun p hp => by simp only [coe_filter, Set.mem_setOf_eq, hK, mem_univ, true_and] at hp ⊢; exact hp.2)]
    refine sum_congr rfl fun g hg => ?_
    rw [diffCount, filter_filter]
    congr 1
    refine filter_congr fun p _ => ?_
    simp only [hK, mem_filter, mem_univ, true_and] at hg
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨h ▸ hg, h⟩
  have h0 : (0 : G) ∈ K := by simp [hK, form, red]
  rw [hA, hB, ← add_sum_erase _ _ h0, diffCount_zero, hD.1,
    sum_congr rfl fun g hg => hD.2 g (ne_of_mem_erase hg), sum_const, card_erase_of_mem h0,
    hK, card_ker_form a b c habc, smul_eq_mul]

/-- The only nonnegative integer solutions of `t₀+t₁+t₂ = 121`, `t₀²+t₁²+t₂² = 4921`. -/
theorem triple_cases (t0 t1 t2 : ℕ) (h1 : t0 + t1 + t2 = 121)
    (h2 : t0 ^ 2 + t1 ^ 2 + t2 ^ 2 = 4921) :
    (t0 = 36 ∧ t1 = 40 ∧ t2 = 45) ∨ (t0 = 36 ∧ t1 = 45 ∧ t2 = 40) ∨
    (t0 = 40 ∧ t1 = 36 ∧ t2 = 45) ∨ (t0 = 40 ∧ t1 = 45 ∧ t2 = 36) ∨
    (t0 = 45 ∧ t1 = 36 ∧ t2 = 40) ∨ (t0 = 45 ∧ t1 = 40 ∧ t2 = 36) := by
  have b0 : t0 < 71 := by nlinarith
  have b1 : t1 < 71 := by nlinarith
  obtain rfl : t2 = 121 - t0 - t1 := by omega
  have key : ∀ u0 u1 : Fin 71, (u0 : ℕ) + u1 ≤ 121 →
      (u0 : ℕ) ^ 2 + (u1 : ℕ) ^ 2 + (121 - u0 - u1) ^ 2 = 4921 →
      ((u0 : ℕ) = 36 ∧ (u1 : ℕ) = 40) ∨ ((u0 : ℕ) = 36 ∧ (u1 : ℕ) = 45) ∨
      ((u0 : ℕ) = 40 ∧ (u1 : ℕ) = 36) ∨ ((u0 : ℕ) = 40 ∧ (u1 : ℕ) = 45) ∨
      ((u0 : ℕ) = 45 ∧ (u1 : ℕ) = 36) ∨ ((u0 : ℕ) = 45 ∧ (u1 : ℕ) = 40) := by
    decide +kernel
  rcases key ⟨t0, b0⟩ ⟨t1, b1⟩ (by simp; omega) h2 with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

/-- Coset counts of a fixed set are congruent mod 3 to their part in `H`. -/
theorem cosetCount_modEq {D : Finset G} (hF : Fixed D) (a b c i : ZMod 3) :
    cosetCount D a b c i ≡ cosetCount (D.filter (· ∈ H)) a b c i [MOD 3] := by
  exact card_modEq_H hF _ fun x => by rw [form_smul61]

/-- Cell counts of a fixed set are congruent mod 3 to their part in `H`. -/
theorem cellCount_modEq {D : Finset G} (hF : Fixed D) (q : ZMod 3 × ZMod 3 × ZMod 3) :
    cellCount D q ≡ cellCount (D.filter (· ∈ H)) q [MOD 3] := by
  exact card_modEq_H hF _ fun x => by rw [cell_smul61]

/-- A nonzero form vanishing on `H` has exactly 40 points of a fixed difference set in its
kernel: the other two coset counts are `≡ 0 (mod 3)`, so they are 36 and 45. -/
lemma cosetCount_zero_of_vanish {D : Finset G} (hD : IsDiffSet D) (hF : Fixed D)
    (a b c : ZMod 3) (habc : (a, b, c) ≠ (0, 0, 0))
    (hvan : ∀ x : G, 3 • x = 0 → form a b c x = 0) : cosetCount D a b c 0 = 40 := by
  have hz : ∀ i : ZMod 3, i ≠ 0 → cosetCount (D.filter (· ∈ H)) a b c i = 0 := by
    intro i hi
    rw [cosetCount, card_eq_zero, filter_eq_empty_iff]
    intro x hx
    simp only [mem_filter, mem_H] at hx
    rw [hvan x hx.2]; exact hi.symm
  have m1 := cosetCount_modEq hF a b c 1
  have congruence_two := cosetCount_modEq hF a b c 2
  rw [hz 1 (by decide)] at m1
  rw [hz 2 (by decide)] at congruence_two
  unfold Nat.ModEq at m1 congruence_two
  rcases triple_cases _ _ _ (coset_sum hD a b c) (coset_sq_sum hD a b c habc) with
    h | h | h | h | h | h <;> omega

/-- `|D ∩ H| = 13` for a fixed difference set. -/
theorem card_S {D : Finset G} (hD : IsDiffSet D) (hF : Fixed D) :
    (D.filter (· ∈ H)).card = 13 := by
  -- the four forms ignoring the first coordinate vanish on `H`
  have e1 := cosetCount_zero_of_vanish hD hF 0 1 0 (by decide) (by decide +kernel)
  have e2 := cosetCount_zero_of_vanish hD hF 0 0 1 (by decide) (by decide +kernel)
  have e3 := cosetCount_zero_of_vanish hD hF 0 1 1 (by decide) (by decide +kernel)
  have e4 := cosetCount_zero_of_vanish hD hF 0 1 2 (by decide) (by decide +kernel)
  -- a point of `H` lies in all four kernels, any other point in exactly one
  have hpt : ∀ x : G, ((if form 0 1 0 x = 0 then 1 else 0) + (if form 0 0 1 x = 0 then 1 else 0) +
      (if form 0 1 1 x = 0 then 1 else 0) + (if form 0 1 2 x = 0 then 1 else 0) : ℕ) =
      1 + 3 * (if 3 • x = 0 then 1 else 0) := by
    decide +kernel
  simp only [cosetCount, card_filter] at e1 e2 e3 e4
  have hS : (D.filter (· ∈ H)).card = ∑ x ∈ D, if 3 • x = 0 then 1 else 0 := by
    rw [card_filter]; simp only [mem_H]
  have hsum := sum_congr rfl fun x (_ : x ∈ D) => hpt x
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, e1, e2, e3, e4, sum_add_distrib,
    ← mul_sum, sum_const, smul_eq_mul, mul_one, hD.1, ← hS] at hsum
  omega

/-- `|S ∩ (S + h)| ≡ 0 (mod 3)` for every nonzero `h ∈ H`, where `S = D ∩ H`. -/
theorem cond_S {D : Finset G} (hD : IsDiffSet D) (hF : Fixed D) (h : G) (hH : h ∈ H)
    (h0 : h ≠ 0) : diffCount (D.filter (· ∈ H)) h % 3 = 0 := by
  have h61 : (61 : ℕ) • h = h := (smul61_eq_self h).2 hH
  -- `σ × σ` permutes the pairs with difference `h`; its fixed pairs lie in `S × S`
  have hc := card_modEq_fixed (fun p : G × G => ((61 : ℕ) • p.1, (61 : ℕ) • p.2))
    (fun p => by simp only [smul61_cube]) ((D ×ˢ D).filter fun p => p.1 - p.2 = h)
    (fun p hp => by
      simp only [mem_filter, mem_product] at hp ⊢
      refine ⟨⟨hF _ hp.1.1, hF _ hp.1.2⟩, ?_⟩
      rw [← smul_sub, hp.2, h61])
  have hfix : (((D ×ˢ D).filter fun p => p.1 - p.2 = h).filter fun p =>
      ((61 : ℕ) • p.1, (61 : ℕ) • p.2) = p) =
      ((D.filter (· ∈ H)) ×ˢ (D.filter (· ∈ H))).filter fun p => p.1 - p.2 = h := by
    ext ⟨x, y⟩
    simp only [mem_filter, mem_product, Prod.mk.injEq, smul61_eq_self]
    tauto
  have hm : diffCount D h ≡ diffCount (D.filter (· ∈ H)) h [MOD 3] := by
    unfold diffCount; rw [← hfix]; exact hc
  rw [hD.2 h h0] at hm
  unfold Nat.ModEq at hm; omega

end DS243
