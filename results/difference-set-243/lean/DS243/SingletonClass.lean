import DS243.SingletonChecks

/-!
# The singleton classification

`exists_word_mask`: a set with `|D ∩ H| = 13` and `|S ∩ (S + h)| ≡ 0 (mod 3)` for every nonzero
`h ∈ H` (where `S = D ∩ H`) is moved by a legal word onto the frozen singleton set. The proof
chains the kernel checks K1 (layer 0), K2 (layer 1), K3 (enumeration) and K4 (survivors).
-/

namespace DS243

open Finset

/-- The mod-3 autocorrelation condition on `D ∩ H`. -/
def CondH (D : Finset G) : Prop := ∀ h ∈ H, h ≠ 0 → diffCount (D.filter (· ∈ H)) h % 3 = 0

lemma Legal.lin_mem_H_iff (L : Legal) (g : G) : L.lin g ∈ H ↔ g ∈ H := by
  rw [mem_H, mem_H, ← map_nsmul]
  constructor
  · intro h; exact L.bij.1 (h.trans (map_zero _).symm)
  · intro h; rw [h, map_zero]

lemma CondH.image {D : Finset G} (hD : CondH D) (L : Legal) : CondH (D.image L.toFun) := by
  intro h hH h0
  obtain ⟨g, rfl⟩ := L.bij.2 h
  rw [Legal.image_inter_H, Legal.diffCount_image]
  refine hD g ((L.lin_mem_H_iff g).1 hH) ?_
  rintro rfl; exact h0 (map_zero _)

lemma cardH_image (D : Finset G) (L : Legal) :
    ((D.image L.toFun).filter (· ∈ H)).card = (D.filter (· ∈ H)).card := by
  rw [Legal.image_inter_H, Legal.image_card]

lemma testBit_img9 (w : Word) (o m j : ℕ) :
    (img9 w o m).testBit j ↔ j < 9 ∧ m.testBit (pullIdx w (o + j) - o) = true := by
  rw [img9, testBit_sum_two_pow]; simp

/-- Numbers below `2^9` agreeing on the first nine bits are equal. -/
lemma eq_of_testBit_lt9 {a b : ℕ} (ha : a < 2 ^ 9) (hb : b < 2 ^ 9)
    (h : ∀ j, j < 9 → a.testBit j = b.testBit j) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 9
  · exact h j hj
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))]

lemma img9_lt (w : Word) (o m : ℕ) : img9 w o m < 2 ^ 9 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  have : ¬ (img9 w o m).testBit i = true := by rw [testBit_img9]; omega
  simpa using this

lemma maskOf_image_eval (w : Word) (D : Finset G) :
    maskOf (D.image w.legal.toFun) = maskOf (D.image w.eval) := by rw [image_eval]

lemma length_filter_map_add (k : ℕ) (l : List ℕ) (p : ℕ → Bool) :
    ((l.map (k + ·)).filter p).length = (l.filter fun i => p (k + i)).length := by
  rw [List.filter_map, List.length_map]; rfl

/-- The popcount of a 27-bit mask splits over its three 9-bit layers. -/
lemma popc_split (m : ℕ) :
    popc m = popc9 (m % 512) + popc9 (m / 512 % 512) + popc9 (m / 262144 % 512) := by
  have h27 : List.range 27 = List.range 9 ++ ((List.range 9).map (9 + ·) ++
      (List.range 9).map (18 + ·)) := by decide
  rw [popc, h27, List.filter_append, List.filter_append, List.length_append, List.length_append,
    length_filter_map_add, length_filter_map_add, popc9, popc9, popc9, add_assoc]
  have e : ∀ (o : ℕ) (f : ℕ → ℕ), (∀ i, i < 9 → m.testBit (o + i) = (f m).testBit i) →
      ((List.range 9).filter fun i => m.testBit (o + i)).length =
        ((List.range 9).filter fun i => (f m).testBit i).length := by
    intro o f h
    congr 1
    apply List.filter_congr
    intro i hi
    exact h i (List.mem_range.1 hi)
  have h0 := e 0 (fun m => m % 512) (fun i hi => by
    rw [show (512 : ℕ) = 2 ^ 9 by norm_num, Nat.testBit_mod_two_pow]; simp [hi])
  have h1 := e 9 (fun m => m / 512 % 512) (fun i hi => by
    rw [show (512 : ℕ) = 2 ^ 9 by norm_num, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    simp [hi, Nat.add_comm])
  have h2 := e 18 (fun m => m / 262144 % 512) (fun i hi => by
    rw [show (512 : ℕ) = 2 ^ 9 by norm_num, show (262144 : ℕ) = 2 ^ 18 by norm_num,
      Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    simp [hi, Nat.add_comm])
  simp only [zero_add] at h0
  rw [h0, h1, h2]

lemma mem_byPop {n : ℕ} (hn : n < 512) : n ∈ byPop (popc9 n) := by
  simp [byPop, hn]

lemma popc9_le (n : ℕ) : popc9 n ≤ 9 := by
  have := List.length_filter_le (fun i => n.testBit i) (List.range 9)
  simpa [popc9] using this

lemma tb_mod512 (x j : ℕ) : (x % 512).testBit j = (decide (j < 9) && x.testBit j) := by
  rw [show (512 : ℕ) = 2 ^ 9 by norm_num, Nat.testBit_mod_two_pow]

lemma tb_div512 (x j : ℕ) : (x / 512).testBit j = x.testBit (j + 9) := by
  rw [show (512 : ℕ) = 2 ^ 9 by norm_num, Nat.testBit_div_two_pow]

lemma eq_of_testBit_512 {a b : ℕ} (ha : a < 512) (hb : b < 512)
    (h : ∀ j, j < 9 → a.testBit j = b.testBit j) : a = b :=
  eq_of_testBit_lt9 (by simpa using ha) (by simpa using hb) h

/-- The singleton classification: some legal word maps `D ∩ H` onto `MaskSet`. -/
theorem exists_word_mask {D : Finset G} (hcard : (D.filter (· ∈ H)).card = 13)
    (hcond : ∀ h ∈ H, h ≠ 0 → diffCount (D.filter (· ∈ H)) h % 3 = 0) :
    ∃ w : Word, (D.image w.legal.toFun).filter (· ∈ H) = MaskSet := by
  -- Step 1: layer 0.
  obtain ⟨m, hm⟩ : ∃ m, m = maskOf D := ⟨_, rfl⟩
  obtain ⟨w0, hw0⟩ : ∃ w0, w0 = T0 (m % 512) := ⟨_, rfl⟩
  obtain ⟨hrep, hpull0⟩ := K1 (m % 512) (Nat.mod_lt _ (by norm_num))
  rw [← hw0] at hrep hpull0
  obtain ⟨D1, hD1⟩ : ∃ D1, D1 = D.image w0.legal.toFun := ⟨_, rfl⟩
  have hA : maskOf D1 % 512 = img9 w0 0 (m % 512) := by
    have h9 := img9_lt w0 0 (m % 512)
    apply eq_of_testBit_512 (Nat.mod_lt _ (by norm_num)) (by simpa using h9)
    intro j hj
    have hp := hpull0 j hj
    rw [tb_mod512, hD1, testBit_maskOf_image w0 D (by omega)]
    apply Bool.eq_iff_iff.2
    rw [testBit_img9, tb_mod512, ← hm]
    simp [hj, hp]
  -- Step 2: layer 1.
  obtain ⟨c, hc⟩ : ∃ c, c = maskOf D1 / 512 % 512 := ⟨_, rfl⟩
  obtain ⟨w1, hw1⟩ : ∃ w1, w1 = T1 c := ⟨_, rfl⟩
  obtain ⟨hcan, hpull1⟩ := K2 c (by omega)
  rw [← hw1] at hcan hpull1
  obtain ⟨D2, hD2⟩ : ∃ D2, D2 = D1.image w1.legal.toFun := ⟨_, rfl⟩
  have hB : maskOf D2 % 512 = maskOf D1 % 512 := by
    apply eq_of_testBit_512 (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    intro j hj
    rw [tb_mod512, tb_mod512, hD2, testBit_maskOf_image w1 D1 (by omega), (hpull1 j hj).1]
  have hC : maskOf D2 / 512 % 512 = img9 w1 9 c := by
    have h9 := img9_lt w1 9 c
    apply eq_of_testBit_512 (Nat.mod_lt _ (by norm_num)) (by simpa using h9)
    intro j hj
    obtain ⟨-, h9, h18⟩ := hpull1 j hj
    rw [tb_mod512, tb_div512, show j + 9 = 9 + j by omega, hD2,
      testBit_maskOf_image w1 D1 (by omega)]
    apply Bool.eq_iff_iff.2
    rw [testBit_img9, hc, tb_mod512, tb_div512,
      show pullIdx w1 (9 + j) - 9 + 9 = pullIdx w1 (9 + j) by omega]
    simp [hj, show pullIdx w1 (9 + j) - 9 < 9 by omega]
  -- Step 3: enumeration.
  obtain ⟨normalized_mask, hm2⟩ : ∃ normalized_mask, normalized_mask = maskOf D2 := ⟨_, rfl⟩
  have hm2lt : normalized_mask < 2 ^ 27 := hm2 ▸ maskOf_lt D2
  have hsplit : normalized_mask = normalized_mask % 512 + 512 * (normalized_mask / 512 % 512) + 262144 * (normalized_mask / 262144) := by omega
  have hn : normalized_mask / 262144 < 512 := by omega
  have hcondD2 : CondH D2 := by
    rw [hD2, hD1]; exact CondH.image (CondH.image hcond _) _
  have hcardD2 : (D2.filter (· ∈ H)).card = 13 := by
    rw [hD2, hD1, cardH_image, cardH_image, hcard]
  have hpop : popc normalized_mask = 13 := by rw [hm2, ← card_inter_H_eq_popc, hcardD2]
  have hcm : condMask normalized_mask = true := hm2 ▸ condMask_maskOf D2 hcondD2
  have hr : normalized_mask % 512 ∈ reps := by rw [hm2, hB, hA]; exact hrep
  have hcc : normalized_mask / 512 % 512 ∈ canon := by rw [hm2, hC]; exact hcan
  have hps := popc_split normalized_mask
  rw [hpop, show normalized_mask / 262144 % 512 = normalized_mask / 262144 by omega] at hps
  have hn9 := popc9_le (normalized_mask / 262144)
  have hsurv := K3 _ hr _ hcc (by omega) (normalized_mask / 262144)
    (by rw [show 13 - popc9 (normalized_mask % 512) - popc9 (normalized_mask / 512 % 512) = popc9 (normalized_mask / 262144) by omega]
        exact mem_byPop hn)
    (by rw [← hsplit]; exact hcm)
  rw [← hsplit, List.mem_map] at hsurv
  obtain ⟨p, hp, hpm⟩ := hsurv
  -- Step 4: the survivor's word.
  have hK4 := K4 p hp
  have hD3 : maskOf (D2.image p.2.legal.toFun) = MASK := by
    apply eq_of_testBit_lt (maskOf_lt _) (by norm_num [MASK])
    intro j hj
    rw [testBit_maskOf_image _ _ hj, hK4 j hj, hpm, hm2]
  refine ⟨p.2 ++ w1 ++ w0, ?_⟩
  have : D.image (p.2 ++ w1 ++ w0).legal.toFun = D2.image p.2.legal.toFun := by
    rw [hD2, hD1]
    simp only [image_eval, image_image]
    congr 1; funext x; simp [Function.comp, Word.eval_append, Word.legal_toFun]
  rw [this]
  exact inter_H_eq_of_maskOf hD3

end DS243
