import DS243.SingletonData

/-!
# Classification of the singleton part `S = D ∩ H`

Elements of `H` are indexed `(x, 3u, 3w) ↦ 9x + 3u + w`, and a set's part in `H` becomes a
27-bit mask. The kernel checks a layered enumeration:

* layer 0 (`x = 0`) is moved to one of 14 representatives (`T0list`, check `K1`);
* layer 1 is sheared to one of 64 representatives (`T1list`, check `K2`);
* every 13-element mask with a representative layer 0, a representative layer 1 and the
  mod-3 autocorrelation condition is one of 12 survivors (`K3`);
* each survivor has a word mapping it to the frozen mask 24909666 (`K4`).

Result (`exists_word_mask`): if `|D ∩ H| = 13` and `|S ∩ (S + h)| ≡ 0 (mod 3)` for all
nonzero `h ∈ H`, some legal word maps `D ∩ H` onto the frozen singleton set.
-/

namespace DS243

open Finset

/-! ## Indexing `H` -/

/-- Index of an element of `H`: `(x, 3u, 3w) ↦ 9x + 3u + w`. -/
def hIndex (p : G) : ℕ := 9 * p.1.val + 3 * (p.2.1.val / 3) + p.2.2.val / 3

/-- The element of `H` with index `i`. -/
def hDec (i : ℕ) : G :=
  (((i / 9 : ℕ) : ZMod 3), ((3 * (i / 3 % 3) : ℕ) : ZMod 9), ((3 * (i % 3) : ℕ) : ZMod 9))

lemma hDec_spec : ∀ i, i < 27 → 3 • hDec i = 0 ∧ hIndex (hDec i) = i := by decide

set_option maxRecDepth 100000 in
lemma hIndex_spec : ∀ x : G, 3 • x = 0 → hIndex x < 27 ∧ hDec (hIndex x) = x := by
  decide +kernel

lemma hDec_mem {i : ℕ} (hi : i < 27) : hDec i ∈ H := mem_H.2 (hDec_spec i hi).1

lemma hIndex_lt {x : G} (hx : x ∈ H) : hIndex x < 27 := (hIndex_spec x (mem_H.1 hx)).1

lemma hDec_hIndex {x : G} (hx : x ∈ H) : hDec (hIndex x) = x := (hIndex_spec x (mem_H.1 hx)).2

lemma hIndex_hDec {i : ℕ} (hi : i < 27) : hIndex (hDec i) = i := (hDec_spec i hi).2

lemma testBit_sum_two_pow (s : Finset ℕ) (i : ℕ) : (∑ j ∈ s, 2 ^ j).testBit i ↔ i ∈ s := by
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, Finset.toFinset_bitIndices_sum_two_pow]

/-- The 27-bit mask of `D ∩ H`. -/
def maskOf (S : Finset G) : ℕ := ∑ i ∈ (S.filter (· ∈ H)).image hIndex, 2 ^ i

lemma testBit_maskOf (S : Finset G) (i : ℕ) :
    (maskOf S).testBit i ↔ i < 27 ∧ hDec i ∈ S := by
  rw [maskOf, testBit_sum_two_pow]
  simp only [mem_image, mem_filter]
  constructor
  · rintro ⟨x, ⟨hxS, hxH⟩, rfl⟩
    exact ⟨hIndex_lt hxH, by rwa [hDec_hIndex hxH]⟩
  · rintro ⟨hi, hS⟩
    exact ⟨hDec i, ⟨hS, hDec_mem hi⟩, hIndex_hDec hi⟩

lemma maskOf_lt (S : Finset G) : maskOf S < 2 ^ 27 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  have : ¬ (maskOf S).testBit i = true := by
    rw [testBit_maskOf]; omega
  simpa using this

/-- Masks below `2^27` agreeing on the first 27 bits are equal. -/
lemma eq_of_testBit_lt {m m' : ℕ} (hm : m < 2 ^ 27) (hm' : m' < 2 ^ 27)
    (h : ∀ j, j < 27 → m.testBit j = m'.testBit j) : m = m' := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 27
  · exact h j hj
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hm' (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-! ## Inverse words -/

/-- An inverse word for each generator. -/
def Gen.inv : Gen → Word
  | .transX => [.transX, .transX]
  | .transY => [.transY, .transY]
  | .transZ => [.transZ, .transZ]
  | .negX => [.negX]
  | .swapYZ => [.swapYZ]
  | .addYZ => [.addYZ, .addYZ, .addYZ, .addYZ, .addYZ, .addYZ, .addYZ, .addYZ]
  | .dblY => [.dblY, .dblY, .dblY, .dblY, .dblY]
  | .shearY => [.shearY, .shearY]
  | .shearZ => [.shearZ, .shearZ]
  | .bX => [.bX, .bX]
  | .cX => [.cX, .cX]

set_option maxRecDepth 100000 in
lemma Gen.inv_eval (s : Gen) : ∀ x : G, Word.eval s.inv (s.legal.toFun x) = x := by
  cases s <;> decide +kernel

/-- The inverse of a word. -/
def Word.inv : Word → Word
  | [] => []
  | s :: w => Word.inv w ++ s.inv

lemma Word.eval_append (w v : Word) (x : G) : (w ++ v).eval x = w.eval (v.eval x) := by
  induction w with
  | nil => rfl
  | cons s w ih => simp [Word.eval, ih]

lemma Word.inv_eval (w : Word) (x : G) : w.inv.eval (w.eval x) = x := by
  induction w with
  | nil => rfl
  | cons s w ih => simp [Word.inv, Word.eval, Word.eval_append, Gen.inv_eval, ih]

lemma Word.eval_inv (w : Word) (y : G) : w.eval (w.inv.eval y) = y := by
  obtain ⟨x, hx⟩ := w.legal.bij.2 (y - w.legal.τ)
  have hy : w.eval x = y := by
    rw [← Word.legal_toFun, Legal.toFun, hx, sub_add_cancel]
  rw [← hy, Word.inv_eval]

lemma Word.eval_mem_H_iff (w : Word) (x : G) : w.eval x ∈ H ↔ x ∈ H := by
  rw [← Word.legal_toFun, Legal.mem_H_iff]

/-- Index pulled back along a word: bit `j` of the image mask is bit `pullIdx w j` of the mask. -/
def pullIdx (w : Word) (j : ℕ) : ℕ := hIndex (w.inv.eval (hDec j))

lemma image_eval (w : Word) (S : Finset G) : S.image w.legal.toFun = S.image w.eval := by
  congr 1; funext x; exact Word.legal_toFun w x

lemma testBit_maskOf_image (w : Word) (S : Finset G) {j : ℕ} (hj : j < 27) :
    (maskOf (S.image w.legal.toFun)).testBit j = (maskOf S).testBit (pullIdx w j) := by
  have hy : w.inv.eval (hDec j) ∈ H := by
    rw [← Word.eval_mem_H_iff w, Word.eval_inv]; exact hDec_mem hj
  apply Bool.eq_iff_iff.2
  rw [testBit_maskOf, testBit_maskOf, image_eval, pullIdx, hDec_hIndex hy]
  simp only [mem_image]
  constructor
  · rintro ⟨_, x, hx, hxj⟩
    refine ⟨hIndex_lt hy, ?_⟩
    rw [← hxj, Word.inv_eval]; exact hx
  · rintro ⟨_, h⟩
    exact ⟨hj, _, h, Word.eval_inv w _⟩

/-! ## Counting on masks -/

/-- Number of set bits among the first 27. -/
def popc (m : ℕ) : ℕ := ((List.range 27).filter fun i => m.testBit i).length

/-- Index of `hDec i - hDec j`. -/
def hsub (i j : ℕ) : ℕ :=
  9 * ((i / 9 + 3 - j / 9) % 3) + 3 * ((i / 3 % 3 + 3 - j / 3 % 3) % 3) + (i % 3 + 3 - j % 3) % 3

lemma hsub_spec : ∀ i, i < 27 → ∀ j, j < 27 → hsub i j < 27 ∧ hDec (hsub i j) = hDec i - hDec j := by
  decide

/-- `|S ∩ (S + h)|` on masks, for `h` of index `j`. -/
def cnt (m j : ℕ) : ℕ := ((List.range 27).filter fun i => m.testBit i && m.testBit (hsub i j)).length

/-- The mod-3 autocorrelation condition on masks. -/
def condMask (m : ℕ) : Bool := (List.range 26).all fun j => cnt m (j + 1) % 3 == 0

lemma length_filter_range (p : ℕ → Bool) :
    ((List.range 27).filter p).length = ((Finset.range 27).filter fun i => p i = true).card := by
  simp [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe]

lemma hIndex_injOn : Set.InjOn hIndex (H : Set G) := by
  intro x hx y hy h
  rw [← hDec_hIndex (Finset.mem_coe.1 hx), ← hDec_hIndex (Finset.mem_coe.1 hy), h]

lemma card_image_hIndex (T : Finset G) (hT : ∀ x ∈ T, x ∈ H) :
    (T.image hIndex).card = T.card :=
  card_image_of_injOn fun x hx y hy h => hIndex_injOn (hT x hx) (hT y hy) h

lemma card_inter_H_eq_popc (S : Finset G) : (S.filter (· ∈ H)).card = popc (maskOf S) := by
  rw [popc, length_filter_range, ← card_image_hIndex _ (fun x hx => (mem_filter.1 hx).2)]
  congr 1
  ext i
  simp only [mem_filter, mem_range, mem_image, testBit_maskOf]
  constructor
  · rintro ⟨x, ⟨hxS, hxH⟩, rfl⟩
    exact ⟨hIndex_lt hxH, hIndex_lt hxH, by rwa [hDec_hIndex hxH]⟩
  · rintro ⟨hi, -, hS⟩
    exact ⟨hDec i, ⟨hS, hDec_mem hi⟩, hIndex_hDec hi⟩

lemma diffCount_inter_H (S : Finset G) {j : ℕ} (hj : j < 27) :
    diffCount (S.filter (· ∈ H)) (hDec j) = cnt (maskOf S) j := by
  rw [diffCount_eq_card_filter, cnt, length_filter_range,
    ← card_image_hIndex _ (fun x hx => (mem_filter.1 (mem_filter.1 hx).1).2)]
  congr 1
  ext i
  simp only [mem_filter, mem_range, mem_image, Bool.and_eq_true, testBit_maskOf]
  constructor
  · rintro ⟨x, ⟨⟨hxS, hxH⟩, hxh, -⟩, rfl⟩
    have hi := hIndex_lt hxH
    obtain ⟨hs, hsd⟩ := hsub_spec _ hi j hj
    refine ⟨hi, ⟨hi, by rwa [hDec_hIndex hxH]⟩, hs, ?_⟩
    rw [hsd, hDec_hIndex hxH]; exact hxh
  · rintro ⟨hi, ⟨-, hS⟩, -, hS'⟩
    obtain ⟨hs, hsd⟩ := hsub_spec _ hi j hj
    refine ⟨hDec i, ⟨⟨hS, hDec_mem hi⟩, ?_, ?_⟩, hIndex_hDec hi⟩
    · rw [← hsd]; exact hS'
    · rw [← hsd]; exact hDec_mem hs

/-- The mod-3 condition on `D ∩ H` gives the mask condition. -/
lemma condMask_maskOf (S : Finset G)
    (hcond : ∀ h ∈ H, h ≠ 0 → diffCount (S.filter (· ∈ H)) h % 3 = 0) :
    condMask (maskOf S) = true := by
  rw [condMask, List.all_eq_true]
  intro j hj
  rw [List.mem_range] at hj
  have hj' : j + 1 < 27 := by omega
  rw [← diffCount_inter_H S hj']
  have hne : hDec (j + 1) ≠ 0 := by
    intro h
    have := hIndex_hDec hj'
    rw [h] at this
    simp [hIndex] at this
  simpa using hcond _ (hDec_mem hj') hne

/-! ## The kernel checks -/

/-- Word of `T0list` for layer-0 mask `m`. -/
def T0 (m : ℕ) : Word := T0list.getD m []

/-- Word of `T1list` for layer-1 mask `c`. -/
def T1 (c : ℕ) : Word := T1list.getD c []

/-- The 9-bit mask whose bit `j` is bit `pullIdx w (o + j) - o` of `m`. -/
def img9 (w : Word) (o m : ℕ) : ℕ :=
  ∑ j ∈ (Finset.range 9).filter (fun j => m.testBit (pullIdx w (o + j) - o) = true), 2 ^ j

/-- The frozen singleton mask (see `checks/campaign.cpp`). -/
def MASK : ℕ := 24909666

/-! ## The frozen singleton set -/

/-- The frozen singleton set: elements of `H` whose index bit is set in `MASK`. -/
def MaskSet : Finset G := ((Finset.range 27).filter fun i => MASK.testBit i = true).image hDec

lemma hDec_inj {i j : ℕ} (hi : i < 27) (hj : j < 27) (h : hDec i = hDec j) : i = j := by
  rw [← hIndex_hDec hi, ← hIndex_hDec hj, h]

lemma MaskSet_sub_H {x : G} (hx : x ∈ MaskSet) : x ∈ H := by
  obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
  exact hDec_mem (mem_range.1 (mem_filter.1 hi).1)

lemma hDec_mem_MaskSet {j : ℕ} (hj : j < 27) : hDec j ∈ MaskSet ↔ MASK.testBit j = true := by
  simp only [MaskSet, mem_image, mem_filter, mem_range]
  constructor
  · rintro ⟨i, ⟨hi, hb⟩, he⟩
    rwa [← hDec_inj hi hj he]
  · intro hb; exact ⟨j, ⟨hj, hb⟩, rfl⟩

lemma maskOf_MaskSet : maskOf MaskSet = MASK := by
  apply eq_of_testBit_lt (maskOf_lt _) (by norm_num [MASK])
  intro j hj
  apply Bool.eq_iff_iff.2
  rw [testBit_maskOf, hDec_mem_MaskSet hj]
  simp [hj]

/-- A set whose mask is `MASK` meets `H` exactly in `MaskSet`. -/
lemma inter_H_eq_of_maskOf {D : Finset G} (h : maskOf D = MASK) :
    D.filter (· ∈ H) = MaskSet := by
  ext x
  rw [mem_filter]
  by_cases hx : x ∈ H
  · have hi := hIndex_lt hx
    have key := testBit_maskOf D (hIndex x)
    rw [hDec_hIndex hx, h] at key
    rw [← hDec_hIndex hx, hDec_mem_MaskSet hi, hDec_hIndex hx]
    simp only [hx, and_true]
    rw [key]; simp [hi]
  · exact ⟨fun h' => absurd h'.2 hx, fun h' => absurd (MaskSet_sub_H h') hx⟩

end DS243
