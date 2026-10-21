import DS243.QuotientData
import DS243.Lifting

/-!
# The quotient image of a normalized fixed difference set

Let `D` be a fixed (243,121,60) difference set meeting `H` in the frozen singleton set.
Its cell counts `r(q) = |D ∩ (cell q)|` on `Q = G / 3G` have special values `(4, 3, 6)` on the
cells `(x, 0, 0)`, are multiples of three at most nine elsewhere, and every one of the 13 forms
has line sums `40` at zero and `{36, 45}` elsewhere. The identity
`∑_L t_L(L q) = 4 · 121 + 9 r(q)` recovers `r` from the 2^13 sign choices, leaving the 144 images
of `imageTable`. A word from the table fixes the singleton set and maps the image to a frozen
case row.
-/

namespace DS243

open Finset

/-- The action of a word on cells. -/
def qfwd (w : Word) (q : ZMod 3 × ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 × ZMod 3 :=
  cell (w.eval (q.1, (q.2.1.val : ZMod 9), (q.2.2.val : ZMod 9)))

/-! ## Linear forms on cells -/

/-- The linear form `f` on a cell. -/
def qform (f q : ZMod 3 × ZMod 3 × ZMod 3) : ZMod 3 := f.1 * q.1 + f.2.1 * q.2.1 + f.2.2 * q.2.2

/-- The `k`-th form of `forms`. -/
def qF (k : ℕ) : ZMod 3 × ZMod 3 × ZMod 3 := forms.getD k 0

/-- Cell index `9x + 3u + w`. -/
def qIdx (q : ZMod 3 × ZMod 3 × ZMod 3) : ℕ := 9 * q.1.val + 3 * q.2.1.val + q.2.2.val

/-- The representative point of a cell used by `qfwd`. -/
def qrep (q : ZMod 3 × ZMod 3 × ZMod 3) : G := (q.1, (q.2.1.val : ZMod 9), (q.2.2.val : ZMod 9))

lemma cosetCount_eq_sum (D : Finset G) (f : ZMod 3 × ZMod 3 × ZMod 3) (i : ZMod 3) :
    cosetCount D f.1 f.2.1 f.2.2 i =
      ∑ q ∈ univ.filter (fun q => qform f q = i), cellCount D q := by
  unfold cosetCount
  rw [card_eq_sum_card_fiberwise (f := cell) (t := univ.filter (fun q => qform f q = i))]
  · refine sum_congr rfl fun q hq => ?_
    unfold cellCount
    rw [filter_filter]
    congr 1
    refine filter_congr fun x _ => ?_
    simp only [mem_filter, mem_univ, true_and] at hq
    constructor
    · exact fun h => h.2
    · intro h; refine ⟨?_, h⟩; rw [← hq, ← h]; rfl
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
    exact hx.2

set_option maxRecDepth 100000 in
lemma qcount : ∀ q q' : ZMod 3 × ZMod 3 × ZMod 3,
    ((range 13).filter fun k => qform (qF k) q' = qform (qF k) q).card =
      if q' = q then 13 else 4 := by
  decide +kernel

/-- Inversion: the 13 line sums through `q` determine `r q`. -/
lemma qinv (r : ZMod 3 × ZMod 3 × ZMod 3 → ℕ) (q : ZMod 3 × ZMod 3 × ZMod 3) :
    ∑ k ∈ range 13, ∑ q' ∈ univ.filter (fun q' => qform (qF k) q' = qform (qF k) q), r q' =
      9 * r q + 4 * ∑ q', r q' := by
  simp_rw [sum_filter]
  rw [sum_comm]
  have h : ∀ q', (∑ k ∈ range 13, if qform (qF k) q' = qform (qF k) q then r q' else 0) =
      4 * r q' + if q' = q then 9 * r q' else 0 := by
    intro q'
    rw [← sum_filter, sum_const, smul_eq_mul, qcount]
    split_ifs <;> ring
  rw [sum_congr rfl fun q' _ => h q', sum_add_distrib, ← mul_sum, sum_ite_eq']
  simp only [mem_univ, if_true]
  ring

lemma exists_bits (β : ℕ → Bool) : ∀ n, ∃ s, s < 2 ^ n ∧ ∀ k, k < n → s.testBit k = β k := by
  intro n
  induction n generalizing β with
  | zero => exact ⟨0, by norm_num, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨s, hs, hb⟩ := ih (fun k => β (k + 1))
    have hb0 := Bool.toNat_le (β 0)
    refine ⟨(β 0).toNat + 2 * s, by rw [pow_succ]; omega, ?_⟩
    intro k hk
    cases k with
    | zero =>
      rw [Nat.testBit_zero]
      cases β 0 <;> simp
    | succ k =>
      rw [Nat.testBit_succ, show ((β 0).toNat + 2 * s) / 2 = s by omega]
      exact hb k (by omega)

lemma list_sum_range (g : ℕ → ℕ) (n : ℕ) : ((List.range n).map g).sum = ∑ k ∈ range n, g k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

lemma all_range' (p : ℕ → Bool) (lo n : ℕ) (h : (List.range' lo n).all p = true) :
    ∀ s, lo ≤ s → s < lo + n → p s = true := by
  intro s h1 h2
  rw [List.all_eq_true] at h
  exact h s (List.mem_range'_1.2 ⟨h1, h2⟩)

/-! ## The sign-vector check -/

/-- The forms of `forms`, as natural numbers. -/
def qformsN : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 1), (0, 1, 0), (0, 1, 1), (0, 1, 2), (1, 0, 0), (1, 0, 1), (1, 0, 2), (1, 1, 0),
   (1, 1, 1), (1, 1, 2), (1, 2, 0), (1, 2, 1), (1, 2, 2)]

/-- Value of form `k` at the cell with index `j`. -/
def qfN (k j : ℕ) : ℕ :=
  let f := qformsN.getD k (0, 0, 0)
  (f.1 * (j / 9) + f.2.1 * (j / 3 % 3) + f.2.2 * (j % 3)) % 3

/-- Line sum of form `k` at value `i` for sign vector `s`: `40` at zero, `{36, 45}` elsewhere. -/
def qT (s k i : ℕ) : ℕ := if i = 0 then 40 else if (s.testBit k == (i == 1)) = true then 45 else 36

/-- `∑_k t_k(f_k q)` at the cell with index `j`. -/
def qS (s j : ℕ) : ℕ := ((List.range 13).map fun k => qT s k (qfN k j)).sum

/-- The recovered cell count. -/
def qR (s j : ℕ) : ℕ := (qS s j - 484) / 9

/-- Special cell values. -/
def qSpec (j : ℕ) : ℕ := if j = 0 then 4 else if j = 9 then 3 else 6

/-- Validity of the recovered count at cell `j`. -/
def qOk (s j : ℕ) : Prop :=
  484 ≤ qS s j ∧ (qS s j - 484) % 9 = 0 ∧ qR s j ≤ 9 ∧ (j % 9 = 0 → qR s j = qSpec j) ∧
    (j % 9 ≠ 0 → qR s j % 3 = 0)

instance (s j : ℕ) : Decidable (qOk s j) := by unfold qOk; infer_instance

/-- All 27 recovered counts are valid. -/
def qValid (s : ℕ) : Bool := (List.range 27).all fun j => decide (qOk s j)

/-- The recovered image. -/
def qImg (s : ℕ) : List ℕ := (List.range 27).map (qR s)

/-- A valid sign vector yields an image in `imageTable`. -/
def qGood (s : ℕ) : Bool := !qValid s || imageTable.any fun e => decide (e.1 = qImg s)

set_option maxRecDepth 100000 in
lemma qGood_0 : (List.range' (512 * 0) 512).all qGood = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma qGood_1 : (List.range' (512 * 1) 512).all qGood = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma qGood_2 : (List.range' (512 * 2) 512).all qGood = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma qGood_3 : (List.range' (512 * 3) 512).all qGood = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma qGood_4 : (List.range' (512 * 4) 512).all qGood = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma qGood_5 : (List.range' (512 * 5) 512).all qGood = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma qGood_6 : (List.range' (512 * 6) 512).all qGood = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma qGood_7 : (List.range' (512 * 7) 512).all qGood = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma qGood_8 : (List.range' (512 * 8) 512).all qGood = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma qGood_9 : (List.range' (512 * 9) 512).all qGood = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma qGood_10 : (List.range' (512 * 10) 512).all qGood = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma qGood_11 : (List.range' (512 * 11) 512).all qGood = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma qGood_12 : (List.range' (512 * 12) 512).all qGood = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma qGood_13 : (List.range' (512 * 13) 512).all qGood = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma qGood_14 : (List.range' (512 * 14) 512).all qGood = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma qGood_15 : (List.range' (512 * 15) 512).all qGood = true := by decide +kernel

lemma qGood_all (s : ℕ) (hs : s < 8192) : qGood s = true := by
  have key : ∀ i, i < 16 → (List.range' (512 * i) 512).all qGood = true := by
    intro i hi
    interval_cases i
    exacts [qGood_0, qGood_1, qGood_2, qGood_3, qGood_4, qGood_5, qGood_6, qGood_7, qGood_8,
      qGood_9, qGood_10, qGood_11, qGood_12, qGood_13, qGood_14, qGood_15]
  exact all_range' _ _ _ (key (s / 512) (by omega)) s (by omega) (by omega)

/-! ## The table check -/

/-- An entry's case is frozen, its word fixes `MASK`, and it maps the image onto the case row. -/
def qEntryOk (e : List ℕ × Word × ℕ) : Bool :=
  decide (e.2.2 < 8) &&
    (List.range 27).all (fun j => MASK.testBit (pullIdx e.2.1 j) == MASK.testBit j) &&
    (List.range 27).all (fun j => caseCoef e.2.2 (qIdx (qfwd e.2.1 (qOf j))) == e.1.getD j 0)

/-- `qEntryOk` at a table position. -/
def qEntryAt (i : ℕ) : Bool := qEntryOk (imageTable.getD i ([], [], 0))

set_option maxRecDepth 100000 in
lemma qEntry_0 : (List.range' (36 * 0) 36).all qEntryAt = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma qEntry_1 : (List.range' (36 * 1) 36).all qEntryAt = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma qEntry_2 : (List.range' (36 * 2) 36).all qEntryAt = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma qEntry_3 : (List.range' (36 * 3) 36).all qEntryAt = true := by decide +kernel

lemma qEntry_all (e : List ℕ × Word × ℕ) (he : e ∈ imageTable) : qEntryOk e = true := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  have hlen : imageTable.length = 144 := by rfl
  have key : ∀ c, c < 4 → (List.range' (36 * c) 36).all qEntryAt = true := by
    intro c hc
    interval_cases c
    exacts [qEntry_0, qEntry_1, qEntry_2, qEntry_3]
  have := all_range' _ _ _ (key (i / 36) (by omega)) i (by omega) (by omega)
  rwa [qEntryAt, List.getD_eq_getElem _ _ hi] at this

/-! ## Finite facts -/

set_option maxRecDepth 100000 in
lemma qfN_spec : ∀ k, k < 13 → ∀ q, (qform (qF k) q).val = qfN k (qIdx q) := by
  decide +kernel

lemma qF_ne : ∀ k, k < 13 → ((qF k).1, (qF k).2.1, (qF k).2.2) ≠ (0, 0, 0) := by decide

set_option maxRecDepth 100000 in
lemma qF_mask : ∀ k, k < 13 → cosetCount MaskSet (qF k).1 (qF k).2.1 (qF k).2.2 0 % 3 = 1 := by
  decide +kernel

lemma qOf_qIdx : ∀ q, qOf (qIdx q) = q := by decide

lemma qIdx_lt : ∀ q, qIdx q < 27 := by decide

lemma qIdx_special : ∀ q, qIdx q % 9 = 0 → q.2 = (0, 0) := by decide

lemma cell_qrep : ∀ q, cell (qrep q) = q := by decide

set_option maxRecDepth 100000 in
lemma cell_card : ∀ q, (univ.filter fun x : G => cell x = q).card = 9 := by decide +kernel

set_option maxRecDepth 100000 in
lemma mask_cell : ∀ q, cellCount MaskSet q =
    if qIdx q = 0 then 4 else if qIdx q = 9 then 3 else if qIdx q = 18 then 6 else 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma special_H : ∀ x : G, (cell x).2 = (0, 0) → 3 • x = 0 := by decide +kernel

lemma cellCount_special (D : Finset G) (q : ZMod 3 × ZMod 3 × ZMod 3) (hq : q.2 = (0, 0)) :
    cellCount D q = cellCount (D.filter (· ∈ H)) q := by
  unfold cellCount
  rw [filter_filter]
  congr 1
  refine filter_congr fun x _ => ?_
  constructor
  · intro h; exact ⟨mem_H.2 (special_H x (by rw [h]; exact hq)), h⟩
  · exact fun h => h.2

lemma cellCount_le (D : Finset G) (q : ZMod 3 × ZMod 3 × ZMod 3) : cellCount D q ≤ 9 := by
  rw [← cell_card q]
  exact card_le_card (filter_subset_filter _ (subset_univ D))

/-! ## Cell transport -/

lemma cell_eval (w : Word) (x : G) : cell (w.eval x) = qfwd w (cell x) := by
  change cell (w.eval x) = cell (w.eval (qrep (cell x)))
  rw [← Word.legal_toFun, ← Word.legal_toFun]
  exact Legal.cell_congr _ (cell_qrep (cell x)).symm

lemma qfwd_inv (w : Word) (q : ZMod 3 × ZMod 3 × ZMod 3) : qfwd w.inv (qfwd w q) = q := by
  change qfwd w.inv (cell (w.eval (qrep q))) = q
  rw [← cell_eval, Word.inv_eval, cell_qrep]

lemma qfwd_inj (w : Word) : Function.Injective (qfwd w) := fun a b h => by
  rw [← qfwd_inv w a, h, qfwd_inv]

lemma cellCount_image (w : Word) (D : Finset G) (q : ZMod 3 × ZMod 3 × ZMod 3) :
    cellCount (D.image w.legal.toFun) (qfwd w q) = cellCount D q := by
  unfold cellCount
  rw [show (D.image w.legal.toFun).filter (fun x => cell x = qfwd w q) =
      (D.filter fun x => cell x = q).image w.legal.toFun from ?_]
  · exact card_image_of_injective _ w.legal.injective
  ext y
  simp only [mem_filter, mem_image]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hc⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    rw [Word.legal_toFun, cell_eval] at hc
    exact qfwd_inj w hc
  · rintro ⟨x, ⟨hx, hc⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by rw [Word.legal_toFun, cell_eval, hc]⟩

/-- Normalization of the quotient image: some word keeps the frozen singleton set and moves the
cell counts onto a frozen case row. -/
theorem quotient_normal {D : Finset G} (hD : IsDiffSet D) (hF : Fixed D)
    (hS : D.filter (· ∈ H) = MaskSet) :
    ∃ w : Word, ∃ c, c < 8 ∧ (D.image w.legal.toFun).filter (· ∈ H) = MaskSet ∧
      ∀ q, cellCount (D.image w.legal.toFun) q = caseCount c q := by
  -- line sums of the 13 forms
  have hT : ∀ k, k < 13 → cosetCount D (qF k).1 (qF k).2.1 (qF k).2.2 0 = 40 ∧
      ((cosetCount D (qF k).1 (qF k).2.1 (qF k).2.2 1 = 36 ∧
        cosetCount D (qF k).1 (qF k).2.1 (qF k).2.2 2 = 45) ∨
       (cosetCount D (qF k).1 (qF k).2.1 (qF k).2.2 1 = 45 ∧
        cosetCount D (qF k).1 (qF k).2.1 (qF k).2.2 2 = 36)) := by
    intro k hk
    have h3 := cosetCount_modEq hF (qF k).1 (qF k).2.1 (qF k).2.2 0
    rw [hS] at h3
    have hm := qF_mask k hk
    unfold Nat.ModEq at h3
    rcases triple_cases _ _ _ (coset_sum hD _ _ _) (coset_sq_sum hD _ _ _ (qF_ne k hk)) with
      h | h | h | h | h | h <;> omega
  -- the sign vector
  obtain ⟨s, hs, hbits⟩ := exists_bits
    (fun k => decide (cosetCount D (qF k).1 (qF k).2.1 (qF k).2.2 1 = 45)) 13
  have hTs : ∀ k, k < 13 → ∀ i : ZMod 3,
      cosetCount D (qF k).1 (qF k).2.1 (qF k).2.2 i = qT s k i.val := by
    intro k hk i
    have hb := hbits k hk
    obtain ⟨h0, h12⟩ := hT k hk
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide
    rcases h12 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] at hb <;> simp at hb <;>
      rcases hi with rfl | rfl | rfl <;> simp [qT, hb, h0, h1, h2] <;> rfl
  have hcard : ∑ q, cellCount D q = 121 := by
    rw [← hD.1, card_eq_sum_card_fiberwise (f := cell) (t := univ) (fun _ _ => mem_univ _)]; rfl
  have hS9 : ∀ q, 9 * cellCount D q + 484 = qS s (qIdx q) := by
    intro q
    have := qinv (cellCount D) q
    rw [hcard] at this
    rw [qS, list_sum_range, show 9 * cellCount D q + 484 = 9 * cellCount D q + 4 * 121 by norm_num,
      ← this]
    refine sum_congr rfl fun k hk => ?_
    have hk' := mem_range.1 hk
    rw [← cosetCount_eq_sum, hTs k hk', qfN_spec k hk' q]
  -- `s` is a valid sign vector
  have hval : qValid s = true := by
    unfold qValid
    rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    apply decide_eq_true
    have hq : qIdx (qOf j) = j := qOf_idx j hj
    have e := hS9 (qOf j)
    rw [hq] at e
    have hle := cellCount_le D (qOf j)
    have hR : qR s j = cellCount D (qOf j) := by unfold qR; omega
    refine ⟨by omega, by omega, by omega, fun h9 => ?_, fun h9 => ?_⟩
    · rw [hR, cellCount_special D _ (qIdx_special _ (by rw [hq]; exact h9)), hS, mask_cell, hq]
      unfold qSpec
      split_ifs <;> omega
    · rw [hR]
      have hm := cellCount_modEq hF (qOf j)
      rw [hS, mask_cell, hq] at hm
      unfold Nat.ModEq at hm
      split_ifs at hm <;> omega
  -- the image is in the table
  have hg := qGood_all s hs
  unfold qGood at hg
  rw [hval] at hg
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true, decide_eq_true_eq] at hg
  obtain ⟨e, he, heq⟩ := hg
  have hok := qEntry_all e he
  simp only [qEntryOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq] at hok
  obtain ⟨⟨hc8, hmask⟩, hcase⟩ := hok
  have hmaskD : maskOf D = MASK := by
    rw [← maskOf_MaskSet]
    unfold maskOf
    rw [hS, filter_true_of_mem fun x hx => MaskSet_sub_H hx]
  refine ⟨e.2.1, e.2.2, hc8, ?_, ?_⟩
  · apply inter_H_eq_of_maskOf
    apply eq_of_testBit_lt (maskOf_lt _) (by norm_num [MASK])
    intro j hj
    rw [testBit_maskOf_image _ _ hj, hmaskD]
    exact hmask j hj
  · intro q'
    obtain ⟨q, rfl⟩ := Finite.surjective_of_injective (qfwd_inj e.2.1) q'
    rw [cellCount_image]
    have h1 := hcase (qIdx q) (qIdx_lt q)
    rw [qOf_qIdx] at h1
    change _ = caseCoef e.2.2 (qIdx (qfwd e.2.1 q))
    rw [h1, heq, qImg, List.getD_eq_getElem _ _ (by simp [qIdx_lt q]), List.getElem_map,
      List.getElem_range]
    have := hS9 q
    unfold qR
    omega

end DS243
