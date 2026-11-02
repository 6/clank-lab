import BaseREhrhart.Data
import BaseREhrhart.Polynomial
import Mathlib.Data.Nat.Digits

/-! Semantic bridge for kernel-checked height data.
The packed base exceeds the entire residue population, so no histogram
coefficient can carry into another coefficient. -/

namespace BaseREhrhart

/-- Explicit arithmetic evaluator, proved equal to the semantic height below. -/
def rawHeight (b : ℕ) : ℕ :=
  (b + (13*b)%537824 + (182*b)%537824 + (2548*b)%537824 +
    (35672*b)%537824 + (499408*b)%537824)/537824

lemma height_eq_rawHeight (b : Fin D) : height b = rawHeight b.val := by
  simp [height, rawHeight, cNat, D, Fin.sum_univ_succ, Nat.add_assoc]

lemma height_le_five (b : Fin D) : height b ≤ 5 := by
  have hs : (∑ i : Fin 5, (cNat i * b.val) % D) ≤ 5 * (D - 1) := by
    calc
      _ ≤ ∑ _i : Fin 5, (D - 1) := by
        apply Finset.sum_le_sum
        intro i _
        exact Nat.le_sub_one_of_lt (Nat.mod_lt _ D_pos)
      _ = _ := by simp
  have hb := b.isLt
  unfold height
  simp only [D] at *
  omega

def radix : ℕ := 1048576

/-- Binary subdivision keeps kernel reduction depth logarithmic. -/
def packedBlock (start : ℕ) : ℕ → ℕ
  | 0 => radix ^ rawHeight start
  | k+1 => packedBlock start k + packedBlock (start + 2^k) k

lemma packedBlock_eq_sum (start k : ℕ) :
    packedBlock start k =
      ∑ i ∈ Finset.range (2 ^ k), radix ^ rawHeight (start + i) := by
  induction k generalizing start with
  | zero => simp [packedBlock]
  | succ k ih =>
    rw [packedBlock, pow_succ, Nat.mul_two, Finset.sum_range_add, ih, ih]
    simp only [Nat.add_assoc]

/-- A list of consecutive binary blocks. -/
def packedCover (start : ℕ) : List ℕ → ℕ
  | [] => 0
  | k::ks => packedBlock start k + packedCover (start + 2^k) ks

def coverSize (ks : List ℕ) : ℕ := (ks.map (2^·)).sum

lemma packedCover_eq_sum (ks : List ℕ) (start : ℕ) :
    packedCover start ks =
      ∑ i ∈ Finset.range (coverSize ks), radix ^ rawHeight (start + i) := by
  induction ks generalizing start with
  | nil => simp [packedCover, coverSize]
  | cons k ks ih =>
    simp only [packedCover, coverSize, List.map_cons, List.sum_cons]
    rw [Finset.sum_range_add, packedBlock_eq_sum, ih]
    simp only [coverSize, Nat.add_assoc]

/-- The actual finite histogram of the exact modular geometric height. -/
def heightCard (h : Fin 6) : ℕ :=
  (Finset.univ.filter (fun b : Fin D => height b = h.val)).card

lemma heightCard_lt_radix (h : Fin 6) : heightCard h < radix := by
  have hh := Finset.card_filter_le (Finset.univ : Finset (Fin D))
    (fun b => height b = h.val)
  simp only [Finset.card_univ, Fintype.card_fin] at hh
  exact lt_of_le_of_lt hh (by decide : D < radix)

lemma ofDigits_six (f : Fin 6 → ℕ) :
    Nat.ofDigits radix (List.ofFn f) = ∑ h : Fin 6, f h * radix ^ h.val := by
  simp [List.ofFn_succ, Nat.ofDigits_cons, Nat.ofDigits_nil, Fin.sum_univ_succ]
  ring

lemma packed_sum_eq_digits :
    (∑ b : Fin D, radix ^ rawHeight b.val) =
      Nat.ofDigits radix (List.ofFn heightCard) := by
  rw [ofDigits_six]
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin D)))
    (t := Finset.range 6) (g := height)
    (by intro b _; exact Finset.mem_range.mpr (Nat.lt_succ_of_le (height_le_five b)))
    (fun b => radix ^ height b)
  have hi : ∀ h : ℕ,
      (∑ b ∈ Finset.univ.filter (fun b : Fin D => height b = h), radix ^ height b) =
        (Finset.univ.filter (fun b : Fin D => height b = h)).card * radix ^ h := by
    intro h
    rw [Finset.sum_congr rfl (fun b hb => by rw [(Finset.mem_filter.mp hb).2])]
    simp
  simp_rw [hi] at hf
  rw [← Fin.sum_univ_eq_sum_range] at hf
  simpa only [heightCard, height_eq_rawHeight] using hf.symm

lemma histogram_of_packed_sum
    (hs : (∑ b : Fin D, radix ^ rawHeight b.val) =
      Nat.ofDigits radix (List.ofFn weight)) :
    ∀ h : Fin 6, heightCard h = weight h := by
  have hd : List.ofFn heightCard = List.ofFn weight := by
    apply Nat.ofDigits_inj_of_len_eq (by decide : 1 < radix)
    · simp
    · intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact heightCard_lt_radix i
    · intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      fin_cases i <;> decide
    · rw [← packed_sum_eq_digits]
      exact hs
  exact congrFun (List.ofFn_injective hd)

end BaseREhrhart
