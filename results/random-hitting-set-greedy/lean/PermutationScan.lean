import ConflictCoupling
import Mathlib.Data.List.Permutation
import Mathlib.Data.Finset.Dedup

/-! A uniform without-replacement scan is the average of deterministic scans
over every permutation, each exactly once. -/
namespace ADG.Uniform.Conflict
open Finset
variable {α : Type} [DecidableEq α]

noncomputable def orders (R : Finset α) : Finset (List α) :=
  R.toList.permutations.toFinset

lemma mem_orders (R : Finset α) (l : List α) :
    l ∈ orders R ↔ l.Nodup ∧ l.toFinset = R := by
  simp only [orders, List.mem_toFinset, List.mem_permutations]
  constructor
  · intro h
    exact ⟨h.nodup_iff.mpr R.nodup_toList,
      (List.toFinset_eq_of_perm _ _ h).trans (by simp)⟩
  · rintro ⟨hn, hs⟩
    exact List.perm_of_nodup_nodup_toFinset_eq hn R.nodup_toList
      (hs.trans (by simp))

lemma card_orders (R : Finset α) : (orders R).card = R.card.factorial := by
  simp only [orders, List.toFinset_card_of_nodup (List.nodup_permutations _ R.nodup_toList),
    List.length_permutations, length_toList]

lemma orders_empty : orders (∅ : Finset α) = {[]} := by simp [orders]

lemma orders_cons (R : Finset α) (hR : R ≠ ∅) :
    orders R = R.biUnion (fun v => (orders (R.erase v)).image (List.cons v)) := by
  ext l
  rw [mem_orders, mem_biUnion]
  constructor
  · rintro ⟨hn, hs⟩
    cases l with
    | nil => simp at hs; exact False.elim (hR hs.symm)
    | cons v l =>
      obtain ⟨hv, hln⟩ := List.nodup_cons.mp hn
      have hvR : v ∈ R := by rw [← hs]; simp
      refine ⟨v, hvR, mem_image.mpr ⟨l, ?_, rfl⟩⟩
      rw [mem_orders]
      refine ⟨hln, ?_⟩
      rw [← hs]
      simp [List.toFinset_cons, hv]
  · rintro ⟨v, hvR, hvl⟩
    obtain ⟨l, hl, rfl⟩ := mem_image.mp hvl
    obtain ⟨hn, hs⟩ := (mem_orders _ _).mp hl
    have hv : v ∉ l := by
      intro hv
      have : v ∈ R.erase v := hs ▸ List.mem_toFinset.mpr hv
      simp at this
    exact ⟨List.nodup_cons.mpr ⟨hv, hn⟩,
      by rw [List.toFinset_cons, hs, insert_erase hvR]⟩

lemma sum_orders_cons (R : Finset α) (hR : R ≠ ∅) (f : List α → ℝ) :
    (∑ l ∈ orders R, f l) =
      ∑ v ∈ R, ∑ l ∈ orders (R.erase v), f (v :: l) := by
  rw [orders_cons R hR, sum_biUnion]
  · apply sum_congr rfl
    intro v _
    exact sum_image (fun _ _ _ _ h => List.cons.inj h |>.2)
  · intro v _ w _ hvw
    apply disjoint_left.mpr
    rintro l hlv hlw
    obtain ⟨a, _, ha⟩ := mem_image.mp hlv
    obtain ⟨b, _, hb⟩ := mem_image.mp hlw
    exact hvw (List.cons.inj (ha.trans hb.symm)).1

def scanList (adj : α → α → Prop) [DecidableRel adj] :
    List α → Finset α → Finset α
  | [], _ => ∅
  | v :: l, S => if v ∈ S then insert v (scanList adj l (prune adj v S))
      else scanList adj l S

theorem scan_average (adj : α → α → Prop) [DecidableRel adj]
    (R S : Finset α) (f : Finset α → ℝ) :
    scan adj R S f = (∑ l ∈ orders R, f (scanList adj l S)) / R.card.factorial := by
  classical
  induction R using Finset.strongInduction generalizing S f with
  | H R ih =>
    by_cases hR : R = ∅
    · subst R
      rw [scan.eq_def, dif_pos rfl]
      simp [orders_empty, scanList]
    rw [scan.eq_def, dif_neg hR]
    rw [sum_orders_cons R hR]
    rw [Finset.sum_coe_sort R (fun v => if v ∈ S then
      scan adj (R.erase v) (prune adj v S) (fun T => f (insert v T))
      else scan adj (R.erase v) S f)]
    have hc : (R.card : ℝ) ≠ 0 := by
      exact_mod_cast card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hR)
    have hcf : ((R.card-1).factorial : ℝ) ≠ 0 := by positivity
    have hfac : (R.card.factorial : ℝ) = R.card * (R.card-1).factorial := by
      have hpos : 0 < R.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hR)
      have heq : R.card = (R.card-1)+1 := by omega
      conv_lhs => rw [heq, Nat.factorial_succ]
      push_cast
      congr 1
      exact_mod_cast heq.symm
    have hterm (v : α) (hv : v ∈ R) :
        (if v ∈ S then scan adj (R.erase v) (prune adj v S) (fun T => f (insert v T))
          else scan adj (R.erase v) S f) =
        (∑ l ∈ orders (R.erase v), f (scanList adj (v :: l) S)) /
          (R.card-1).factorial := by
      have hlt := erase_ssubset hv
      by_cases hs : v ∈ S
      · rw [if_pos hs, ih _ hlt]
        simp only [scanList, if_pos hs, card_erase_of_mem hv]
      · rw [if_neg hs, ih _ hlt]
        simp only [scanList, if_neg hs, card_erase_of_mem hv]
    rw [sum_congr rfl hterm, ← sum_div, hfac, div_div]
    congr 1
    ring

end ADG.Uniform.Conflict
