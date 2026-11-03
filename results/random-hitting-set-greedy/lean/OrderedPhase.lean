import UniformPhase
import PermutationScan
import DeterministicGap

/-! The original leftmost Greedy as an ordered scan of the triple phase. -/
namespace ADG.Uniform
open Finset
open scoped Classical

lemma scanList_subset {α : Type} [DecidableEq α] (adj : α → α → Prop)
    [DecidableRel adj] (l : List α) (S : Finset α) :
    Conflict.scanList adj l S ⊆ S := by
  induction l generalizing S with
  | nil => simp [Conflict.scanList]
  | cons v l ih =>
    simp only [Conflict.scanList]
    split_ifs with hv
    · exact insert_subset hv ((ih _).trans
        ((Conflict.prune_subset adj v S).trans (erase_subset _ _)))
    · exact ih S

lemma scanList_first {α : Type} [DecidableEq α] (adj : α → α → Prop)
    [DecidableRel adj] (l : List α) (S : Finset α) (v : α)
    (h : l.find? (fun w => w ∈ S) = some v) :
    Conflict.scanList adj l S =
      insert v (Conflict.scanList adj l (Conflict.prune adj v S)) := by
  induction l with
  | nil => simp at h
  | cons w l ih =>
    by_cases hw : w ∈ S
    · simp [hw] at h
      subst v
      have hnot : w ∉ Conflict.prune adj w S := by
        intro hmem
        have := Conflict.prune_subset adj w S hmem
        simp at this
      simp [Conflict.scanList, hw, hnot]
    · have hf : l.find? (fun w => w ∈ S) = some v := by simpa [hw] using h
      have hnot : w ∉ Conflict.prune adj v S := fun hm =>
        hw (mem_of_mem_erase (Conflict.prune_subset adj v S hm))
      simpa [Conflict.scanList, hw, hnot] using ih hf

lemma best_find_level {m n : ℕ} (A : Matrix m n) (U : Finset (Fin m))
    (l : List (Fin n)) (b : ℕ) (v : Fin n)
    (hb : ∀ j ∈ l, gain A U j ≤ b)
    (hv : l.find? (fun j => gain A U j = b) = some v) : best A U l = some v := by
  induction l with
  | nil => simp at hv
  | cons w l ih =>
    by_cases hw : gain A U w = b
    · have heq : w = v := by simpa [hw] using hv
      subst v
      cases ht : best A U l with
      | none => simp [best, ht]
      | some t =>
        have htm := (best_mem_max A U l t ht).1
        have htw : gain A U t ≤ gain A U w := by rw [hw]; exact hb t (by simp [htm])
        simp [best, ht, htw]
    · have htail : l.find? (fun j => gain A U j = b) = some v := by simpa [hw] using hv
      have hit := ih (fun j hj => hb j (by simp [hj])) htail
      have hvb : gain A U v = b := by simpa using List.find?_some htail
      have hwb : gain A U w < b := lt_of_le_of_ne (hb w (by simp)) hw
      simp [best, hit, hvb, Nat.not_le_of_gt hwb]

lemma original_triple_first {m n : ℕ} (A : Matrix m n) (U : Finset (Fin m))
    (hn : noLargeColumns A) (ht : (triples A U).Nonempty) :
    ∃ j, best A U (List.finRange n) = some j ∧
      (List.finRange n).find? (fun v => v ∈ triples A U) = some j ∧
      j ∈ triples A U := by
  have he : ∃ j ∈ List.finRange n, decide (j ∈ triples A U) = true := by
    obtain ⟨j, hj⟩ := ht
    exact ⟨j, List.mem_finRange j, by simpa using hj⟩
  obtain ⟨j, hj⟩ : ∃ j, (List.finRange n).find? (fun v => v ∈ triples A U) = some j := by
    apply Option.ne_none_iff_exists'.mp
    intro hnone
    obtain ⟨v, hv, hp⟩ := he
    exact (List.find?_eq_none.mp hnone v hv) hp
  refine ⟨j, ?_, hj, ?_⟩
  · apply best_find_level A U _ 3 j (fun v _ => (gain_le_column A U v).trans (hn v))
    simpa only [triples_gain A U hn] using hj
  · simpa using List.find?_some hj

lemma scanList_empty {α : Type} [DecidableEq α] (adj : α → α → Prop)
    [DecidableRel adj] (l : List α) : Conflict.scanList adj l ∅ = ∅ := by
  induction l with
  | nil => rfl
  | cons v l ih => simpa [Conflict.scanList] using ih

/-- Deterministic leftmost trace and its ordered triple scan have identical counts. -/
theorem original_count_phase {m n : ℕ} (A : Matrix m n) (hf : feasible A)
    (hn : noLargeColumns A) (hp : allExactPairs A) (fuel : ℕ)
    (U : Finset (Fin m)) (hfu : U.card ≤ fuel) :
    let T := Conflict.scanList (conflict A) (List.finRange n) (triples A U)
    (trace A fuel U).length = T.card + ((U \ T.biUnion A).card + 1)/2 := by
  induction fuel generalizing U with
  | zero =>
    have hU : U = ∅ := card_eq_zero.mp (by omega)
    have ht : triples A U = ∅ := by
      apply eq_empty_iff_forall_not_mem.mpr
      intro j hj
      obtain ⟨hc, hs⟩ := (mem_triples A U j).mp hj
      rw [hU] at hs
      have := subset_empty.mp hs
      simp [this] at hc
    simp only [ht, scanList_empty]
    simp [trace, hU]
  | succ fuel ih =>
    by_cases hU : U = ∅
    · have ht : triples A U = ∅ := by
        apply eq_empty_iff_forall_not_mem.mpr
        intro j hj
        obtain ⟨hc, hs⟩ := (mem_triples A U j).mp hj
        rw [hU] at hs
        have := subset_empty.mp hs
        simp [this] at hc
      simp only [ht, scanList_empty]
      simp [trace, hU]
    obtain ⟨j, hb, hpos⟩ := best_exists_positive A hf U hU
    have hj : j ∈ maximizers A U := (mem_maximizers A U j).mpr
      ⟨hpos, fun t => (best_mem_max A U _ j hb).2 t (List.mem_finRange t)⟩
    have hm := card_sdiff_add_card_inter U (A j)
    change (U \ A j).card + gain A U j = U.card at hm
    have hres : (U \ A j).card ≤ fuel := by omega
    simp only [trace, if_neg hU, hb, if_neg (Nat.ne_of_gt hpos), List.length_cons]
    by_cases ht : triples A U = ∅
    · have hg := maximal_low_gain A hp hn U ht j hj
      have htc : triples A (U \ A j) = ∅ := subset_empty.mp (by
        simpa [ht] using (triples_mono A (sdiff_subset : U \ A j ⊆ U)))
      rw [ih _ hres]
      simp only [ht, htc, scanList_empty, card_empty, biUnion_empty, sdiff_empty, zero_add]
      omega
    · obtain ⟨v, hvb, hvf, hvt⟩ := original_triple_first A U hn
        (nonempty_iff_ne_empty.mpr ht)
      have hvj : v = j := Option.some.inj (hvb.symm.trans hb)
      subst v
      have hscan := scanList_first (conflict A) (List.finRange n) (triples A U) j hvf
      rw [ih _ hres, hscan, ← triples_prune A U j hvt]
      let T := Conflict.scanList (conflict A) (List.finRange n) (triples A (U \ A j))
      have hjT : j ∉ T := by
        intro hjT
        have hh := scanList_subset (conflict A) (List.finRange n)
          (triples A (U \ A j)) hjT
        rw [triples_prune A U j hvt] at hh
        have := Conflict.prune_subset (conflict A) j (triples A U) hh
        simp at this
      have hsd : (U \ A j) \ T.biUnion A = U \ (insert j T).biUnion A := by
        ext x
        simp only [mem_sdiff, mem_biUnion, mem_insert]
        constructor <;> intro h <;> aesop
      change T.card + ((U \ A j) \ T.biUnion A).card.succ / 2 + 1 =
        (insert j T).card + ((U \ (insert j T).biUnion A).card + 1)/2
      rw [card_insert_of_not_mem hjT, hsd]
      omega

end ADG.Uniform
