import Certificate

namespace LockedTromino

/-- Enumerate sublists of a specified size, preserving pool order. -/
def chooseCells : Nat → List Cell → List (List Cell)
  | 0, _ => [[]]
  | _+1, [] => []
  | n+1, x::xs => (chooseCells n xs).map (x :: ·) ++ chooseCells (n+1) xs

theorem sublist_mem_choose {xs ys : List Cell} (hsub : xs.Sublist ys) :
    xs ∈ chooseCells xs.length ys := by
  induction hsub with
  | slnil => simp [chooseCells]
  | @cons xs ys a h ih =>
    cases xs with
    | nil => simp [chooseCells]
    | cons b bs => exact List.mem_append_right _ ih
  | @cons_cons xs ys a h ih =>
    simp only [List.length_cons, chooseCells, List.mem_append, List.mem_map]
    exact Or.inl ⟨xs,ih,rfl⟩

/-- Only 20 unordered candidates instead of 216 ordered triples per pair. -/
def SubsetPairCheck (xs ys : List Cell) : Prop :=
  (xs ++ ys).Nodup ∧
  ∀ candidate ∈ chooseCells 3 (xs ++ ys),
    tileCheck candidate = true → tileCheck (remainder (xs ++ ys) candidate) = true →
    SameCells candidate xs ∨ SameCells candidate ys

instance (xs ys : List Cell) : Decidable (SubsetPairCheck xs ys) := by
  unfold SubsetPairCheck; infer_instance

theorem subsetPairCheck_sound {xs ys : List Cell} (hp : SubsetPairCheck xs ys) :
    Rigid (Cells xs) (Cells ys) := by
  intro C D hs
  obtain ⟨a,b,c,hab,hac,hbc,hC⟩ := hs.1.1
  let pred : Cell → Bool := fun x => decide (x = a ∨ x = b ∨ x = c)
  let candidate := (xs ++ ys).filter pred
  have hmember : Sub C (Cells (xs ++ ys)) := by
    intro x hx
    have hu : (C x ∨ D x) ↔ (Cells xs x ∨ Cells ys x) := Iff.of_eq (congrFun hs.2.2.2 x)
    simpa [Cells] using hu.mp (Or.inl hx)
  have heq : Cells candidate = C := by
    apply region_ext
    intro x
    simp only [Cells, candidate, List.mem_filter]
    have he : pred x = true ↔ C x := by simp only [pred, decide_eq_true_eq, hC]
    rw [he]
    exact ⟨fun h => h.2, fun hx => ⟨hmember x hx,hx⟩⟩
  have hn : candidate.Nodup := hp.1.sublist List.filter_sublist
  have ht : Tile (Cells candidate) := heq.symm ▸ hs.1
  have hlen := triple_length hn ht.1
  have hin : candidate ∈ chooseCells 3 (xs ++ ys) := by
    rw [← hlen]
    exact sublist_mem_choose List.filter_sublist
  have hs' : Split (Cells xs) (Cells ys) (Cells candidate) D := heq.symm ▸ hs
  have hrem := remainder_eq hs'
  have hremnodup : (remainder (xs ++ ys) candidate).Nodup := hp.1.sublist List.filter_sublist
  have hchoice := hp.2 candidate hin (tileCheck_complete hn ht)
    (tileCheck_complete hremnodup (hrem.symm ▸ hs.2.1))
  have dis : Disjoint (Cells xs) (Cells ys) := by
    intro x hx hy
    exact (List.pairwise_append.mp hp.1).2.2 x hx x hy rfl
  rcases hchoice with h | h
  · have hc : C = Cells xs := heq.symm.trans (sameCells_eq h)
    refine Or.inl ⟨hc, ?_⟩
    rw [hc] at hs
    exact split_other dis hs
  · have hc : C = Cells ys := heq.symm.trans (sameCells_eq h)
    refine Or.inr ⟨hc, ?_⟩
    rw [hc] at hs
    have hu : Union (Cells xs) (Cells ys) = Union (Cells ys) (Cells xs) :=
      region_ext fun _ => Or.comm
    exact split_other (fun x hx hy => dis x hy hx)
      ⟨hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.trans hu⟩

end LockedTromino
