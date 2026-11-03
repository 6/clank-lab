import UniformGoodLaw

/-! Explicit ceiling count on the event that every column has at most three rows
and every two-row column occurs. -/
namespace ADG.Uniform
open Finset
open scoped Classical

lemma scan_triple_mass {m n : ℕ} (A : Matrix m n) (l : List (Fin n))
    (S : Finset (Fin n)) (U : Finset (Fin m))
    (hS : ∀ j ∈ S, (A j).card = 3 ∧ A j ⊆ U) :
    let T := Conflict.scanList (conflict A) l S
    T.biUnion A ⊆ U ∧ (T.biUnion A).card = 3*T.card := by
  induction l generalizing S U with
  | nil => simp [Conflict.scanList]
  | cons j l ih =>
    by_cases hj : j ∈ S
    · simp only [Conflict.scanList, if_pos hj]
      have hchild : ∀ v ∈ Conflict.prune (conflict A) j S,
          (A v).card = 3 ∧ A v ⊆ U \ A j := by
        intro v hv
        obtain ⟨hvS, _, hd⟩ := mem_filter.mp hv
        exact ⟨(hS v hvS).1, subset_sdiff.mpr ⟨(hS v hvS).2, by
          simpa only [conflict, not_not] using (not_not.mp hd).symm⟩⟩
      obtain ⟨hsub, hcard⟩ := ih _ _ hchild
      let T := Conflict.scanList (conflict A) l (Conflict.prune (conflict A) j S)
      have hjT : j ∉ T := by
        intro h
        have := Conflict.prune_subset (conflict A) j S
          (scanList_subset (conflict A) l _ h)
        simp at this
      have hdis : Disjoint (A j) (T.biUnion A) := disjoint_left.mpr (by
        intro x hxj hxT
        exact (mem_sdiff.mp (hsub hxT)).2 hxj)
      rw [biUnion_insert, card_union_of_disjoint hdis, card_insert_of_not_mem hjT]
      refine ⟨union_subset (hS j hj).2 (hsub.trans sdiff_subset), ?_⟩
      rw [(hS j hj).1, hcard]
      dsimp [T] at *
      omega
    · simpa only [Conflict.scanList, if_neg hj] using ih S U hS

lemma scan_count_ceiling {m n : ℕ} (A : Matrix m n) (l : List (Fin n))
    (U : Finset (Fin m)) :
    let T := Conflict.scanList (conflict A) l (triples A U)
    T.card + ((U \ T.biUnion A).card+1)/2 = (U.card-T.card+1)/2 := by
  obtain ⟨hsub, hc⟩ := scan_triple_mass A l (triples A U) U
    (fun j hj => (mem_triples A U j).mp hj)
  have hm := card_sdiff_add_card_eq_card hsub
  omega

/-- Fresh uniform ties have exactly the ceiling count determined by their
accepted labelled triple set, with no restriction on later pair ties. -/
theorem countProb_good_ceiling {m n : ℕ} (A : Matrix m n) (hf : feasible A)
    (hn : noLargeColumns A) (hp : allExactPairs A) (event : ℕ → Prop) :
    countProb A m univ event =
      (∑ l ∈ Conflict.orders (univ : Finset (Fin n)),
        let K := (Conflict.scanList (conflict A) l (triples A univ)).card
        if event ((m-K+1)/2) then (1 : ℝ) else 0) / n.factorial := by
  rw [countProb_phase A hf hn hp m univ (by simp),
    ← Conflict.scan_eq_choose (conflict A) univ (triples A univ) (subset_univ _) _,
    Conflict.scan_average]
  simp only [card_univ, Fintype.card_fin]
  congr 1
  apply sum_congr rfl
  intro l _
  unfold phasePayoff
  rw [scan_count_ceiling]
  simp

end ADG.Uniform
