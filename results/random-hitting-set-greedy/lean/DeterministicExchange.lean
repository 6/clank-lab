import GreedyPaths
import PathDefinitions
import LP

/-! Exchange of isolated-path middles for their ends, and pair completion. -/
namespace ADG
open Finset

lemma pathLeft_card {m : ℕ} (t : PathTuple m) : (pathLeft t).card = 3 := by
  simp [pathLeft, t.injective.eq_iff]
lemma pathMiddle_card {m : ℕ} (t : PathTuple m) : (pathMiddle t).card = 3 := by
  simp [pathMiddle, t.injective.eq_iff]
lemma pathRight_card {m : ℕ} (t : PathTuple m) : (pathRight t).card = 3 := by
  simp [pathRight, t.injective.eq_iff]

lemma pathLeft_subset_rows {m : ℕ} (t : PathTuple m) : pathLeft t ⊆ pathRows t := by
  intro i hi
  simp only [pathLeft, mem_insert, mem_singleton] at hi
  rcases hi with rfl | rfl | rfl <;> simp [pathRows]
lemma pathMiddle_subset_rows {m : ℕ} (t : PathTuple m) : pathMiddle t ⊆ pathRows t := by
  intro i hi
  simp only [pathMiddle, mem_insert, mem_singleton] at hi
  rcases hi with rfl | rfl | rfl <;> simp [pathRows]
lemma pathRight_subset_rows {m : ℕ} (t : PathTuple m) : pathRight t ⊆ pathRows t := by
  intro i hi
  simp only [pathRight, mem_insert, mem_singleton] at hi
  rcases hi with rfl | rfl | rfl <;> simp [pathRows]

lemma pathOccursAt_isolation {m n : ℕ} (A : Matrix m n) (t : PathTuple m)
    (left middle right : Fin n) (h : pathOccursAt A t left middle right)
    (j : Fin n) (hc : (A j).card = 3) (htouch : ¬Disjoint (A j) (pathRows t)) :
    j = middle ∨ j = left ∨ j = right := by
  by_contra hn
  have hne : j ≠ left ∧ j ≠ middle ∧ j ≠ right := by tauto
  have hout := h.2.2.2.2.2.2 j hne.1 hne.2.1 hne.2.2
  exact hout (by simp [pathForbidden, hc, htouch])

lemma pathOccursAt_middle_selected {m n : ℕ} (A : Matrix m n) (hn : noLargeColumns A)
    (t : PathTuple m) (left middle right : Fin n) (h : pathOccursAt A t left middle right) :
    (middle,3) ∈ greedyTrace A := by
  apply isolated_middle_triple_mem_greedy A hn (pathRows t) middle left right
  · rw [h.2.2.2.2.1]; exact pathMiddle_card t
  · rw [h.2.2.2.2.1]; exact pathMiddle_subset_rows t
  · exact h.1
  · exact h.2.1
  · exact pathOccursAt_isolation A t left middle right h

noncomputable def tripleColumns {m n : ℕ} (A : Matrix m n) : Finset (Fin n) :=
  (((greedyTrace A).filter (fun t => t.2 = 3)).map Prod.fst).toFinset

lemma mem_tripleColumns {m n : ℕ} (A : Matrix m n) (j : Fin n) :
    j ∈ tripleColumns A ↔ (j,3) ∈ greedyTrace A := by
  classical
  simp only [tripleColumns, List.mem_toFinset, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨⟨k,g⟩, ⟨ht,hg⟩, hkj⟩
    simp only [Prod.fst, Prod.snd, decide_eq_true_eq] at hg hkj
    subst k; subst g; exact ht
  · intro h
    exact ⟨(j,3), ⟨h, by simp⟩, rfl⟩

lemma tripleColumns_card {m n : ℕ} (A : Matrix m n) :
    (tripleColumns A).card = tripleCount A := by
  have hsub : (((greedyTrace A).filter (fun t => t.2 = 3)).map Prod.fst).Sublist
      ((greedyTrace A).map Prod.fst) := by
    apply List.Sublist.map
    exact List.filter_sublist
  have hnod := (trace_nodup A m univ).sublist hsub
  unfold tripleColumns
  rw [List.toFinset_card_of_nodup hnod, List.length_map]
  rfl

lemma badMiddles_subset_tripleColumns {m n : ℕ} (A : Matrix m n)
    (hn : noLargeColumns A) : badMiddles A ⊆ tripleColumns A := by
  classical
  intro middle hm
  obtain ⟨t,left,right,h⟩ := (Finset.mem_filter.mp hm).2
  exact (mem_tripleColumns A middle).mpr (pathOccursAt_middle_selected A hn t left middle right h)

lemma badMiddles_le_tripleCount {m n : ℕ} (A : Matrix m n)
    (hn : noLargeColumns A) : B A ≤ tripleCount A := by
  unfold B
  rw [← tripleColumns_card A]
  exact Finset.card_le_card (badMiddles_subset_tripleColumns A hn)

lemma tripleColumns_card_three {m n : ℕ} (A : Matrix m n) (hn : noLargeColumns A)
    (j : Fin n) (hj : j ∈ tripleColumns A) : (A j).card = 3 := by
  have ht := (mem_tripleColumns A j).mp hj
  have hle := (trace_positive_le A m univ (j,3) ht).2
  change 3 ≤ gain A univ j at hle
  have hc := hn j
  have hu := gain_le_column A univ j
  omega

lemma tripleColumns_pairwise {m n : ℕ} (A : Matrix m n) (hn : noLargeColumns A) :
    ∀ j ∈ tripleColumns A, ∀ k ∈ tripleColumns A, j ≠ k → Disjoint (A j) (A k) := by
  have hp : (((greedyTrace A).filter (fun t => t.2 = 3)).map Prod.fst).Pairwise
      (fun j k => Disjoint (A j) (A k)) := by
    simpa only [List.pairwise_map] using trace_triples_disjoint A hn m univ
  intro j hj k hk hne
  apply hp.set_pairwise (fun _ _ h => h.symm)
  · simpa only [tripleColumns, List.mem_toFinset] using hj
  · simpa only [tripleColumns, List.mem_toFinset] using hk
  · exact hne

/-- Every selected triple other than an isolated middle avoids its entire component. -/
lemma selected_triple_avoids_path {m n : ℕ} (A : Matrix m n) (hn : noLargeColumns A)
    (t : PathTuple m) (left middle right : Fin n) (h : pathOccursAt A t left middle right)
    (j : Fin n) (hj : j ∈ tripleColumns A) (hne : j ≠ middle) :
    Disjoint (A j) (pathRows t) := by
  have hm : middle ∈ tripleColumns A := (mem_tripleColumns A middle).mpr
    (pathOccursAt_middle_selected A hn t left middle right h)
  have hd := tripleColumns_pairwise A hn j hj middle hm hne
  by_contra hnot
  rcases pathOccursAt_isolation A t left middle right h j
      (tripleColumns_card_three A hn j hj) hnot with hm' | hl' | hr'
  · exact hne hm'
  · subst j
    apply (Finset.disjoint_left.mp hd) (a := t 2)
    · rw [h.2.2.2.1]; simp [pathLeft]
    · rw [h.2.2.2.2.1]; simp [pathMiddle]
  · subst j
    apply (Finset.disjoint_left.mp hd) (a := t 4)
    · rw [h.2.2.2.2.2.1]; simp [pathRight]
    · rw [h.2.2.2.2.1]; simp [pathMiddle]

/-- Exact pairs, with one feasible singleton at the end, cover any residual at ceiling half. -/
lemma pair_completion {m n : ℕ} (A : Matrix m n) (hf : feasible A)
    (hp : allExactPairs A) (U : Finset (Fin m)) :
    ∃ C : Finset (Fin n), C.card ≤ (U.card+1)/2 ∧
      ∀ i ∈ U, ∃ j ∈ C, i ∈ A j := by
  classical
  induction hu : U.card using Nat.strong_induction_on generalizing U with
  | h q ih =>
    by_cases hem : U = ∅
    · exact ⟨∅, by simp [hem], by simp [hem]⟩
    by_cases hsmall : U.card < 2
    · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hem
      obtain ⟨c, hc⟩ := hf a
      have hcard : U.card = 1 := by
        have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hem)
        omega
      have hsing : U = {a} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨ha, fun i hi => (Finset.card_le_one.mp (by omega)) i hi a ha⟩
      refine ⟨{c}, ?_, ?_⟩
      · have hq : q = 1 := by omega
        simp [hq]
      · intro i hi
        have : i = a := by simpa [hsing] using hi
        subst i
        exact ⟨c, by simp, hc⟩
    · have htwo : 1 < U.card := by omega
      obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp htwo
      obtain ⟨c,hc⟩ := hp a b hab
      have hsub : ({a,b} : Finset (Fin m)) ⊆ U := by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl <;> assumption
      have hres : (U \ {a,b}).card + 2 = U.card := by
        have hh := Finset.card_sdiff_add_card_inter U {a,b}
        rw [Finset.inter_eq_right.mpr hsub] at hh
        simpa [hab] using hh
      obtain ⟨D,hD,hcover⟩ := ih (U \ {a,b}).card (by omega) (U \ {a,b}) rfl
      refine ⟨insert c D, ?_, ?_⟩
      · have hins := Finset.card_insert_le c D
        omega
      · intro i hi
        by_cases hpab : i ∈ ({a,b} : Finset (Fin m))
        · exact ⟨c, by simp, by simpa [hc] using hpab⟩
        · obtain ⟨j,hj,hij⟩ := hcover i (Finset.mem_sdiff.mpr ⟨hi,hpab⟩)
          exact ⟨j, Finset.mem_insert_of_mem hj, hij⟩

lemma pathRows_eq_union {m : ℕ} (t : PathTuple m) :
    pathRows t = pathLeft t ∪ pathMiddle t ∪ pathRight t := by
  apply Finset.Subset.antisymm
  · intro i hi
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hi
    fin_cases v <;> simp [pathLeft, pathMiddle, pathRight]
  · exact Finset.union_subset (Finset.union_subset
      (pathLeft_subset_rows t) (pathMiddle_subset_rows t)) (pathRight_subset_rows t)

lemma pathLeft_disjoint_right {m : ℕ} (t : PathTuple m) :
    Disjoint (pathLeft t) (pathRight t) := by
  simp [pathLeft, pathRight, Finset.disjoint_insert_left, t.injective.eq_iff]

lemma occurring_touch_subset_rows {m n : ℕ} (A : Matrix m n)
    (t : PathTuple m) (left middle right : Fin n) (h : pathOccursAt A t left middle right)
    (j : Fin n) (hc : (A j).card = 3) (htouch : ¬Disjoint (A j) (pathRows t)) :
    A j ⊆ pathRows t := by
  rcases pathOccursAt_isolation A t left middle right h j hc htouch with rfl | rfl | rfl
  · rw [h.2.2.2.2.1]; exact pathMiddle_subset_rows t
  · rw [h.2.2.2.1]; exact pathLeft_subset_rows t
  · rw [h.2.2.2.2.2.1]; exact pathRight_subset_rows t

/-- Distinct actual isolated bad middles have disjoint seven-row components. -/
lemma distinct_occurring_paths_disjoint {m n : ℕ} (A : Matrix m n) (hn : noLargeColumns A)
    (t s : PathTuple m) (left middle right left' middle' right' : Fin n)
    (h : pathOccursAt A t left middle right) (h' : pathOccursAt A s left' middle' right')
    (hne : middle' ≠ middle) : Disjoint (pathRows s) (pathRows t) := by
  have hmid : Disjoint (A middle') (pathRows t) := selected_triple_avoids_path A hn
    t left middle right h middle' ((mem_tripleColumns A middle').mpr
      (pathOccursAt_middle_selected A hn s left' middle' right' h')) hne
  have hleft : Disjoint (A left') (pathRows t) := by
    by_contra hd
    have hsub := occurring_touch_subset_rows A t left middle right h left'
      (by rw [h'.2.2.2.1]; exact pathLeft_card s) hd
    apply (Finset.disjoint_left.mp hmid) (a := s 2)
    · rw [h'.2.2.2.2.1]; simp [pathMiddle]
    · apply hsub
      rw [h'.2.2.2.1]; simp [pathLeft]
  have hright : Disjoint (A right') (pathRows t) := by
    by_contra hd
    have hsub := occurring_touch_subset_rows A t left middle right h right'
      (by rw [h'.2.2.2.2.2.1]; exact pathRight_card s) hd
    apply (Finset.disjoint_left.mp hmid) (a := s 4)
    · rw [h'.2.2.2.2.1]; simp [pathMiddle]
    · apply hsub
      rw [h'.2.2.2.2.2.1]; simp [pathRight]
  rw [pathRows_eq_union, ←h'.2.2.2.1, ←h'.2.2.2.2.1, ←h'.2.2.2.2.2.1]
  simp only [Finset.disjoint_union_left]
  exact ⟨⟨hleft,hmid⟩,hright⟩

/-- A disjoint collection of actual triple columns extends to a genuine small cover. -/
lemma triple_packing_cover {m n : ℕ} (A : Matrix m n) (hf : feasible A)
    (hp : allExactPairs A) (Q : Finset (Fin n))
    (hc : ∀ j ∈ Q, (A j).card = 3)
    (hd : ∀ j ∈ Q, ∀ k ∈ Q, j ≠ k → Disjoint (A j) (A k)) :
    ∃ C : Finset (Fin n), C.card ≤ (m-Q.card+1)/2 ∧ coversBy A C := by
  classical
  let V := Q.biUnion A
  have hV : V.card = 3*Q.card := by
    dsimp [V]
    rw [Finset.card_biUnion (by intro j hj k hk hne; exact hd j hj k hk hne)]
    calc
      (∑ j ∈ Q, (A j).card) = ∑ _j ∈ Q, 3 := Finset.sum_congr rfl hc
      _ = 3*Q.card := by simp [Nat.mul_comm]
  let U : Finset (Fin m) := univ \ V
  have hU : U.card + 3*Q.card = m := by
    have hmass := Finset.card_sdiff_add_card_inter (univ : Finset (Fin m)) V
    simpa [U, hV] using hmass
  obtain ⟨D,hD,hcover⟩ := pair_completion A hf hp U
  refine ⟨Q ∪ D, ?_, ?_⟩
  · have hun := Finset.card_union_le Q D
    omega
  · intro i
    by_cases hi : i ∈ V
    · obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp hi
      exact ⟨j, Finset.mem_union_left D hj, hij⟩
    · obtain ⟨j,hj,hij⟩ := hcover i (by simp [U,hi])
      exact ⟨j, Finset.mem_union_right Q hj, hij⟩

lemma lp_le_triple_packing {m n : ℕ} (A : Matrix m n) (hf : feasible A)
    (hp : allExactPairs A) (Q : Finset (Fin n))
    (hc : ∀ j ∈ Q, (A j).card = 3)
    (hd : ∀ j ∈ Q, ∀ k ∈ Q, j ≠ k → Disjoint (A j) (A k)) :
    L A ≤ ((m-Q.card+1)/2 : ℕ) := by
  obtain ⟨C,hC,hcover⟩ := triple_packing_cover A hf hp Q hc hd
  exact (lp_le_cover A C hcover).trans (by exact_mod_cast hC)

structure BadPathData {m n : ℕ} (A : Matrix m n) (middle : Fin n) where
  tuple : PathTuple m
  left : Fin n
  right : Fin n
  occurs : pathOccursAt A tuple left middle right

noncomputable def chosenBadPath {m n : ℕ} (A : Matrix m n) (b : ↥(badMiddles A)) :
    BadPathData A b.val := by
  classical
  have hex : Nonempty (BadPathData A b.val) := by
    obtain ⟨t,l,r,h⟩ := (Finset.mem_filter.mp b.property).2
    exact ⟨⟨t,l,r,h⟩⟩
  exact Classical.choice hex

noncomputable def replacementEnds {m n : ℕ} (A : Matrix m n) (b : ↥(badMiddles A)) :
    Finset (Fin n) := {(chosenBadPath A b).left, (chosenBadPath A b).right}

lemma replacementEnds_card {m n : ℕ} (A : Matrix m n) (b : ↥(badMiddles A)) :
    (replacementEnds A b).card = 2 := by
  have h := (chosenBadPath A b).occurs.2.2.1
  simp [replacementEnds, h]

lemma replacementEnd_support {m n : ℕ} (A : Matrix m n) (b : ↥(badMiddles A))
    (j : Fin n) (hj : j ∈ replacementEnds A b) :
    (A j).card = 3 ∧ A j ⊆ pathRows (chosenBadPath A b).tuple := by
  have h := (chosenBadPath A b).occurs
  simp only [replacementEnds, mem_insert, mem_singleton] at hj
  rcases hj with rfl | rfl
  · rw [h.2.2.2.1]
    exact ⟨pathLeft_card _, pathLeft_subset_rows _⟩
  · rw [h.2.2.2.2.2.1]
    exact ⟨pathRight_card _, pathRight_subset_rows _⟩

lemma replacementEnds_pairwise {m n : ℕ} (A : Matrix m n) (b : ↥(badMiddles A)) :
    ∀ j ∈ replacementEnds A b, ∀ k ∈ replacementEnds A b, j ≠ k → Disjoint (A j) (A k) := by
  have h := (chosenBadPath A b).occurs
  intro j hj k hk hne
  simp only [replacementEnds, mem_insert, mem_singleton] at hj hk
  rcases hj with rfl | rfl <;> rcases hk with rfl | rfl
  · exact False.elim (hne rfl)
  · rw [h.2.2.2.1,h.2.2.2.2.2.1]
    exact pathLeft_disjoint_right _
  · rw [h.2.2.2.1,h.2.2.2.2.2.1]
    exact (pathLeft_disjoint_right _).symm
  · exact False.elim (hne rfl)

lemma replacementEnds_cross_supports {m n : ℕ} (A : Matrix m n) (hn : noLargeColumns A)
    (b c : ↥(badMiddles A)) (hne : b ≠ c)
    (j : Fin n) (hj : j ∈ replacementEnds A b)
    (k : Fin n) (hk : k ∈ replacementEnds A c) : Disjoint (A j) (A k) := by
  have hbc : b.val ≠ c.val := fun he => hne (Subtype.ext he)
  have hrows := distinct_occurring_paths_disjoint A hn
    (chosenBadPath A c).tuple (chosenBadPath A b).tuple
    (chosenBadPath A c).left c.val (chosenBadPath A c).right
    (chosenBadPath A b).left b.val (chosenBadPath A b).right
    (chosenBadPath A c).occurs (chosenBadPath A b).occurs hbc
  exact hrows.mono (replacementEnd_support A b j hj).2 (replacementEnd_support A c k hk).2

lemma column_ne_of_disjoint_three {m n : ℕ} (A : Matrix m n) (j k : Fin n)
    (hc : (A j).card = 3) (hd : Disjoint (A j) (A k)) : j ≠ k := by
  intro he; subst k
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0 < (A j).card by omega)
  exact (Finset.disjoint_left.mp hd) hi hi

lemma replacementEnds_disjoint {m n : ℕ} (A : Matrix m n) (hn : noLargeColumns A)
    (b c : ↥(badMiddles A)) (hne : b ≠ c) :
    Disjoint (replacementEnds A b) (replacementEnds A c) := by
  apply Finset.disjoint_left.mpr
  intro j hj hk
  exact column_ne_of_disjoint_three A j j (replacementEnd_support A b j hj).1
    (replacementEnds_cross_supports A hn b c hne j hj j hk) rfl

noncomputable def allReplacementEnds {m n : ℕ} (A : Matrix m n) : Finset (Fin n) := by
  classical
  exact univ.biUnion (replacementEnds A)

lemma allReplacementEnds_card {m n : ℕ} (A : Matrix m n) (hn : noLargeColumns A) :
    (allReplacementEnds A).card = 2*B A := by
  classical
  unfold allReplacementEnds
  rw [Finset.card_biUnion (by
    intro b hb c hc hne
    exact replacementEnds_disjoint A hn b c hne)]
  simp [replacementEnds_card, B, Nat.mul_comm]

lemma allReplacementEnds_pairwise {m n : ℕ} (A : Matrix m n) (hn : noLargeColumns A) :
    ∀ j ∈ allReplacementEnds A, ∀ k ∈ allReplacementEnds A,
      j ≠ k → Disjoint (A j) (A k) := by
  classical
  intro j hj k hk hne
  obtain ⟨b,hb,hjb⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨c,hc,hkc⟩ := Finset.mem_biUnion.mp hk
  by_cases hbc : b = c
  · subst c
    exact replacementEnds_pairwise A b j hjb k hkc hne
  · exact replacementEnds_cross_supports A hn b c hbc j hjb k hkc

noncomputable def survivingTriples {m n : ℕ} (A : Matrix m n) : Finset (Fin n) :=
  tripleColumns A \ badMiddles A

noncomputable def exchangedTriples {m n : ℕ} (A : Matrix m n) : Finset (Fin n) :=
  survivingTriples A ∪ allReplacementEnds A

lemma survivor_replacement_supports_disjoint {m n : ℕ} (A : Matrix m n) (hn : noLargeColumns A)
    (j : Fin n) (hj : j ∈ survivingTriples A)
    (k : Fin n) (hk : k ∈ allReplacementEnds A) : Disjoint (A j) (A k) := by
  classical
  obtain ⟨b,hb,hkb⟩ := Finset.mem_biUnion.mp hk
  let hd := chosenBadPath A b
  have hne : j ≠ b.val := by
    intro he
    exact (Finset.mem_sdiff.mp hj).2 (he ▸ b.property)
  have hrows := selected_triple_avoids_path A hn hd.tuple hd.left b.val hd.right
    hd.occurs j (Finset.mem_sdiff.mp hj).1 hne
  exact hrows.mono_right (replacementEnd_support A b k hkb).2

lemma survivor_replacement_disjoint {m n : ℕ} (A : Matrix m n) (hn : noLargeColumns A) :
    Disjoint (survivingTriples A) (allReplacementEnds A) := by
  apply Finset.disjoint_left.mpr
  intro j hj hk
  exact column_ne_of_disjoint_three A j j
    (tripleColumns_card_three A hn j (Finset.mem_sdiff.mp hj).1)
    (survivor_replacement_supports_disjoint A hn j hj j hk) rfl

lemma exchangedTriples_card {m n : ℕ} (A : Matrix m n) (hn : noLargeColumns A) :
    (exchangedTriples A).card = tripleCount A + B A := by
  classical
  unfold exchangedTriples
  rw [Finset.card_union_of_disjoint (survivor_replacement_disjoint A hn),
    allReplacementEnds_card A hn]
  have hs : (survivingTriples A).card = tripleCount A - B A := by
    unfold survivingTriples
    rw [Finset.card_sdiff (badMiddles_subset_tripleColumns A hn), tripleColumns_card]
    rfl
  have hB := badMiddles_le_tripleCount A hn
  omega

lemma exchangedTriples_support_card {m n : ℕ} (A : Matrix m n) (hn : noLargeColumns A) :
    ∀ j ∈ exchangedTriples A, (A j).card = 3 := by
  classical
  intro j hj
  rcases Finset.mem_union.mp hj with hs | he
  · exact tripleColumns_card_three A hn j (Finset.mem_sdiff.mp hs).1
  · obtain ⟨b,hb,hjb⟩ := Finset.mem_biUnion.mp he
    exact (replacementEnd_support A b j hjb).1

lemma exchangedTriples_support_disjoint {m n : ℕ} (A : Matrix m n) (hn : noLargeColumns A) :
    ∀ j ∈ exchangedTriples A, ∀ k ∈ exchangedTriples A,
      j ≠ k → Disjoint (A j) (A k) := by
  classical
  intro j hj k hk hne
  rcases Finset.mem_union.mp hj with hs | he <;> rcases Finset.mem_union.mp hk with hs' | he'
  · exact tripleColumns_pairwise A hn j (Finset.mem_sdiff.mp hs).1 k
      (Finset.mem_sdiff.mp hs').1 hne
  · exact survivor_replacement_supports_disjoint A hn j hs k he'
  · exact (survivor_replacement_supports_disjoint A hn k hs' j he).symm
  · exact allReplacementEnds_pairwise A hn j he k he' hne

/-- Genuine simultaneous exchange and completion, with a single global rounding loss. -/
theorem isolated_path_exchange_cover {m n : ℕ} (A : Matrix m n)
    (hm : 2 ≤ m) (hn : noLargeColumns A) (hp : allExactPairs A) :
    ∃ C : Finset (Fin n), C.card ≤ (m-tripleCount A-B A+1)/2 ∧ coversBy A C := by
  obtain ⟨C,hC,hcover⟩ := triple_packing_cover A (exactPairs_feasible A hm hp) hp
    (exchangedTriples A) (exchangedTriples_support_card A hn) (exchangedTriples_support_disjoint A hn)
  refine ⟨C, ?_, hcover⟩
  simpa [exchangedTriples_card A hn, Nat.sub_add_eq] using hC

/-- Bound on the actual fractional optimum, supplied by the actual exchanged cover. -/
theorem lp_le_isolated_path_exchange {m n : ℕ} (A : Matrix m n)
    (hm : 2 ≤ m) (hn : noLargeColumns A) (hp : allExactPairs A) :
    L A ≤ ((m-tripleCount A-B A+1)/2 : ℕ) := by
  obtain ⟨C,hC,hcover⟩ := isolated_path_exchange_cover A hm hn hp
  exact (lp_le_cover A C hcover).trans (by exact_mod_cast hC)

end ADG
