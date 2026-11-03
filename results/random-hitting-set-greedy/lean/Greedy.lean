import Endpoint

/-! The phases of leftmost Greedy on matrices whose columns have at most three
rows and which contain every two-row column. -/
namespace ADG
open Finset

lemma best_none_iff {m n : ℕ} (A : Matrix m n) (U : Finset (Fin m))
    (l : List (Fin n)) : best A U l = none ↔ l = [] := by
  induction l with
  | nil => simp [best]
  | cons j js ih =>
    simp only [best]
    cases hb : best A U js with
    | none => simp [hb]
    | some t => simp [hb]; split <;> simp

lemma best_mem_max {m n : ℕ} (A : Matrix m n) (U : Finset (Fin m))
    (l : List (Fin n)) (j : Fin n) (h : best A U l = some j) :
    j ∈ l ∧ ∀ t ∈ l, gain A U t ≤ gain A U j := by
  induction l generalizing j with
  | nil => simp [best] at h
  | cons a l ih =>
    simp only [best] at h
    cases hb : best A U l with
    | none =>
      simp only [hb] at h
      cases h
      have hl : l = [] := (best_none_iff A U l).mp hb
      subst l
      simp
    | some b =>
      simp only [hb] at h
      have hi := ih b hb
      split at h
      · rename_i hab
        cases h
        constructor
        · simp
        · intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · exact le_rfl
          · exact (hi.2 t ht).trans hab
      · rename_i hab
        cases h
        constructor
        · exact List.mem_cons_of_mem a hi.1
        · intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · exact Nat.le_of_lt (Nat.lt_of_not_ge hab)
          · exact hi.2 t ht

lemma gain_mono {m n : ℕ} (A : Matrix m n) {U V : Finset (Fin m)}
    (h : U ⊆ V) (j : Fin n) : gain A U j ≤ gain A V j := by
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_inter.mpr ⟨h (Finset.mem_inter.mp hi).1, (Finset.mem_inter.mp hi).2⟩

lemma gain_le_card {m n : ℕ} (A : Matrix m n) (U : Finset (Fin m)) (j : Fin n) :
    gain A U j ≤ U.card := Finset.card_le_card Finset.inter_subset_left

lemma gain_le_column {m n : ℕ} (A : Matrix m n) (U : Finset (Fin m)) (j : Fin n) :
    gain A U j ≤ (A j).card := Finset.card_le_card Finset.inter_subset_right

lemma exactPairs_feasible {m n : ℕ} (A : Matrix m n) (hm : 2 ≤ m)
    (hp : allExactPairs A) : feasible A := by
  intro i
  obtain ⟨j, hj⟩ : ∃ j : Fin m, j ≠ i := by
    by_cases h : i = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, by intro he; have := congrArg Fin.val (he.trans h); simp at this⟩
    · exact ⟨⟨0, by omega⟩, Ne.symm h⟩
  obtain ⟨c, hc⟩ := hp i j (Ne.symm hj)
  exact ⟨c, by simp [hc]⟩

lemma best_exists_positive {m n : ℕ} (A : Matrix m n) (hf : feasible A)
    (U : Finset (Fin m)) (hu : U ≠ ∅) :
    ∃ j, best A U (List.finRange n) = some j ∧ 0 < gain A U j := by
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hu
  obtain ⟨c, hc⟩ := hf i
  have hpos : 0 < gain A U c := Finset.card_pos.mpr ⟨i, by simp [hi, hc]⟩
  cases hb : best A U (List.finRange n) with
  | none =>
    have hl := (best_none_iff A U _).mp hb
    have : c ∈ List.finRange n := List.mem_finRange c
    rw [hl] at this
    contradiction
  | some j =>
    exact ⟨j, rfl, hpos.trans_le ((best_mem_max A U _ j hb).2 c (List.mem_finRange c))⟩

lemma best_gain_at_least_two {m n : ℕ} (A : Matrix m n) (hp : allExactPairs A)
    (U : Finset (Fin m)) (hu : 2 ≤ U.card) (j : Fin n)
    (hb : best A U (List.finRange n) = some j) : 2 ≤ gain A U j := by
  obtain ⟨a, ha, b, hbU, hab⟩ := Finset.one_lt_card.mp hu
  obtain ⟨c, hc⟩ := hp a b hab
  have hpU : ({a,b} : Finset (Fin m)) ⊆ U := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hg : gain A U c = 2 := by
    simp only [gain, hc]
    rw [Finset.inter_eq_right.mpr hpU]
    simp [hab]
  rw [← hg]
  exact (best_mem_max A U _ j hb).2 c (List.mem_finRange c)

/-- Every actual recorded step is positive and bounded by its gain in the initial residual. -/
lemma trace_positive_le {m n : ℕ} (A : Matrix m n) (fuel : ℕ)
    (U : Finset (Fin m)) :
    ∀ t ∈ trace A fuel U, 0 < t.2 ∧ t.2 ≤ gain A U t.1 := by
  induction fuel generalizing U with
  | zero => simp [trace]
  | succ fuel ih =>
    simp only [trace]
    split
    · simp
    · cases hb : best A U (List.finRange n) with
      | none => simp
      | some j =>
        simp only
        split
        · simp
        · rename_i hg
          intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · exact ⟨Nat.pos_of_ne_zero hg, le_rfl⟩
          · have hi := ih (U \ A j) t ht
            exact ⟨hi.1, hi.2.trans (gain_mono A Finset.sdiff_subset _)⟩

lemma gain_sdiff_self {m n : ℕ} (A : Matrix m n) (U : Finset (Fin m)) (j : Fin n) :
    gain A (U \ A j) j = 0 := by simp [gain]

lemma trace_nodup {m n : ℕ} (A : Matrix m n) (fuel : ℕ)
    (U : Finset (Fin m)) : ((trace A fuel U).map Prod.fst).Nodup := by
  induction fuel generalizing U with
  | zero => simp [trace]
  | succ fuel ih =>
    simp only [trace]
    split
    · simp
    · cases hb : best A U (List.finRange n) with
      | none => simp
      | some j =>
        simp only
        split
        · simp
        · simp only [List.map_cons, List.nodup_cons]
          refine ⟨?_, ih _⟩
          intro hj
          obtain ⟨t, ht, he⟩ := List.mem_map.mp hj
          have hi := trace_positive_le A fuel (U \ A j) t ht
          rw [he, gain_sdiff_self] at hi
          omega

lemma triple_support_subset {m n : ℕ} (A : Matrix m n) (hn : noLargeColumns A)
    (fuel : ℕ) (U : Finset (Fin m)) (t : Fin n × ℕ)
    (ht : t ∈ trace A fuel U) (hg : t.2 = 3) : A t.1 ⊆ U := by
  have hi := (trace_positive_le A fuel U t ht).2
  have hs : U ∩ A t.1 = A t.1 := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
    have := hn t.1
    simp only [gain] at hi
    omega
  exact Finset.inter_eq_right.mp hs

lemma trace_triples_disjoint {m n : ℕ} (A : Matrix m n) (hn : noLargeColumns A)
    (fuel : ℕ) (U : Finset (Fin m)) :
    (((trace A fuel U).filter (fun t => t.2 = 3)).map (fun t => A t.1)).Pairwise Disjoint := by
  induction fuel generalizing U with
  | zero => simp [trace]
  | succ fuel ih =>
    simp only [trace]
    split
    · simp
    · cases hb : best A U (List.finRange n) with
      | none => simp
      | some j =>
        simp only
        split
        · simp
        · by_cases hg : gain A U j = 3
          · simp only [List.filter_cons, hg, decide_true, Bool.true_eq, ↓reduceIte,
              List.map_cons, List.pairwise_cons]
            refine ⟨?_, ih _⟩
            intro s hs
            obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
            have htf := List.mem_filter.mp ht
            have hts := triple_support_subset A hn fuel (U \ A j) t htf.1 (by simpa using htf.2)
            exact Finset.disjoint_left.mpr (by
              intro i hi hj
              exact (Finset.mem_sdiff.mp (hts hj)).2 hi)
          · simpa [List.filter_cons, hg] using ih (U \ A j)

/-- A later positive step never exceeds the gain of the current actual maximum. -/
lemma tail_gain_le_best {m n : ℕ} (A : Matrix m n) (fuel : ℕ)
    (U : Finset (Fin m)) (j : Fin n)
    (hb : best A U (List.finRange n) = some j)
    (t : Fin n × ℕ) (ht : t ∈ trace A fuel (U \ A j)) :
    t.2 ≤ gain A U j := by
  have hi := (trace_positive_le A fuel (U \ A j) t ht).2
  exact (hi.trans (gain_mono A Finset.sdiff_subset _)).trans
    ((best_mem_max A U _ j hb).2 t.1 (List.mem_finRange t.1))

/-- Exact phases and removed-row mass, for an arbitrary initial residual and enough fuel. -/
lemma trace_phase_mass {m n : ℕ} (A : Matrix m n) (hf : feasible A)
    (hn : noLargeColumns A) (hp : allExactPairs A) (fuel : ℕ)
    (U : Finset (Fin m)) (hfu : U.card ≤ fuel) :
    ∃ K T S : ℕ, S ≤ 1 ∧
      (trace A fuel U).map Prod.snd =
        List.replicate K 3 ++ List.replicate T 2 ++ List.replicate S 1 ∧
      U.card = 3*K + 2*T + S := by
  induction fuel generalizing U with
  | zero =>
    have hu : U = ∅ := Finset.card_eq_zero.mp (by omega)
    subst U
    exact ⟨0, 0, 0, by omega, by simp [trace], by simp⟩
  | succ fuel ih =>
    by_cases hu : U = ∅
    · subst U
      exact ⟨0, 0, 0, by omega, by simp [trace], by simp⟩
    obtain ⟨j, hb, hgpos⟩ := best_exists_positive A hf U hu
    have hgle : gain A U j ≤ 3 := (gain_le_column A U j).trans (hn j)
    have hmass : (U \ A j).card + gain A U j = U.card := by
      exact Finset.card_sdiff_add_card_inter U (A j)
    have hres : (U \ A j).card ≤ fuel := by omega
    have heq : trace A (fuel+1) U =
        (j, gain A U j) :: trace A fuel (U \ A j) := by
      simp [trace, hu, hb, Nat.ne_of_gt hgpos]
    obtain ⟨K, T, S, hS, hph, hca⟩ := ih (U \ A j) hres
    have hcases : gain A U j = 1 ∨ gain A U j = 2 ∨ gain A U j = 3 := by omega
    rcases hcases with hg | hg | hg
    · have huc : U.card = 1 := by
        by_contra hne
        have htwo : 2 ≤ U.card := by
          have hc := gain_le_card A U j
          omega
        have := best_gain_at_least_two A hp U htwo j hb
        omega
      have hrem : U \ A j = ∅ := Finset.card_eq_zero.mp (by omega)
      refine ⟨0, 0, 1, by omega, ?_, by omega⟩
      rw [heq, hrem]
      cases fuel <;> simp [trace, hg]
    · have hK : K = 0 := by
        by_contra hne
        have hm : 3 ∈ (trace A fuel (U \ A j)).map Prod.snd := by
          rw [hph]
          apply List.mem_append_left
          apply List.mem_append_left
          exact List.mem_replicate.mpr ⟨hne, rfl⟩
        obtain ⟨t, ht, ht3⟩ := List.mem_map.mp hm
        have hbound := tail_gain_le_best A fuel U j hb t ht
        omega
      subst K
      refine ⟨0, T+1, S, hS, ?_, by omega⟩
      rw [heq]
      simp only [List.map_cons, hg, hph, List.replicate_zero, List.nil_append]
      simp [List.replicate_succ, List.cons_append]
    · refine ⟨K+1, T, S, hS, ?_, by omega⟩
      rw [heq]
      simp only [List.map_cons, hg, hph]
      simp [List.replicate_succ, List.cons_append]

lemma count_triples_map {n : ℕ} (l : List (Fin n × ℕ)) :
    (l.filter (fun t => t.2 = 3)).length = (l.map Prod.snd).count 3 := by
  induction l with
  | nil => simp
  | cons t l ih =>
    by_cases ht : t.2 = 3
    · simp [ht, ih]
    · simp [ht, ih, Ne.symm ht]

/-- The phase count for the actual leftmost maximum-gain algorithm. -/
theorem greedy_phase_count : GreedyPhaseCount := by
  intro m n A hm hn hp
  obtain ⟨K, T, S, hS, hph, hmass⟩ :=
    trace_phase_mass A (exactPairs_feasible A hm hp) hn hp m univ (by simp)
  have hm' : m = 3*K + 2*T + S := by simpa using hmass
  have hK : tripleCount A = K := by
    unfold tripleCount greedyTrace
    rw [count_triples_map, hph]
    simp [List.count_replicate]
  have hpar : (m - 3*K) % 2 = S := by omega
  refine ⟨K, T, hK, ?_, trace_nodup A m univ, trace_triples_disjoint A hn m univ, ?_⟩
  · unfold greedyTrace
    simpa [hpar] using hph
  · have hlen := congrArg List.length hph
    simp only [List.length_map, List.length_append, List.length_replicate] at hlen
    unfold G greedyTrace
    omega

end ADG
