import Statement

namespace NWDigraph

variable {n : ℕ}

theorem sorted_ge_iff (L : List ℕ) (hs : L.Pairwise (· ≤ ·)) (j : ℕ) (hj : j < L.length) (m : ℕ) :
    m ≤ L[j] ↔ L.countP (fun x => decide (x < m)) ≤ j := by
  rw [List.pairwise_iff_getElem] at hs
  constructor
  · intro h
    have e : L.countP (fun x => decide (x < m)) = (L.take j).countP (fun x => decide (x < m)) +
        (L.drop j).countP (fun x => decide (x < m)) := by
      rw [← List.countP_append, List.take_append_drop]
    have h0 : (L.drop j).countP (fun x => decide (x < m)) = 0 := by
      rw [List.countP_eq_zero]
      intro a ha
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ha
      rw [List.getElem_drop]
      have hk' : k < L.length - j := by simpa using hk
      have : L[j] ≤ L[j + k] := by
        rcases Nat.eq_zero_or_pos k with rfl | hpos
        · simp
        · exact hs j (j + k) hj (by omega) (by omega)
      simpa using by omega
    have h1 := List.countP_le_length (p := fun x => decide (x < m)) (l := L.take j)
    have h2 : (L.take j).length ≤ j := by simp
    omega
  · intro h
    by_contra hlt
    push Not at hlt
    have h1 : (L.take (j + 1)).countP (fun x => decide (x < m)) = (L.take (j + 1)).length := by
      rw [List.countP_eq_length]
      intro a ha
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ha
      rw [List.getElem_take]
      have hk' : k < j + 1 := by simp at hk; omega
      have : L[k] ≤ L[j] := by
        rcases Nat.lt_or_ge k j with hkj | hkj
        · exact hs k j _ _ hkj
        · have : k = j := by omega
          subst this; exact le_refl _
      simpa using by omega
    have h2 := (List.take_sublist (j + 1) L).countP_le (p := fun x => decide (x < m))
    have h3 : (L.take (j + 1)).length = j + 1 := by simp; omega
    omega

theorem sortedDegrees_perm (d : Fin n → ℕ) : (sortedDegrees d).Perm (List.ofFn d) :=
  List.mergeSort_perm _ _

theorem sortedDegrees_sorted (d : Fin n → ℕ) : (sortedDegrees d).Pairwise (· ≤ ·) := by
  have := List.pairwise_mergeSort' (· ≤ ·) (List.ofFn d)
  simpa [sortedDegrees] using this

theorem sortedDegrees_length (d : Fin n → ℕ) : (sortedDegrees d).length = n := by
  rw [(sortedDegrees_perm d).length_eq]; simp

/-- Number of vertices whose degree satisfies `P`. -/
def cnt (P : ℕ → Prop) [DecidablePred P] (d : Fin n → ℕ) : ℕ :=
  (Finset.univ.filter fun v => P (d v)).card

theorem countP_sorted (d : Fin n → ℕ) (m : ℕ) :
    (sortedDegrees d).countP (fun x => decide (x < m)) = cnt (· < m) d := by
  rw [(sortedDegrees_perm d).countP_eq]
  rw [List.ofFn_eq_map, List.countP_map, cnt, Finset.card_def, Finset.filter_val, Fin.univ_def]
  simp [List.countP_eq_length_filter, Function.comp_def]

theorem getD_ge_iff (d : Fin n → ℕ) (j : ℕ) (hj : j < n) (m : ℕ) :
    m ≤ (sortedDegrees d).getD j 0 ↔ cnt (· < m) d ≤ j := by
  have hl : j < (sortedDegrees d).length := by rw [sortedDegrees_length]; exact hj
  rw [List.getD_eq_getElem _ _ hl, sorted_ge_iff _ (sortedDegrees_sorted d) j hl, countP_sorted]

theorem cnt_add (m : ℕ) (d : Fin n → ℕ) : cnt (· < m) d + cnt (fun x => m ≤ x) d = n := by
  unfold cnt
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun v => d v < m)
  simpa using this

/-- The Nash-Williams hypothesis in counting form. -/
def NWCount (G : Digraph n) (i : ℕ) : Prop :=
  (cnt (· < i + 1) G.outdeg ≤ i - 1 ∨ i + 1 ≤ cnt (fun x => n - i ≤ x) G.indeg) ∧
  (cnt (· < i + 1) G.indeg ≤ i - 1 ∨ i + 1 ≤ cnt (fun x => n - i ≤ x) G.outdeg)

instance (G : Digraph n) (i : ℕ) : Decidable (NWCount G i) := by
  unfold NWCount; infer_instance

theorem low_iff (d : Fin n → ℕ) (i : ℕ) (h1 : 1 ≤ i) (h2 : 2 * i < n) :
    i + 1 ≤ (sortedDegrees d).getD (i - 1) 0 ↔ cnt (· < i + 1) d ≤ i - 1 :=
  getD_ge_iff d (i - 1) (by omega) (i + 1)

theorem high_iff (d : Fin n → ℕ) (i : ℕ) (h1 : 1 ≤ i) (h2 : 2 * i < n) :
    n - i ≤ (sortedDegrees d).getD (n - i - 1) 0 ↔ i + 1 ≤ cnt (fun x => n - i ≤ x) d := by
  rw [getD_ge_iff d (n - i - 1) (by omega) (n - i)]
  have := cnt_add (n - i) d
  omega

theorem nw_of_count {G : Digraph n} (h : ∀ i, 1 ≤ i → 2 * i < n → NWCount G i) : NWHyp G := by
  intro i h1 h2
  obtain ⟨hA, hB⟩ := h i h1 h2
  constructor
  · rcases hA with hA | hA
    · exact Or.inl ((low_iff G.outdeg i h1 h2).2 hA)
    · exact Or.inr ((high_iff G.indeg i h1 h2).2 hA)
  · rcases hB with hB | hB
    · exact Or.inl ((low_iff G.indeg i h1 h2).2 hB)
    · exact Or.inr ((high_iff G.outdeg i h1 h2).2 hB)

theorem nw_of_count_range {G : Digraph n}
    (h : ∀ i ∈ Finset.range n, 1 ≤ i → 2 * i < n → NWCount G i) : NWHyp G :=
  nw_of_count fun i h1 h2 => h i (Finset.mem_range.2 (by omega)) h1 h2

end NWDigraph
