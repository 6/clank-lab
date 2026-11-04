import Family

namespace NWDigraph

theorem finRotate_val {m : ℕ} (i : Fin m) : ((finRotate m i : Fin m) : ℕ) = (i.val + 1) % m := by
  cases m with
  | zero => exact i.elim0
  | succ m =>
    rw [finRotate_apply, Fin.val_add]
    simp [Nat.add_mod]

theorem nocycle_of_lists {n : ℕ} (G : Digraph n) (a b d : Fin n)
    (h : ∀ s ∈ (List.finRange n).sublists, ∀ l ∈ s.permutations', a ∈ l → b ∈ l →
      ∃ k < l.length, G.adj (l.getD k d) (l.getD ((k + 1) % l.length) d) = false) :
    ¬ CycleThrough G a b := by
  rintro ⟨m, c, hinj, hadj, ⟨i, hi⟩, ⟨j, hj⟩⟩
  have hnd : (List.ofFn c).Nodup := List.nodup_ofFn.2 hinj
  have hp : (List.ofFn c).Perm ((List.finRange n).filter (fun x => decide (x ∈ List.ofFn c))) := by
    rw [List.perm_ext_iff_of_nodup hnd ((List.nodup_finRange n).filter _)]
    intro x; simp
  obtain ⟨k, hk, hf⟩ := h _ (List.mem_sublists.2 (List.filter_sublist))
    (List.ofFn c) (List.mem_permutations'.2 hp) (List.mem_ofFn.2 ⟨i, hi⟩) (List.mem_ofFn.2 ⟨j, hj⟩)
  have hlen : (List.ofFn c).length = m := by simp
  simp only [hlen] at hk hf
  have e1 : (List.ofFn c).getD k d = c ⟨k, hk⟩ := by
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_ofFn]
  have hk2 : (k + 1) % m < m := Nat.mod_lt _ (by omega)
  have e2 : (List.ofFn c).getD ((k + 1) % m) d = c (finRotate m ⟨k, hk⟩) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hk2), List.getElem_ofFn]
    congr 1; exact Fin.ext (by rw [finRotate_val])
  rw [e1, e2, hadj] at hf
  exact Bool.noConfusion hf

/-- In `G6` no cycle passes through both vertex 2 and vertex 3. -/
theorem G6_nocycle : ¬ CycleThrough G6 2 3 :=
  nocycle_of_lists G6 2 3 0 (by decide +kernel)

end NWDigraph
