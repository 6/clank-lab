import Lemmas

namespace NWDigraph

variable {n : ℕ}

/-- One round of forward / backward reachability. -/
def fstep (G : Digraph n) (S : Finset (Fin n)) : Finset (Fin n) :=
  S ∪ Finset.univ.filter fun w => ∃ v ∈ S, G.adj v w = true

def bstep (G : Digraph n) (S : Finset (Fin n)) : Finset (Fin n) :=
  S ∪ Finset.univ.filter fun w => ∃ v ∈ S, G.adj w v = true

theorem fstep_iter (G : Digraph n) (a : Fin n) (k : ℕ) :
    ∀ v ∈ (fstep G)^[k] {a}, Relation.ReflTransGen (fun x y => G.adj x y = true) a v := by
  induction k with
  | zero => intro v hv; simp at hv; subst hv; exact .refl
  | succ k ih =>
    intro v hv
    rw [Function.iterate_succ_apply'] at hv
    simp only [fstep, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rcases hv with hv | ⟨x, hx, hxv⟩
    · exact ih v hv
    · exact (ih x hx).tail hxv

theorem bstep_iter (G : Digraph n) (a : Fin n) (k : ℕ) :
    ∀ v ∈ (bstep G)^[k] {a}, Relation.ReflTransGen (fun x y => G.adj x y = true) v a := by
  induction k with
  | zero => intro v hv; simp at hv; subst hv; exact .refl
  | succ k ih =>
    intro v hv
    rw [Function.iterate_succ_apply'] at hv
    simp only [bstep, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rcases hv with hv | ⟨x, hx, hxv⟩
    · exact ih v hv
    · exact Relation.ReflTransGen.head hxv (ih x hx)

theorem sc_of_iter (G : Digraph n) (a : Fin n) (k : ℕ)
    (hf : ∀ v, v ∈ (fstep G)^[k] {a}) (hb : ∀ v, v ∈ (bstep G)^[k] {a}) : StronglyConnected G :=
  fun u v => (bstep_iter G a k u (hb u)).trans (fstep_iter G a k v (hf v))

theorem G6_sc : StronglyConnected G6 :=
  sc_of_iter G6 0 6 (by decide +kernel) (by decide +kernel)

theorem G7_sc : StronglyConnected G7 :=
  sc_of_iter G7 0 7 (by decide +kernel) (by decide +kernel)

theorem G6_nw : NWHyp G6 :=
  nw_of_count_range (by decide +kernel)

theorem G7_nw : NWHyp G7 :=
  nw_of_count_range (by decide +kernel)

theorem noham_of_perms {m : ℕ} (G : Digraph (m + 1))
    (h : ∀ a : Fin (m + 1), ∀ l ∈ ((List.finRange (m + 1)).erase a).permutations',
      ∃ k : Fin (m + 1),
        G.adj ((a :: l).getD k 0) ((a :: l).getD (finRotate (m + 1) k) 0) = false) :
    ¬ HasHamCycle G := by
  rintro ⟨c, hc⟩
  have hp : (List.ofFn c).Perm (List.finRange (m + 1)) := by
    rw [List.perm_ext_iff_of_nodup (List.nodup_ofFn.2 c.injective) (List.nodup_finRange _)]
    intro a
    simp only [List.mem_ofFn, List.mem_finRange, iff_true]
    exact ⟨c.symm a, by simp⟩
  rw [List.ofFn_succ, List.cons_perm_iff_perm_erase] at hp
  obtain ⟨k, hk⟩ := h (c 0) _ (List.mem_permutations'.2 hp.2)
  have e : ∀ j : Fin (m + 1), (c 0 :: List.ofFn fun i : Fin m => c i.succ).getD j 0 = c j := by
    intro j
    have := List.ofFn_succ (f := c)
    rw [← this, List.getD_eq_getElem _ _ (by have := j.isLt; simp; omega), List.getElem_ofFn]
  rw [e, e, hc k] at hk
  exact Bool.noConfusion hk

theorem G6_noham : ¬ HasHamCycle G6 :=
  noham_of_perms G6 (by decide +kernel)

theorem G7_noham : ¬ HasHamCycle G7 :=
  noham_of_perms G7 (by decide +kernel)

end NWDigraph
