import Small

namespace NWDigraph

theorem card_filter_fin (N : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    (Finset.univ.filter fun v : Fin N => Q v.val).card = ((Finset.range N).filter Q).card := by
  rw [← Finset.card_map Fin.valEmbedding]
  congr 1
  ext x
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a.isLt, ha⟩
  · rintro ⟨hx, hq⟩; exact ⟨⟨x, hx⟩, hq, rfl⟩

theorem F_adj (u : ℕ) (a b : Fin (u + 4)) : (F u).adj a b = true ↔ Fadj u a.val b.val := by
  simp [F]

/-- Out-degrees of `F u`. -/
def outF (u k : ℕ) : ℕ := if k < u then u + 3 else if k = u + 1 then 3 else 2

/-- In-degrees of `F u`. -/
def inF (u k : ℕ) : ℕ :=
  if k = 0 then u + 1 else if k < u then u - 1 else if k = u then u else if k = u + 1 then u + 3
  else u + 2

theorem F_outdeg (u : ℕ) (hu : 1 ≤ u) (v : Fin (u + 4)) : (F u).outdeg v = outF u v.val := by
  unfold Digraph.outdeg
  simp only [F_adj]
  rw [card_filter_fin (u + 4) (Fadj u v.val)]
  have hv := v.isLt
  unfold outF
  split_ifs with h1 h2
  · have : (Finset.range (u + 4)).filter (Fadj u v.val) = (Finset.range (u + 4)).erase v.val := by
      ext x; rw [Finset.mem_filter]; simp only [Finset.mem_range, Finset.mem_erase, Fadj]; omega
    rw [this, Finset.card_erase_of_mem (by simp [hv])]; simp
  · have : (Finset.range (u + 4)).filter (Fadj u v.val) = {0, u + 2, u + 3} := by
      ext x; rw [Finset.mem_filter]; simp only [Finset.mem_range, Finset.mem_insert,
        Finset.mem_singleton, Fadj]; omega
    rw [this]; rw [Finset.card_insert_of_notMem (by simp), Finset.card_pair (by omega)]
  · have hc : v.val = u ∨ v.val = u + 2 ∨ v.val = u + 3 := by omega
    rcases hc with hc | hc | hc
    · have : (Finset.range (u + 4)).filter (Fadj u v.val) = {0, u + 1} := by
        ext x; rw [Finset.mem_filter]; simp only [Finset.mem_range, Finset.mem_insert,
          Finset.mem_singleton, Fadj]; omega
      rw [this, Finset.card_pair (by omega)]
    · have : (Finset.range (u + 4)).filter (Fadj u v.val) = {u + 1, u + 3} := by
        ext x; rw [Finset.mem_filter]; simp only [Finset.mem_range, Finset.mem_insert,
          Finset.mem_singleton, Fadj]; omega
      rw [this, Finset.card_pair (by omega)]
    · have : (Finset.range (u + 4)).filter (Fadj u v.val) = {u + 1, u + 2} := by
        ext x; rw [Finset.mem_filter]; simp only [Finset.mem_range, Finset.mem_insert,
          Finset.mem_singleton, Fadj]; omega
      rw [this, Finset.card_pair (by omega)]

theorem F_indeg (u : ℕ) (hu : 1 ≤ u) (v : Fin (u + 4)) : (F u).indeg v = inF u v.val := by
  unfold Digraph.indeg
  simp only [F_adj]
  rw [card_filter_fin (u + 4) (fun a => Fadj u a v.val)]
  have hv := v.isLt
  unfold inF
  split_ifs with h1 h2 h3 h4
  · have : (Finset.range (u + 4)).filter (fun a => Fadj u a v.val) =
        (Finset.range (u + 2)).erase 0 := by
      ext x; rw [Finset.mem_filter]; simp only [Finset.mem_range, Finset.mem_erase, Fadj]; omega
    rw [this, Finset.card_erase_of_mem (by simp)]; simp
  · have : (Finset.range (u + 4)).filter (fun a => Fadj u a v.val) =
        (Finset.range u).erase v.val := by
      ext x; rw [Finset.mem_filter]; simp only [Finset.mem_range, Finset.mem_erase, Fadj]; omega
    rw [this, Finset.card_erase_of_mem (by simp; omega)]; simp
  · have : (Finset.range (u + 4)).filter (fun a => Fadj u a v.val) = Finset.range u := by
      ext x; rw [Finset.mem_filter]; simp only [Finset.mem_range, Fadj]; omega
    rw [this]; simp
  · have : (Finset.range (u + 4)).filter (fun a => Fadj u a v.val) =
        (Finset.range (u + 4)).erase (u + 1) := by
      ext x; rw [Finset.mem_filter]; simp only [Finset.mem_range, Finset.mem_erase, Fadj]; omega
    rw [this, Finset.card_erase_of_mem (by simp)]; simp
  · have hc : v.val = u + 2 ∨ v.val = u + 3 := by omega
    have : (Finset.range (u + 4)).filter (fun a => Fadj u a v.val) =
        ((Finset.range (u + 4)).erase u).erase v.val := by
      ext x; rw [Finset.mem_filter]; simp only [Finset.mem_range, Finset.mem_erase, Fadj]; omega
    rw [this, Finset.card_erase_of_mem (by simp; omega), Finset.card_erase_of_mem (by simp)]
    simp

theorem cnt_out (u : ℕ) (hu : 1 ≤ u) (P : ℕ → Prop) [DecidablePred P] :
    cnt P (F u).outdeg =
      (if P (u + 3) then u else 0) + (if P 3 then 1 else 0) + (if P 2 then 3 else 0) := by
  unfold cnt
  simp only [F_outdeg u hu]
  rw [card_filter_fin (u + 4) (fun k => P (outF u k)), Finset.card_filter]
  simp only [Finset.sum_range_succ]
  have h : ∑ k ∈ Finset.range u, (if P (outF u k) then 1 else 0) = if P (u + 3) then u else 0 := by
    rw [Finset.sum_congr rfl (g := fun _ => if P (u + 3) then 1 else 0)
      (fun k hk => by simp [outF, Finset.mem_range.1 hk])]
    split_ifs <;> simp
  have e1 : outF u u = 2 := by simp [outF]
  have e2 : outF u (u + 1) = 3 := by simp [outF]
  have e3 : outF u (u + 2) = 2 := by simp [outF]
  have e4 : outF u (u + 3) = 2 := by simp [outF]
  rw [h, e1, e2, e3, e4]
  split_ifs <;> omega

theorem cnt_in (u : ℕ) (hu : 1 ≤ u) (P : ℕ → Prop) [DecidablePred P] :
    cnt P (F u).indeg =
      (if P (u + 1) then 1 else 0) + (if P (u - 1) then u - 1 else 0) + (if P u then 1 else 0) +
      (if P (u + 3) then 1 else 0) + (if P (u + 2) then 2 else 0) := by
  unfold cnt
  simp only [F_indeg u hu]
  rw [card_filter_fin (u + 4) (fun k => P (inF u k)), Finset.card_filter]
  obtain ⟨a, rfl⟩ : ∃ a, u = a + 1 := ⟨u - 1, by omega⟩
  rw [Finset.sum_range_succ']
  simp only [Finset.sum_range_succ]
  have h : ∑ k ∈ Finset.range a, (if P (inF (a + 1) (k + 1)) then 1 else 0) =
      if P (a + 1 - 1) then a else 0 := by
    rw [Finset.sum_congr rfl (g := fun _ => if P (a + 1 - 1) then 1 else 0)
      (fun k hk => by have := Finset.mem_range.1 hk; simp [inF]; split_ifs <;> omega)]
    split_ifs <;> simp
  have e0 : inF (a + 1) 0 = a + 1 + 1 := by simp [inF]
  have e1 : inF (a + 1) (a + 1) = a + 1 := by simp [inF]
  have e2 : inF (a + 1) (a + 1 + 1) = a + 1 + 3 := by simp [inF]
  have e3 : inF (a + 1) (a + 2 + 1) = a + 1 + 2 := by simp [inF]
  have e4 : inF (a + 1) (a + 3 + 1) = a + 1 + 2 := by simp [inF]
  rw [h, e0, e1, e2, e3, e4]
  simp only [Nat.add_sub_cancel]
  split_ifs <;> omega

set_option linter.deprecated false in
theorem F_nw (u : ℕ) (hu : 4 ≤ u) : NWHyp (F u) := by
  apply nw_of_count
  intro i h1 h2
  unfold NWCount
  simp only [cnt_out u (by omega), cnt_in u (by omega)]
  rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ 5 ≤ i) with h | h | h | h | h
  all_goals simp (disch := omega) only [if_pos, if_neg]
  all_goals omega

theorem F_sc (u : ℕ) (hu : 1 ≤ u) : StronglyConnected (F u) := by
  have step : ∀ a b : Fin (u + 4), Fadj u a.val b.val →
      Relation.ReflTransGen (fun x y => (F u).adj x y = true) a b :=
    fun a b h => Relation.ReflTransGen.single ((F_adj u a b).2 h)
  obtain ⟨w, hw⟩ : ∃ w : Fin (u + 4), w.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  have to0 : ∀ v : Fin (u + 4), Relation.ReflTransGen (fun x y => (F u).adj x y = true) v w := by
    intro v
    have hv := v.isLt
    by_cases h0 : v.val = 0
    · rw [show v = w from Fin.ext (by omega)]
    · by_cases h1 : v.val < u + 2
      · exact step v w (by simp only [Fadj]; omega)
      · refine (step v ⟨u + 1, by omega⟩ (by show Fadj u v.val (u + 1); simp only [Fadj]; omega)).trans
          (step ⟨u + 1, by omega⟩ w (by show Fadj u (u + 1) w.val; simp only [Fadj, true_and]; omega))
  have from0 : ∀ v : Fin (u + 4), Relation.ReflTransGen (fun x y => (F u).adj x y = true) w v := by
    intro v
    by_cases h0 : v.val = 0
    · rw [show v = w from Fin.ext (by omega)]
    · exact step w v (by simp only [Fadj]; omega)
  exact fun a b => (to0 a).trans (from0 b)

open Fin.NatCast in
/-- The successor map of a Hamilton cycle is injective, follows arcs, and has no proper nonempty
closed set. -/
theorem ham_closed {n : ℕ} {G : Digraph n} (h : HasHamCycle G) :
    ∃ f : Fin n → Fin n, Function.Injective f ∧ (∀ v, G.adj v (f v) = true) ∧
      ∀ S : Fin n → Prop, (∀ v, S v → S (f v)) → (∃ v, S v) → ∀ v, S v := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun v => c (finRotate n (c.symm v)), ?_, ?_, ?_⟩
  · intro a b hab
    simpa using hab
  · intro v
    simpa using hc (c.symm v)
  · intro S hS ⟨v0, hv0⟩ v
    obtain ⟨k0, rfl⟩ := c.surjective v0
    cases n with
    | zero => exact k0.elim0
    | succ m =>
      have hT : ∀ j : ℕ, S (c (k0 + (j : Fin (m + 1)))) := by
        intro j
        induction j with
        | zero => simpa using hv0
        | succ j ih =>
          have := hS _ ih
          simpa [finRotate_apply, add_assoc] using this
      obtain ⟨k, rfl⟩ := c.surjective v
      have : k = k0 + (((k - k0 : Fin (m + 1)) : ℕ) : Fin (m + 1)) := by
        rw [Fin.cast_val_eq_self]; abel
      rw [this]
      exact hT _

theorem F_noham (u : ℕ) : ¬ HasHamCycle (F u) := by
  intro h
  obtain ⟨f, hinj, hadj, hclosed⟩ := ham_closed h
  obtain ⟨s, hs⟩ : ∃ s : Fin (u + 4), s.val = u := ⟨⟨u, by omega⟩, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : Fin (u + 4), r.val = u + 2 := ⟨⟨u + 2, by omega⟩, rfl⟩
  have hne : ∀ v : Fin (u + 4), v.val ≠ u → (f v).val ≠ (f s).val := by
    intro v hv hfv
    have e : v = s := hinj (Fin.ext hfv)
    exact hv (by rw [e]; exact hs)
  have hs' := (F_adj u s (f s)).1 (hadj s)
  have hfs := (f s).isLt
  have key := fun v : Fin (u + 4) => (F_adj u v (f v)).1 (hadj v)
  have fin : ∀ v : Fin (u + 4), (f v).val < u + 4 := fun v => (f v).isLt
  have fin' : ∀ v : Fin (u + 4), v.val < u + 4 := fun v => v.isLt
  have hs2 : (f s).val = u + 1 ∨ (f s).val = 0 := by
    unfold Fadj at hs'; omega
  rcases hs2 with h1 | h1
  · have := hclosed (fun v => u + 2 ≤ v.val) (by
      intro v hv
      have := key v
      have := hne v (by omega)
      have := fin v
      have := fin' v
      unfold Fadj at *
      omega) ⟨r, by omega⟩ s
    omega
  · have := hclosed (fun v => u + 1 ≤ v.val) (by
      intro v hv
      have := key v
      have := hne v (by omega)
      have := fin v
      have := fin' v
      unfold Fadj at *
      omega) ⟨r, by omega⟩ s
    omega

open Fin.NatCast in
/-- A subset of positions of a cycle closed under successor is everything. -/
theorem rot_closed {m : ℕ} (T : Fin m → Prop) (h : ∀ i, T i → T (finRotate m i)) (i0 : Fin m)
    (h0 : T i0) : ∀ i, T i := by
  cases m with
  | zero => exact i0.elim0
  | succ m =>
    have hT : ∀ j : ℕ, T (i0 + (j : Fin (m + 1))) := by
      intro j
      induction j with
      | zero => simpa using h0
      | succ j ih => simpa [finRotate_apply, add_assoc] using h _ ih
    intro i
    have : i = i0 + (((i - i0 : Fin (m + 1)) : ℕ) : Fin (m + 1)) := by
      rw [Fin.cast_val_eq_self]; abel
    rw [this]
    exact hT _

theorem F_nocycle (u : ℕ) (s r : Fin (u + 4)) (hs : s.val = u) (hr : r.val = u + 2 ∨ r.val = u + 3) :
    ¬ CycleThrough (F u) s r := by
  rintro ⟨m, c, hinj, hadj, ⟨is, his⟩, ⟨ir, hir⟩⟩
  have hne : ∀ i, i ≠ is → (c (finRotate m i)).val ≠ (c (finRotate m is)).val := by
    intro i hi h
    exact hi (by simpa using hinj (Fin.ext h))
  have hs' := (F_adj u _ _).1 (hadj is)
  rw [his] at hs'
  have key := fun i => (F_adj u _ _).1 (hadj i)
  have fin := fun i => (c (finRotate m i)).isLt
  have fin' := fun i => (c i).isLt
  have hcs : ∀ i, (c i).val = u → i = is := fun i h => hinj (Fin.ext (by rw [his]; omega))
  have hs2 : (c (finRotate m is)).val = u + 1 ∨ (c (finRotate m is)).val = 0 := by
    have := (c (finRotate m is)).isLt
    unfold Fadj at hs'; omega
  rcases hs2 with h1 | h1
  · have := rot_closed (fun i => u + 2 ≤ (c i).val) (by
      intro i hi
      have := key i
      have := hne i (fun e => by have := hcs i; subst e; omega)
      have := fin i
      have := fin' i
      unfold Fadj at *
      omega) ir (by omega) is
    omega
  · have := rot_closed (fun i => u + 1 ≤ (c i).val) (by
      intro i hi
      have := key i
      have := hne i (fun e => by have := hcs i; subst e; omega)
      have := fin i
      have := fin' i
      unfold Fadj at *
      omega) ir (by omega) is
    omega

theorem F_kot3 (u : ℕ) (hu : 4 ≤ u) :
    (u + 4) % 2 = 0 → (F u).dplus ((u + 4) / 2) ≥ (u + 4) / 2 ∨
      (F u).dminus ((u + 4) / 2) ≥ (u + 4) / 2 := by
  intro he
  have hj : (u + 4) / 2 - 1 < u + 4 := by omega
  unfold Digraph.dplus Digraph.dminus
  rw [ge_iff_le, getD_ge_iff _ _ hj, ge_iff_le, getD_ge_iff _ _ hj]
  rw [cnt_out u (by omega), cnt_in u (by omega)]
  split_ifs <;> omega

end NWDigraph
