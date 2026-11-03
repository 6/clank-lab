import CD13.Core
import Mathlib.Data.List.Sort

/-! Ordered constructor histories and prefix versions. -/
noncomputable section
namespace CD13.EventHistory
open scoped Classical
universe u
variable {V : Type u} [Fintype V] {E : V → V → Prop}

def eventsAt (a : V) (w : List V) : List (Sigma (Term E)) :=
  (eventTerms w (initialState (E := E))).filter (fun t => decide (t.1 = a))

def countAt (a : V) (w : List V) : Nat :=
  (w.filter (fun x => decide (x = a))).length

def version (b : V) (history : List (Sigma (Term E))) (t : Term E b) : Nat :=
  if t = Term.initial b then 0 else history.idxOf ⟨b, t⟩ + 1

omit [Fintype V] in
theorem eventTerms_append (p q : List V) (s : TermState E) :
    eventTerms (p ++ q) s = eventTerms p s ++ eventTerms q (run p s) := by
  induction p generalizing s with
  | nil => rfl
  | cons a p ih => simp only [List.cons_append, eventTerms_cons, run_cons, ih]

omit [Fintype V] in
theorem eventsAt_append (a : V) (p q : List V) :
    eventsAt (E := E) a (p ++ q) = eventsAt a p ++
      (eventTerms q (run p (initialState (E := E)))).filter (fun t => decide (t.1 = a)) := by
  simp only [eventsAt, eventTerms_append, List.filter_append]

private theorem pairwise_from (b : V) (p q : List V)
    (h : RepeatProperty E (p ++ q)) :
    (eventTerms q (run p (initialState (E := E)))).Pairwise
      (fun x y => x.1 = b → y.1 = b → Term.size x.2 < Term.size y.2) := by
  induction q generalizing p with
  | nil => exact List.Pairwise.nil
  | cons a q ih =>
    rw [eventTerms_cons, List.pairwise_cons]
    constructor
    · intro t ht hab htb
      change a = b at hab
      subst a
      obtain ⟨m, c, r, hq, ht⟩ := (mem_eventTerms_iff q _ t).mp ht
      have hcb : c = b := by simpa [ht, eventTerm] using htb
      subst c
      subst t
      have hh : RepeatProperty E (p ++ b :: (m ++ b :: r)) := by simpa [hq] using h
      have hs : run m (step b (run p (initialState (E := E)))) =
          run (p ++ b :: m) (initialState (E := E)) := by simp [run_append]
      change Term.size (eventTerm b (run p (initialState (E := E)))).2 < _
      rw [hs]
      exact strict_event_pair p m r b hh
    · have hh : RepeatProperty E ((p ++ [a]) ++ q) := by simpa [List.append_assoc] using h
      simpa [run_append] using ih (p ++ [a]) hh

theorem eventsAt_strict (a : V) (w : List V) (h : RepeatProperty E w) :
    (eventsAt (E := E) a w).Pairwise (fun x y => Term.size x.2 < Term.size y.2) := by
  apply List.pairwise_filter.mpr
  simpa only [List.nil_append, run_nil, decide_eq_true_eq] using pairwise_from a [] w h

theorem eventsAt_nodup (a : V) (w : List V) (h : RepeatProperty E w) :
    (eventsAt (E := E) a w).Nodup :=
  (eventsAt_strict a w h).imp (fun {x y} hxy heq => by subst y; omega)

theorem eventsAt_eq (u v : List V) (hu : RepeatProperty E u) (hv : RepeatProperty E v)
    (hfinal : run u (initialState (E := E)) = run v (initialState (E := E))) (a : V) :
    eventsAt (E := E) a u = eventsAt a v := by
  let R : Sigma (Term E) → Sigma (Term E) → Prop := fun x y => Term.size x.2 < Term.size y.2
  have : Std.Antisymm R := ⟨fun x y hxy hyx => by dsimp [R] at *; omega⟩
  have : Std.Irrefl R := ⟨fun x hxx => by dsimp [R] at *; omega⟩
  apply List.Pairwise.eq_of_mem_iff (r := R) (eventsAt_strict a u hu) (eventsAt_strict a v hv)
  intro t
  simp only [eventsAt, List.mem_filter, decide_eq_true_eq]
  rw [exact_subterm_coverage u hu, exact_subterm_coverage v hv, hfinal]

omit [Fintype V] in
@[simp] theorem countAt_nil (a : V) : countAt a [] = 0 := rfl

omit [Fintype V] in
@[simp] theorem countAt_append (a : V) (p q : List V) :
    countAt a (p ++ q) = countAt a p + countAt a q := by
  simp [countAt, List.filter_append]

omit [Fintype V] in
@[simp] theorem countAt_cons (a c : V) (w : List V) :
    countAt a (c :: w) = (if c = a then 1 else 0) + countAt a w := by
  by_cases hc : c = a <;> simp [countAt, hc, Nat.add_comm]

omit [Fintype V] in
theorem countAt_eq_zero (a : V) (w : List V) (h : a ∉ w) : countAt a w = 0 := by
  apply congrArg List.length (List.filter_eq_nil_iff.mpr ?_)
  intro x hx hxa
  have hxa : x = a := of_decide_eq_true hxa
  subst x
  exact h hx

omit [Fintype V] in
private theorem filtered_length (a : V) (w : List V) (s : TermState E) :
    ((eventTerms w s).filter (fun t => decide (t.1 = a))).length = countAt a w := by
  induction w generalizing s with
  | nil => rfl
  | cons c w ih =>
    by_cases hc : c = a <;> simp [eventTerms, hc, ih, countAt_cons, Nat.add_comm]

omit [Fintype V] in
@[simp] theorem eventsAt_length (a : V) (w : List V) :
    (eventsAt (E := E) a w).length = countAt a w := filtered_length a w _

omit [Fintype V] in
theorem eventsAt_snoc (a c : V) (p : List V) :
    eventsAt (E := E) a (p ++ [c]) = eventsAt a p ++
      (if c = a then [eventTerm c (run p (initialState (E := E)))] else []) := by
  rw [eventsAt_append]
  by_cases hc : c = a <;> simp [eventTerms, eventTerm, hc]

omit [Fintype V] in
@[simp] theorem version_initial (b : V) (history : List (Sigma (Term E))) :
    version b history (Term.initial b) = 0 := by simp [version]

/-- The coordinate at a prefix is either initial or its unique last producer event;
its position in the full ordered history recovers the prefix event count. -/
theorem version_prefix (b : V) (p r : List V) (h : RepeatProperty E (p ++ r)) :
    version b (eventsAt (E := E) b (p ++ r)) (run p (initialState (E := E)) b) =
      countAt b p := by
  by_cases hb : b ∈ p
  · obtain ⟨l, q, hp, hq⟩ := split_last hb
    have hpre : RepeatProperty E (l ++ [b]) := by
      apply repeat_prefix (q := q ++ r)
      simpa [hp, List.append_assoc] using h
    have hn := eventsAt_nodup b (l ++ [b]) hpre
    rw [eventsAt_snoc] at hn
    simp only [ite_true] at hn
    have hnot : eventTerm b (run l (initialState (E := E))) ∉ eventsAt b l := by
      intro hm
      exact (List.nodup_append.mp hn).2.2 _ hm _ (by simp) rfl
    have hs : run p (initialState (E := E)) b =
        Term.node b (fun j => run l (initialState (E := E)) j.val) := by
      rw [hp, run_append, run_cons, run_absent q _ b hq, step_same]
    have hhist : eventsAt (E := E) b (p ++ r) = eventsAt b l ++
        eventTerm b (run l (initialState (E := E))) ::
          (eventTerms (q ++ r) (step b (run l (initialState (E := E))))).filter
            (fun t => decide (t.1 = b)) := by
      simp only [hp, List.append_assoc, List.cons_append, eventsAt_append,
        eventTerms_cons, List.filter_cons, decide_true, ite_true, eventTerm]
    rw [hs, version, ite_eq_right (by intro he; cases he)]
    change (eventsAt (E := E) b (p ++ r)).idxOf
      (eventTerm b (run l (initialState (E := E)))) + 1 = _
    rw [hhist, List.idxOf_append_of_notMem hnot]
    simp only [List.idxOf_cons_self, Nat.add_zero, eventsAt_length]
    rw [hp, countAt_append, countAt_cons]
    simp [countAt_eq_zero b q hq]
  · rw [run_absent p (initialState (E := E)) b hb]
    simpa [initialState, version] using (countAt_eq_zero b p hb).symm

theorem prefix_count_eq (b : V) (p r q s : List V)
    (hu : RepeatProperty E (p ++ r)) (hv : RepeatProperty E (q ++ s))
    (hhistory : eventsAt (E := E) b (p ++ r) = eventsAt b (q ++ s))
    (hcurrent : run p (initialState (E := E)) b = run q (initialState (E := E)) b) :
    countAt b p = countAt b q := by
  rw [← version_prefix b p r hu, hhistory, hcurrent, version_prefix b q s hv]

end CD13.EventHistory
