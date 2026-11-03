import CD13.Core
import CD13.PairRecovery
import CD13.EventHistory

/-! Recovering directed two-letter projections from the final constructor state. -/
noncomputable section
namespace CD13.Recovery
open scoped Classical
universe u
variable {V : Type u} [Fintype V] {E : V → V → Prop}

/-- Fixed recovery obligation, including singleton projections. -/
def ProjectionEndpoint (E : V → V → Prop) : Prop :=
  ∀ u v : List V, RepeatProperty E u → RepeatProperty E v →
    run (E := E) u initialState = run v initialState →
    (∀ a, Trace.projection a a u = Trace.projection a a v) ∧
    (∀ a b, E a b → Trace.projection a b u = Trace.projection a b v)

/-- A saved outgoing-neighbor value, read from a tagged constructor term.
The default is used only on initial terms or terms with the wrong tag. -/
def childSnapshot (a b : V) (hab : E a b) (t : Sigma (Term E)) : Term E b :=
  if h : t.1 = a then
    match h ▸ t.2 with
    | .initial _ => .initial b
    | .node _ c => c ⟨b, hab⟩
  else .initial b

@[simp] theorem snapshot_event (a b : V) (hab : E a b) (s : TermState E) :
    childSnapshot a b hab (eventTerm a s) = s b := by
  simp [childSnapshot, eventTerm]

/-- Event terms at a specified vertex, in chronological order. -/
def eventsFor (a : V) (w : List V) (s : TermState E) : List (Sigma (Term E)) :=
  (eventTerms w s).filter (fun t => decide (t.1 = a))

theorem eventTerms_append (p q : List V) (s : TermState E) :
    eventTerms (p ++ q) s = eventTerms p s ++ eventTerms q (run p s) := by
  induction p generalizing s with
  | nil => rfl
  | cons a p ih => simp only [List.cons_append, eventTerms_cons, run_cons,
      ih, List.cons_append]

theorem eventsFor_append (a : V) (p q : List V) (s : TermState E) :
    eventsFor a (p ++ q) s = eventsFor a p s ++ eventsFor a q (run p s) := by
  simp only [eventsFor, eventTerms_append, List.filter_append]

@[simp] theorem eventsFor_nil (a : V) (s : TermState E) : eventsFor a [] s = [] := rfl

theorem eventsFor_snoc (a : V) (w : List V) (c : V) (s : TermState E) :
    eventsFor a (w ++ [c]) s =
      if c = a then eventsFor a w s ++ [eventTerm c (run w s)]
      else eventsFor a w s := by
  rw [eventsFor_append]
  by_cases h : c = a
  · simp [eventsFor, eventTerms, eventTerm, h]
  · simp [eventsFor, eventTerms, eventTerm, h]

theorem eventsFor_length (a : V) (w : List V) (s : TermState E) :
    (eventsFor a w s).length = (Trace.projection a a w).length := by
  induction w generalizing s with
  | nil => rfl
  | cons c w ih =>
    by_cases h : c = a
    · subst c
      simp [eventsFor, eventTerms_cons, eventTerm, Trace.projection_cons,
        ← ih (step a s)]
    · simp [eventsFor, eventTerms_cons, eventTerm, Trace.projection_cons, h,
        ← ih (step c s)]

theorem singleton_eq_of_length (a : V) (u v : List V)
    (h : (Trace.projection a a u).length = (Trace.projection a a v).length) :
    Trace.projection a a u = Trace.projection a a v := by
  have hr (w : List V) : Trace.projection a a w =
      List.replicate (Trace.projection a a w).length a := by
    apply List.eq_replicate_length.mpr
    intro b hb
    exact (show b ∈ w ∧ b = a by
      simpa only [Trace.projection, List.mem_filter, decide_eq_true_eq, or_self] using hb).2
  rw [hr u, hr v, h]

/-- Any function that correctly decodes a saved neighbor value into its
prefix event count recovers the complete chronological sample list. -/
theorem samples_of_snapshot (a b : V) (hab : E a b) (hne : a ≠ b)
    (w : List V) (version : Term E b → Nat)
    (hv : ∀ p q, w = p ++ q → version (run p initialState b) =
      (Trace.projection b b p).length) :
    (eventsFor a w initialState).map
        (fun t => version (childSnapshot a b hab t)) = PairRecovery.samples a b w := by
  induction w using List.reverseRecOn with
  | nil => simp [PairRecovery.samples]
  | append_singleton w c ih =>
    have hv' : ∀ p q, w = p ++ q → version (run p initialState b) =
        (Trace.projection b b p).length := by
      intro p q hp
      exact hv p (q ++ [c]) (by simp only [hp, List.append_assoc])
    rw [eventsFor_snoc, PairRecovery.samples_snoc a b hne]
    by_cases h : c = a
    · subst c
      simp only [ite_true, List.map_append, List.map_cons, List.map_nil,
        snapshot_event, ih hv']
      rw [hv w [a] rfl]
    · simp only [ite_eq_right h, ih hv']

/-- The complete combinatorial recovery step, with the event-history and
prefix-version facts explicit. The constructor event-history module must
supply those facts before this yields the target obligation. -/
theorem recover_of_history
    (noLoops : ∀ a, ¬ E a a) (u v : List V)
    (hh : ∀ a, eventsFor (E := E) a u initialState = eventsFor a v initialState)
    (version : (b : V) → List (Sigma (Term E)) → Term E b → Nat)
    (hu : ∀ b p q, u = p ++ q →
      version b (eventsFor b u initialState) (run p initialState b) =
        (Trace.projection b b p).length)
    (hv : ∀ b p q, v = p ++ q →
      version b (eventsFor b v initialState) (run p initialState b) =
        (Trace.projection b b p).length) :
    (∀ a, Trace.projection a a u = Trace.projection a a v) ∧
    (∀ a b, E a b → Trace.projection a b u = Trace.projection a b v) := by
  have single (a : V) : Trace.projection a a u = Trace.projection a a v := by
    apply singleton_eq_of_length
    rw [← eventsFor_length a u (initialState (E := E)),
      ← eventsFor_length a v (initialState (E := E)), hh a]
  refine ⟨single, ?_⟩
  intro a b hab
  have hne : a ≠ b := by
    intro h
    subst b
    exact noLoops a hab
  apply PairRecovery.projection_reconstruct a b hne u v
  · exact congrArg List.length (single b)
  · rw [← samples_of_snapshot a b hab hne u
        (version b (eventsFor b u initialState)) (hu b),
      ← samples_of_snapshot a b hab hne v
        (version b (eventsFor b v initialState)) (hv b), hh a, hh b]

theorem eventsFor_eq_eventsAt (a : V) (w : List V) :
    eventsFor (E := E) a w initialState = EventHistory.eventsAt a w := rfl

theorem countAt_eq_projection (a : V) (w : List V) :
    EventHistory.countAt a w = (Trace.projection a a w).length := by
  simp only [EventHistory.countAt, Trace.projection, or_self]

/-- Equal final constructor vectors recover every dependent projection.
No event-history or version-decoding premise remains. -/
theorem projection_endpoint (noLoops : ∀ a, ¬ E a a) : ProjectionEndpoint E := by
  intro u v hu hv hfinal
  apply recover_of_history noLoops u v
    (fun a => EventHistory.eventsAt_eq u v hu hv hfinal a) EventHistory.version
  · intro b p q hp
    subst u
    simpa only [eventsFor_eq_eventsAt, countAt_eq_projection] using
      EventHistory.version_prefix b p q hu
  · intro b p q hp
    subst v
    simpa only [eventsFor_eq_eventsAt, countAt_eq_projection] using
      EventHistory.version_prefix b p q hv

end CD13.Recovery
