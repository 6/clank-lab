import CD13.Model

/-! Event-size and exact subterm-coverage core. -/
noncomputable section
namespace CD13
open scoped Classical
universe u
variable {V : Type u} [Fintype V] {E : V → V → Prop}

/-- Every saved child snapshot has size at most its current coordinate. -/
def Coherent (s : TermState E) : Prop :=
  ∀ i (c : (j : {j // E i j}) → Term E j.val), s i = Term.node i c →
    ∀ j, Term.size (c j) ≤ Term.size (s j.val)

def SizeLE (s t : TermState E) : Prop := ∀ i, Term.size (s i) ≤ Term.size (t i)

@[simp] theorem coherent_initial : Coherent ((initialState (E := E)) : TermState E) := by
  intro i c h
  cases h

theorem coherent_step_le {s : TermState E} (hs : Coherent s) (a : V) :
    SizeLE s (step a s) := by
  intro i
  by_cases h : i = a
  · subst i
    rw [step_same]
    cases hi : s a with
    | initial => simp [Term.size]
    | node a c =>
      simp only [Term.size_node]
      exact Nat.add_le_add_left (Finset.sum_le_sum (fun j _ => hs a c hi j)) 1
  · rw [step_other a i s h]

theorem coherent_step {s : TermState E} (hs : Coherent s) (a : V) :
    Coherent (step a s) := by
  have hle := coherent_step_le hs a
  intro i c hc j
  by_cases h : i = a
  · subst i
    rw [step_same] at hc
    have hchildren := (Term.node.inj hc)
    subst c
    exact hle j.val
  · rw [step_other a i s h] at hc
    exact (hs i c hc j).trans (hle j.val)

theorem coherent_run (w : List V) {s : TermState E} (hs : Coherent s) :
    Coherent (run w s) := by
  induction w generalizing s with
  | nil => exact hs
  | cons a w ih => exact ih (coherent_step hs a)

theorem coherent_run_le (w : List V) {s : TermState E} (hs : Coherent s) :
    SizeLE s (run w s) := by
  induction w generalizing s with
  | nil => exact fun _ => le_rfl
  | cons a w ih =>
    intro i
    exact (coherent_step_le hs a i).trans (ih (coherent_step hs a) i)

theorem run_absent (w : List V) (s : TermState E) (a : V) (ha : a ∉ w) :
    run w s a = s a := by
  induction w generalizing s with
  | nil => rfl
  | cons b w ih =>
    simp only [List.mem_cons, not_or] at ha
    rw [run_cons, ih _ ha.2, step_other b a s ha.1]

/-- Last occurrence split, so the suffix has no further producer updates. -/
theorem split_last {a : V} {w : List V} (h : a ∈ w) :
    ∃ p q, w = p ++ a :: q ∧ a ∉ q := by
  induction w with
  | nil => simp at h
  | cons b w ih =>
    by_cases hw : a ∈ w
    · obtain ⟨p, q, hp, hq⟩ := ih hw
      exact ⟨b :: p, q, by simp [hp], hq⟩
    · have hab : a = b := (List.mem_cons.mp h).resolve_right hw
      subst b
      exact ⟨[], w, rfl, hw⟩

theorem repeat_prefix {p q : List V} (h : RepeatProperty E (p ++ q)) :
    RepeatProperty E p := by
  intro a l m r hp
  apply h a l m (r ++ q)
  simp only [hp, List.append_assoc]

theorem repeat_suffix {p q : List V} (h : RepeatProperty E (p ++ q)) :
    RepeatProperty E q := by
  intro a l m r hq
  apply h a (p ++ l) m r
  simp only [hq, List.append_assoc]

theorem run_prefix_size_le (p q : List V) (i : V) :
    Term.size (run p (initialState (E := E)) i) ≤ Term.size (run (p ++ q) (initialState (E := E)) i) := by
  rw [run_append]
  exact coherent_run_le q (coherent_run p coherent_initial) i

/-- Every event strictly increases its producer coordinate in a repeat word.
The proof uses chronological induction, rather than an assumed once-only
consumer condition or a graph rank argument. -/
theorem strict_update (w : List V) (a : V) (h : RepeatProperty E (w ++ [a])) :
    Term.size (run w (initialState (E := E)) a) <
      Term.size (step a (run w (initialState (E := E))) a) := by
  induction w using (measure (fun w : List V => w.length)).wf.induction generalizing a with
  | h w ih =>
    by_cases ha : a ∈ w
    · obtain ⟨p, q, hw, hq⟩ := split_last ha
      obtain ⟨b, hbq, hab⟩ := (h a p q [] (by simp [hw, List.append_assoc])).2
      obtain ⟨r, s, hqs⟩ := List.mem_iff_append.mp hbq
      have hpre : RepeatProperty E ((p ++ a :: r) ++ [b]) := by
        apply repeat_prefix (q := s ++ [a])
        simpa [hw, hqs, List.append_assoc] using h
      have hlen : (p ++ a :: r).length < w.length := by
        simp [hw, hqs]
      have hb := ih (p ++ a :: r) hlen b hpre
      have hbefore := run_prefix_size_le (E := E) p (a :: r) b
      have hafter := run_prefix_size_le (E := E) ((p ++ a :: r) ++ [b]) s b
      simp only [run_append, run_cons, run_nil] at hafter
      have hchild : Term.size (run p (initialState (E := E)) b) < Term.size (run w (initialState (E := E)) b) := by
        have hmid := hbefore.trans_lt hb
        simp only [run_append, run_cons, run_nil] at hmid
        simpa [hw, hqs, run_append, List.append_assoc] using hmid.trans_le hafter
      have hchildren : ∀ j : {j // E a j},
          Term.size (run p (initialState (E := E)) j.val) ≤ Term.size (run w (initialState (E := E)) j.val) := by
        intro j
        simpa [hw] using run_prefix_size_le (E := E) p (a :: q) j.val
      have hold : run w (initialState (E := E)) a = Term.node a (fun j => run p (initialState (E := E)) j.val) := by
        rw [hw, run_append, run_cons, run_absent q _ a hq, step_same]
      rw [hold, step_same]
      simp only [Term.size_node]
      exact Nat.add_lt_add_left
        (Finset.sum_lt_sum (fun j _ => hchildren j)
          ⟨⟨b, hab⟩, Finset.mem_univ _, hchild⟩) 1
    · rw [run_absent w (initialState (E := E)) a ha, step_same]
      exact Term.size_node_pos _ _

/-- The term made by the next event, with its vertex tag. -/
def eventTerm (a : V) (s : TermState E) : Sigma (Term E) :=
  ⟨a, Term.node a (fun j => s j.val)⟩

/-- Two occurrences at one vertex produce different terms, ordered by size. -/
theorem strict_event_pair (p m q : List V) (a : V)
    (h : RepeatProperty E (p ++ a :: (m ++ a :: q))) :
    Term.size (eventTerm a (run p (initialState (E := E)))).2 <
      Term.size (eventTerm a (run (p ++ a :: m) (initialState (E := E)))).2 := by
  have hp : RepeatProperty E ((p ++ a :: m) ++ [a]) := by
    apply repeat_prefix (q := q)
    simpa [List.append_assoc] using h
  have hle := run_prefix_size_le (E := E) (p ++ [a]) m a
  have hlt := strict_update (p ++ a :: m) a hp
  have hle' : Term.size (eventTerm a (run p (initialState (E := E)))).2 ≤
      Term.size (run (p ++ a :: m) (initialState (E := E)) a) := by
    simpa [run_append, run_cons, run_nil, step_same, eventTerm] using hle
  exact hle'.trans_lt (by simpa [step_same, eventTerm] using hlt)

/-- A reflexive occurrence, following zero or more child links. -/
inductive Subterm : Sigma (Term E) → Sigma (Term E) → Prop
  | refl (t) : Subterm t t
  | child {i : V} (c : (j : {j // E i j}) → Term E j.val)
      (j : {j // E i j}) {t} (h : Subterm t ⟨j.val, c j⟩) :
      Subterm t ⟨i, Term.node i c⟩

namespace Subterm
theorem trans {a b c : Sigma (Term E)} (hab : Subterm a b) (hbc : Subterm b c) :
    Subterm a c := by
  induction hbc with
  | refl => exact hab
  | child c j _ ih => exact .child c j (ih hab)

theorem initial {t : Sigma (Term E)} {i : V} (h : Subterm t ⟨i, Term.initial i⟩) :
    t = ⟨i, Term.initial i⟩ := by
  cases h
  rfl

theorem node_cases {t : Sigma (Term E)} {i : V}
    {c : (j : {j // E i j}) → Term E j.val}
    (h : Subterm t ⟨i, Term.node i c⟩) :
    t = ⟨i, Term.node i c⟩ ∨ ∃ j, Subterm t ⟨j.val, c j⟩ := by
  cases h with
  | refl => exact Or.inl rfl
  | child c j h => exact Or.inr ⟨j, h⟩
end Subterm

def Seen (s : TermState E) (t : Sigma (Term E)) : Prop :=
  ∃ i, Subterm t ⟨i, s i⟩

def Noninitial (t : Sigma (Term E)) : Prop := t.2 ≠ Term.initial t.1

theorem seen_step_cases (a : V) (s : TermState E) (t : Sigma (Term E))
    (h : Seen (step a s) t) : t = eventTerm a s ∨ Seen s t := by
  obtain ⟨i, hi⟩ := h
  by_cases hia : i = a
  · subst i
    rw [step_same] at hi
    rcases hi.node_cases with ht | ⟨j, hj⟩
    · exact Or.inl ht
    · exact Or.inr ⟨j.val, hj⟩
  · rw [step_other a i s hia] at hi
    exact Or.inr ⟨i, hi⟩

theorem seen_run_cases (w : List V) (s : TermState E) (t : Sigma (Term E))
    (h : Seen (run w s) t) : t ∈ eventTerms w s ∨ Seen s t := by
  induction w generalizing s with
  | nil => exact Or.inr h
  | cons a w ih =>
    rcases ih (step a s) h with hm | hs
    · exact Or.inl (List.mem_cons_of_mem _ hm)
    · rcases seen_step_cases a s t hs with he | hs
      · exact Or.inl (List.mem_cons.mpr (Or.inl he))
      · exact Or.inr hs

theorem seen_initial_not_noninitial {t : Sigma (Term E)}
    (h : Seen (initialState (E := E)) t) : ¬ Noninitial t := by
  obtain ⟨i, hi⟩ := h
  have ht := hi.initial
  subst t
  exact fun h => h rfl

theorem seen_noninitial_created (w : List V) {t : Sigma (Term E)}
    (hn : Noninitial t) (h : Seen (run w (initialState (E := E))) t) :
    t ∈ eventTerms w (initialState (E := E)) := by
  exact (seen_run_cases w _ t h).resolve_right (fun hs => seen_initial_not_noninitial hs hn)

theorem mem_eventTerms_iff (w : List V) (s : TermState E) (t : Sigma (Term E)) :
    t ∈ eventTerms w s ↔ ∃ p a q, w = p ++ a :: q ∧ t = eventTerm a (run p s) := by
  induction w generalizing s with
  | nil => simp [eventTerms]
  | cons b w ih =>
    constructor
    · intro h
      rcases List.mem_cons.mp h with ht | ht
      · exact ⟨[], b, w, rfl, ht⟩
      · obtain ⟨p, a, q, hw, ht⟩ := (ih (step b s)).mp ht
        exact ⟨b :: p, a, q, by simp [hw], ht⟩
    · rintro ⟨p, a, q, hw, ht⟩
      cases p with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        exact List.mem_cons.mpr (Or.inl ht)
      | cons c p =>
        simp only [List.cons_append, List.cons.injEq] at hw
        obtain ⟨rfl, hw⟩ := hw
        apply List.mem_cons_of_mem
        exact (ih (step b s)).mpr ⟨p, a, q, hw, ht⟩

theorem split_first {a : V} {w : List V} (h : a ∈ w) :
    ∃ p q, w = p ++ a :: q ∧ a ∉ p := by
  induction w with
  | nil => simp at h
  | cons b w ih =>
    by_cases hab : a = b
    · subst b
      exact ⟨[], w, rfl, by simp⟩
    · obtain ⟨p, q, hp, hq⟩ := ih ((List.mem_cons.mp h).resolve_left hab)
      exact ⟨b :: p, q, by simp [hp], by simp [hab, hq]⟩

/-- An event survives as a subterm. If its producer fires again, follow an
intervening incoming-neighbor consumer. The recursive event is later in time;
it can itself fire any number of times. -/
theorem event_seen_final (q : List V) (p : List V) (a : V)
    (h : RepeatProperty E (p ++ a :: q)) :
    Seen (run (p ++ a :: q) (initialState (E := E)))
      (eventTerm a (run p (initialState (E := E)))) := by
  induction q using (measure (fun q : List V => q.length)).wf.induction generalizing p a with
  | h q ih =>
    by_cases ha : a ∈ q
    · obtain ⟨m, r, hq, hm⟩ := split_first ha
      obtain ⟨b, hbm, hba⟩ := (h a p m r (by simp [hq, List.append_assoc])).1
      obtain ⟨l, s, hms⟩ := List.mem_iff_append.mp hbm
      have hal : a ∉ l := by
        intro hal
        apply hm
        simp [hms, hal]
      have hlen : (s ++ a :: r).length < q.length := by
        simp [hq, hms]
        omega
      have heq : p ++ a :: q = (p ++ a :: l) ++ b :: (s ++ a :: r) := by
        simp [hq, hms, List.append_assoc]
      have hnew : RepeatProperty E ((p ++ a :: l) ++ b :: (s ++ a :: r)) := by
        rw [← heq]
        exact h
      obtain ⟨i, hi⟩ := ih (s ++ a :: r) hlen (p ++ a :: l) b hnew
      have hcoord : run (p ++ a :: l) (initialState (E := E)) a =
          Term.node a (fun j => run p (initialState (E := E)) j.val) := by
        rw [run_append, run_cons, run_absent l _ a hal, step_same]
      have hsub : Subterm (eventTerm a (run p (initialState (E := E))))
          (eventTerm b (run (p ++ a :: l) (initialState (E := E)))) := by
        apply Subterm.child _ ⟨a, hba⟩
        rw [hcoord]
        exact Subterm.refl _
      refine ⟨i, ?_⟩
      rw [heq]
      exact hsub.trans hi
    · refine ⟨a, ?_⟩
      rw [run_append, run_cons, run_absent q _ a ha, step_same]
      exact Subterm.refl _

theorem created_seen_final (w : List V) (h : RepeatProperty E w)
    {t : Sigma (Term E)} (ht : t ∈ eventTerms w (initialState (E := E))) :
    Seen (run w (initialState (E := E))) t := by
  obtain ⟨p, a, q, hw, rfl⟩ := (mem_eventTerms_iff w _ t).mp ht
  subst w
  exact event_seen_final q p a h

theorem created_noninitial (w : List V) {t : Sigma (Term E)}
    (ht : t ∈ eventTerms w (initialState (E := E))) : Noninitial t := by
  obtain ⟨p, a, q, _, rfl⟩ := (mem_eventTerms_iff w _ t).mp ht
  intro hn
  cases hn

/-- Exact subterm coverage in both directions, for every repeat word. -/
theorem exact_subterm_coverage (w : List V) (h : RepeatProperty E w)
    (t : Sigma (Term E)) :
    t ∈ eventTerms w (initialState (E := E)) ↔
      Noninitial t ∧ Seen (run w (initialState (E := E))) t := by
  constructor
  · intro ht
    exact ⟨created_noninitial w ht, created_seen_final w h ht⟩
  · rintro ⟨hn, hs⟩
    exact seen_noninitial_created w hn hs

end CD13
