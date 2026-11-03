import Std

/-!
Elementary HK cancellation and reduced representatives.
Elementary cancellations follow
Aragona–D'Andrea, Lemma 2.1. No confluence theorem is used.
-/
namespace CD13.Reduction

variable {V : Type u}

/-- A congruence on the free monoid of words. -/
structure WordCongruence (V : Type u) where
  Rel : List V → List V → Prop
  refl : ∀ w, Rel w w
  symm : ∀ {u v}, Rel u v → Rel v u
  trans : ∀ {u v w}, Rel u v → Rel v w → Rel u w
  append : ∀ {u v x y}, Rel u v → Rel x y → Rel (u ++ x) (v ++ y)

/-- Every interval between repeated letters has a neighbor of each direction.
The condition includes all repeated pairs, hence in particular consecutive ones. -/
def RepeatProperty (E : V → V → Prop) (w : List V) : Prop :=
  ∀ a p m q, w = p ++ a :: (m ++ a :: q) →
    (∃ b, b ∈ m ∧ E a b) ∧ (∃ b, b ∈ m ∧ E b a)

/-- Relations needed from the HK presentation, with no extra identifications. -/
structure HKRelations (C : WordCongruence V) (E : V → V → Prop) : Prop where
  idem : ∀ a, C.Rel [a, a] [a]
  commute : ∀ a b, a ≠ b → ¬ E a b → ¬ E b a → C.Rel [a, b] [b, a]
  triangleOut : ∀ a b, E a b → C.Rel [a, b, a] [a, b]
  triangleIn : ∀ a b, E a b → C.Rel [b, a, b] [a, b]

/-- Fixed reduction endpoint, stated before its supporting proof lemmas. -/
def ReductionEndpoint : Prop :=
  ∀ (C : WordCongruence V) (E : V → V → Prop), HKRelations C E →
    ∀ w, ∃ v, C.Rel w v ∧ RepeatProperty E v ∧ v.length ≤ w.length

namespace WordCongruence

 theorem left (C : WordCongruence V) (p : List V) {u v}
    (h : C.Rel u v) : C.Rel (p ++ u) (p ++ v) :=
  C.append (C.refl p) h

 theorem right (C : WordCongruence V) {u v} (h : C.Rel u v)
    (q : List V) : C.Rel (u ++ q) (v ++ q) :=
  C.append h (C.refl q)

/-- Reverse words to exchange the two elementary cancellation laws. -/
def reverse (C : WordCongruence V) : WordCongruence V where
  Rel u v := C.Rel u.reverse v.reverse
  refl w := C.refl w.reverse
  symm h := C.symm h
  trans h k := C.trans h k
  append h k := by simpa using C.append k h

end WordCongruence

 theorem absorb_right (C : WordCongruence V) (a : V)
    (idem : C.Rel [a, a] [a]) (m : List V)
    (h : ∀ b, b ∈ m → C.Rel [a, b, a] [a, b]) :
    C.Rel (a :: (m ++ [a])) (a :: m) := by
  induction m with
  | nil => simpa using idem
  | cons b m ih =>
      have hb := h b (by simp)
      have hm := ih (fun c hc => h c (by simp [hc]))
      have h₁ := C.right (C.symm hb) (m ++ [a])
      have h₂ := C.left [a, b] hm
      have h₃ := C.right hb m
      exact C.trans (by simpa using h₁)
        (C.trans (by simpa using h₂) (by simpa using h₃))

 theorem absorb_left (C : WordCongruence V) (a : V)
    (idem : C.Rel [a, a] [a]) (m : List V)
    (h : ∀ b, b ∈ m → C.Rel [a, b, a] [b, a]) :
    C.Rel (a :: (m ++ [a])) (m ++ [a]) := by
  have hi : C.reverse.Rel [a, a] [a] := by simpa [WordCongruence.reverse] using idem
  have hm : ∀ b, b ∈ m.reverse → C.reverse.Rel [a, b, a] [a, b] := by
    intro b hb
    simpa [WordCongruence.reverse] using h b (by simpa using hb)
  have hx := absorb_right C.reverse a hi m.reverse hm
  simpa [WordCongruence.reverse, List.reverse_cons, List.reverse_append] using hx

 theorem cancel_no_incoming (C : WordCongruence V) (E : V → V → Prop)
    (H : HKRelations C E) (a : V) (m : List V)
    (h : ∀ b, b ∈ m → ¬ E b a) :
    C.Rel (a :: (m ++ [a])) (a :: m) := by
  apply absorb_right C a (H.idem a) m
  intro b hb
  by_cases heq : a = b
  · subst b
    simpa using C.right (H.idem a) [a]
  · by_cases he : E a b
    · exact H.triangleOut a b he
    · have hc := H.commute a b heq he (h b hb)
      have h₁ := C.right hc [a]
      have h₂ := C.left [b] (H.idem a)
      exact C.trans (by simpa using h₁)
        (C.trans (by simpa using h₂) (C.symm hc))

 theorem cancel_no_outgoing (C : WordCongruence V) (E : V → V → Prop)
    (H : HKRelations C E) (a : V) (m : List V)
    (h : ∀ b, b ∈ m → ¬ E a b) :
    C.Rel (a :: (m ++ [a])) (m ++ [a]) := by
  apply absorb_left C a (H.idem a) m
  intro b hb
  by_cases heq : a = b
  · subst b
    simpa using C.right (H.idem a) [a]
  · by_cases he : E b a
    · exact H.triangleIn b a he
    · have hc := H.commute a b heq (h b hb) he
      have h₁ := C.right hc [a]
      have h₂ := C.left [b] (H.idem a)
      exact C.trans (by simpa using h₁) (by simpa using h₂)

 theorem reduce (C : WordCongruence V) (E : V → V → Prop)
    (H : HKRelations C E) (w : List V) :
    ∃ v, C.Rel w v ∧ RepeatProperty E v ∧ v.length ≤ w.length := by
  have aux : ∀ n, ∀ w : List V, w.length = n →
      ∃ v, C.Rel w v ∧ RepeatProperty E v ∧ v.length ≤ w.length := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro w hn
      by_cases hw : RepeatProperty E w
      · exact ⟨w, C.refl w, hw, Nat.le_refl _⟩
      · have bad : ∃ a p m q, w = p ++ a :: (m ++ a :: q) ∧
            (¬ (∃ b, b ∈ m ∧ E a b) ∨ ¬ (∃ b, b ∈ m ∧ E b a)) := by
          apply Classical.byContradiction
          intro hb
          apply hw
          intro a p m q heq
          have hn' : ¬ (¬ (∃ b, b ∈ m ∧ E a b) ∨ ¬ (∃ b, b ∈ m ∧ E b a)) := by
            intro hbad
            exact hb ⟨a, p, m, q, heq, hbad⟩
          exact ⟨Classical.byContradiction (fun h => hn' (Or.inl h)),
            Classical.byContradiction (fun h => hn' (Or.inr h))⟩
        obtain ⟨a, p, m, q, heq, hbad⟩ := bad
        have shorter : ∃ z, C.Rel w z ∧ z.length < w.length := by
          rcases hbad with hout | hin
          · have hm : ∀ b, b ∈ m → ¬ E a b := by
              intro b hb he
              exact hout ⟨b, hb, he⟩
            refine ⟨p ++ m ++ a :: q, ?_, ?_⟩
            · have hc := C.right (C.left p (cancel_no_outgoing C E H a m hm)) q
              simpa [heq, List.append_assoc] using hc
            · simp only [heq, List.length_append, List.length_cons]
              omega
          · have hm : ∀ b, b ∈ m → ¬ E b a := by
              intro b hb he
              exact hin ⟨b, hb, he⟩
            refine ⟨p ++ a :: (m ++ q), ?_, ?_⟩
            · have hc := C.right (C.left p (cancel_no_incoming C E H a m hm)) q
              simpa [heq, List.append_assoc] using hc
            · simp only [heq, List.length_append, List.length_cons]
              omega
        obtain ⟨z, hz, hlen⟩ := shorter
        obtain ⟨v, hv, hr, hl⟩ := ih z.length (by omega) z rfl
        exact ⟨v, C.trans hz hv, hr, Nat.le_trans hl (Nat.le_of_lt hlen)⟩
  exact aux w.length w rfl

 theorem repeat_reverse (E : V → V → Prop) (w : List V)
    (h : RepeatProperty E w) : RepeatProperty E w.reverse := by
  intro a p m q heq
  have hw : w = q.reverse ++ a :: (m.reverse ++ a :: p.reverse) := by
    have hx := congrArg List.reverse heq
    simpa [List.reverse_cons, List.reverse_append, List.append_assoc] using hx
  obtain ⟨⟨b, hb, he⟩, ⟨c, hc, hf⟩⟩ := h a q.reverse m.reverse p.reverse hw
  exact ⟨⟨b, by simpa using hb, he⟩, ⟨c, by simpa using hc, hf⟩⟩

 theorem reductionEndpoint : @ReductionEndpoint V := by
  intro C E H w
  exact reduce C E H w

end CD13.Reduction
