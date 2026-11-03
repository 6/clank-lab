import Std

/-!
Trace reconstruction by two-letter projections.

The argument is the standard trace-monoid
projection argument (Cori–Perrin/Duboc), proved directly here. The main
statement includes repeated projection letters, which supply singleton
counts. No graph finiteness is needed in this module.
-/
namespace CD13.Trace

variable {V : Type u}

/-- Words related by adjacent independent commutations. -/
inductive Equiv (I : V → V → Prop) : List V → List V → Prop
  | nil : Equiv I [] []
  | cons (a : V) {u v} : Equiv I u v → Equiv I (a :: u) (a :: v)
  | swap (a b : V) (w : List V) : I a b → Equiv I (a :: b :: w) (b :: a :: w)
  | trans {u v w} : Equiv I u v → Equiv I v w → Equiv I u w

/-- Keep occurrences of either named letter; the names may coincide. -/
def projection [DecidableEq V] (a b : V) (w : List V) : List V :=
  w.filter (fun x => decide (x = a ∨ x = b))

/-- The exact endpoint of this supporting module, before its proof lemmas. -/
def Reconstruction : Prop :=
  ∀ (I : V → V → Prop) [DecidableEq V],
    (∀ a, ¬ I a a) → (∀ a b, I a b → I b a) →
    ∀ u v : List V,
      (∀ a b, ¬ I a b → projection a b u = projection a b v) → Equiv I u v

 theorem refl (I : V → V → Prop) (w : List V) : Equiv I w w := by
  induction w with
  | nil => exact .nil
  | cons a w ih => exact .cons a ih

 theorem projection_cons [DecidableEq V] (a b c : V) (w : List V) :
    projection a b (c :: w) =
      if c = a ∨ c = b then c :: projection a b w else projection a b w := by
  simp [projection, List.filter_cons]

 theorem swap_projection [DecidableEq V] (I : V → V → Prop)
    (hirr : ∀ a, ¬ I a a) (hsym : ∀ a b, I a b → I b a)
    (a b x y : V) (w : List V) (hab : I a b) (hxy : ¬ I x y) :
    projection x y (a :: b :: w) = projection x y (b :: a :: w) := by
  have habne : a ≠ b := fun h => hirr b (h ▸ hab)
  have hboth : ¬ ((a = x ∨ a = y) ∧ (b = x ∨ b = y)) := by
    rintro ⟨ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact hirr _ hab
    · exact hxy hab
    · exact hxy (hsym _ _ hab)
    · exact hirr _ hab
  simp only [projection_cons]
  split <;> split <;> simp_all

 theorem preserves_projection [DecidableEq V] (I : V → V → Prop)
    (hirr : ∀ a, ¬ I a a) (hsym : ∀ a b, I a b → I b a)
    {u v : List V} (h : Equiv I u v) (x y : V) (hxy : ¬ I x y) :
    projection x y u = projection x y v := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [projection_cons]; rw [ih]
  | swap a b w hab => exact swap_projection I hirr hsym a b x y w hab hxy
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

 theorem pull_head [DecidableEq V] (I : V → V → Prop)
    (hirr : ∀ a, ¬ I a a) (a : V) (v : List V)
    (h : ∀ b, ¬ I a b → ∃ t, projection a b v = a :: t) :
    ∃ t, Equiv I (a :: t) v := by
  induction v with
  | nil =>
      obtain ⟨t, ht⟩ := h a (hirr a)
      simp [projection] at ht
  | cons b v ih =>
      by_cases hab : a = b
      · subst b
        exact ⟨v, refl I _⟩
      · have hi : I a b := by
          apply Classical.byContradiction
          intro hn
          obtain ⟨t, ht⟩ := h b hn
          have hb : b = a := by
            have := ht
            simp only [projection_cons, or_true, ite_true] at this
            exact (List.cons.inj this).1
          exact hab hb.symm
        have hv : ∀ c, ¬ I a c → ∃ t, projection a c v = a :: t := by
          intro c hc
          have hbc : b ≠ c := by
            intro heq
            exact hc (heq ▸ hi)
          obtain ⟨t, ht⟩ := h c hc
          exact ⟨t, by simpa [projection_cons, Ne.symm hab, hbc] using ht⟩
        obtain ⟨t, ht⟩ := ih hv
        exact ⟨b :: t, .trans (.swap a b t hi) (.cons b ht)⟩

 theorem reconstruct [DecidableEq V] (I : V → V → Prop)
    (hirr : ∀ a, ¬ I a a) (hsym : ∀ a b, I a b → I b a)
    (u v : List V)
    (h : ∀ a b, ¬ I a b → projection a b u = projection a b v) : Equiv I u v := by
  induction u generalizing v with
  | nil =>
      cases v with
      | nil => exact .nil
      | cons b v =>
          have hb := h b b (hirr b)
          simp [projection] at hb
  | cons a u ih =>
      have hv : ∀ b, ¬ I a b → ∃ t, projection a b v = a :: t := by
        intro b hb
        exact ⟨projection a b u, by simpa [projection_cons] using (h a b hb).symm⟩
      obtain ⟨t, ht⟩ := pull_head I hirr a v hv
      have hu : ∀ x y, ¬ I x y → projection x y u = projection x y t := by
        intro x y hxy
        have hp := (h x y hxy).trans (preserves_projection I hirr hsym ht x y hxy).symm
        simp only [projection_cons] at hp
        split at hp
        · exact (List.cons.inj hp).2
        · exact hp
      exact .trans (.cons a (ih t hu)) ht

 theorem reconstruction : @Reconstruction V := by
  intro I inst hirr hsym u v h
  exact reconstruct I hirr hsym u v h

end CD13.Trace
