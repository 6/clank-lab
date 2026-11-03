import Mathlib

/-! Definitions. Colours are indexed 0..3;
adding one gives exactly the palette {1,2,3,4} and preserves differences. -/
namespace Antony24

abbrev Colour := Fin 4

def diff (a b : Colour) : ℕ := Nat.dist a.val b.val

def IsGraceful (G : SimpleGraph V) (c : V → Colour) : Prop :=
  (∀ ⦃u v⦄, G.Adj u v → c u ≠ c v) ∧
  (∀ ⦃v u w⦄, G.Adj v u → G.Adj v w → u ≠ w →
    diff (c v) (c u) ≠ diff (c v) (c w))

def Graceful4 (G : SimpleGraph V) : Prop := ∃ c, IsGraceful G c

def PMC (G : SimpleGraph V) : Prop :=
  ∃ side : V → Bool, ∀ v, ∃! w, G.Adj v w ∧ side v ≠ side w

/-- Exactly three distinct neighbours, with no finiteness or nonempty assumption. -/
def Cubic (G : SimpleGraph V) : Prop :=
  ∀ v, ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    ∀ w, G.Adj v w ↔ w = a ∨ w = b ∨ w = c

abbrev Dart (G : SimpleGraph V) := {p : V × V // G.Adj p.1 p.2}

def Dart.rev {G : SimpleGraph V} (d : Dart G) : Dart G :=
  ⟨(d.val.2, d.val.1), d.property.symm⟩

@[simp] theorem Dart.rev_rev {G : SimpleGraph V} (d : Dart G) : d.rev.rev = d := by
  cases d; rfl

abbrev SubVertex (G : SimpleGraph V) := V ⊕ Dart G

/-- One internal vertex per directed incidence: the edge uv becomes
u -- (u,v) -- (v,u) -- v, exactly two fresh vertices per unordered edge. -/
def S2 (G : SimpleGraph V) : SimpleGraph (SubVertex G) where
  Adj x y := match x, y with
    | .inl _, .inl _ => False
    | .inl v, .inr d => v = d.val.1
    | .inr d, .inl v => v = d.val.1
    | .inr d, .inr e => e = d.rev
  symm := by
    intro x y h
    cases x <;> cases y
    · exact h
    · exact h
    · exact h
    · dsimp at h ⊢
      rw [h, Dart.rev_rev]
  loopless := by
    intro x
    cases x with
    | inl v => exact id
    | inr d =>
      intro h
      have q := congrArg (fun e : Dart G => e.val.1) h
      exact G.ne_of_adj d.property q

/-- Tagged dependent disjoint union, allowing empty indices and fibres. -/
def Union {I : Type*} {V : I → Type*} (G : ∀ i, SimpleGraph (V i)) :
    SimpleGraph (Sigma V) where
  Adj x y := ∃ h : x.1 = y.1, (G x.1).Adj x.2 (h ▸ y.2)
  symm := by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨h, a⟩
    cases h
    exact ⟨rfl, a.symm⟩
  loopless := by
    rintro ⟨i, x⟩ ⟨h, a⟩
    exact (G i).loopless x a

end Antony24
