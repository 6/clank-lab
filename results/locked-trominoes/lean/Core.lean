import Std

/-! Concrete grid semantics. There are no axioms about tile existence. -/
namespace LockedTromino

abbrev Cell := Int × Int
abbrev Region := Cell → Prop

def Adj (x y : Cell) : Prop :=
  (x.1 = y.1 ∧ (x.2 + 1 = y.2 ∨ y.2 + 1 = x.2)) ∨
  (x.2 = y.2 ∧ (x.1 + 1 = y.1 ∨ y.1 + 1 = x.1))

def Sub (A B : Region) : Prop := ∀ x, A x → B x
def Disjoint (A B : Region) : Prop := ∀ x, A x → B x → False
def Union (A B : Region) : Region := fun x => A x ∨ B x

def Triple (A : Region) : Prop :=
  ∃ a b c : Cell, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    ∀ x, A x ↔ x = a ∨ x = b ∨ x = c

inductive Walk (A : Region) : Cell → Cell → Prop
  | refl {x} : A x → Walk A x x
  | step {x y z} : Walk A x y → A z → Adj y z → Walk A x z

def Connected (A : Region) : Prop := ∀ x y, A x → A y → Walk A x y

def Tile (A : Region) : Prop := Triple A ∧ Connected A

def Rectangle (h w : Nat) : Region :=
  fun x => 0 ≤ x.1 ∧ x.1 < h ∧ 0 ≤ x.2 ∧ x.2 < w

/-- A tiling is literally a partition into connected three-element subsets. -/
def Tiling (R : Region) (T : Region → Prop) : Prop :=
  (∀ A, T A → Tile A) ∧
  (∀ x, R x ↔ ∃ A, T A ∧ A x) ∧
  (∀ A B, T A → T B → A ≠ B → Disjoint A B)

def Split (A B C D : Region) : Prop :=
  Tile C ∧ Tile D ∧ Disjoint C D ∧ Union C D = Union A B

def Rigid (A B : Region) : Prop :=
  ∀ C D, Split A B C D → (C = A ∧ D = B) ∨ (C = B ∧ D = A)

def PairwiseRigid (T : Region → Prop) : Prop :=
  ∀ A B, T A → T B → A ≠ B → Rigid A B

/-- The extra vertex of the metagraph is part of the definition. -/
def Locked (R : Region) (T : Region → Prop) : Prop :=
  Tiling R T ∧ PairwiseRigid T ∧ ∃ U, Tiling R U ∧ U ≠ T

theorem region_ext {A B : Region} (h : ∀ x, A x ↔ B x) : A = B :=
  funext fun x => propext (h x)

theorem triple_nonempty {A : Region} (h : Triple A) : ∃ x, A x := by
  obtain ⟨a, b, c, _, _, _, h⟩ := h
  exact ⟨a, (h a).mpr (Or.inl rfl)⟩

/-- Equal finite cardinality turns tile containment into equality. -/
theorem triple_sub_eq {A B : Region} (ha : Triple A) (hb : Triple B)
    (hs : Sub A B) : A = B := by
  obtain ⟨a, b, c, hab, hac, hbc, ha⟩ := ha
  obtain ⟨d, e, f, hde, hdf, hef, hb⟩ := hb
  apply region_ext
  intro x
  have aa := hs a ((ha a).mpr (Or.inl rfl))
  have ab := hs b ((ha b).mpr (Or.inr (Or.inl rfl)))
  have ac := hs c ((ha c).mpr (Or.inr (Or.inr rfl)))
  simp only [hb] at aa ab ac
  rw [ha, hb]
  grind

def NoEdges (A B : Region) : Prop :=
  ∀ x y, A x → B y → ¬ Adj x y

theorem adj_symm {x y : Cell} (h : Adj x y) : Adj y x := by
  unfold Adj at *
  grind

theorem walk_stays {A B C : Region} (hsub : Sub C (Union A B))
    (hne : NoEdges A B) {x y : Cell} (hx : A x) (p : Walk C x y) : A y := by
  induction p with
  | refl _ => exact hx
  | @step y z _ hz hyz ih =>
    rcases hsub z hz with ha | hb
    · exact ha
    · exact False.elim (hne y z ih hb hyz)

/-- A connected set inside two nonadjacent sets stays on one side. -/
theorem connected_subset_one {A B C : Region} (hc : Connected C)
    (hn : ∃ x, C x) (hs : Sub C (Union A B)) (he : NoEdges A B) :
    Sub C A ∨ Sub C B := by
  obtain ⟨x, hx⟩ := hn
  rcases hs x hx with ha | hb
  · exact Or.inl fun y hy => walk_stays hs he ha (hc x y hx hy)
  · apply Or.inr
    intro y hy
    have hs' : Sub C (Union B A) := fun z hz => (hs z hz).symm
    have he' : NoEdges B A := fun z w hz hw hed => he w z hw hz (adj_symm hed)
    exact walk_stays hs' he' hb (hc x y hx hy)

/-- Disconnected tile unions cannot support a two-tile move. -/
theorem noEdges_rigid {A B : Region} (ha : Tile A) (hb : Tile B)
    (_hd : Disjoint A B) (he : NoEdges A B) : Rigid A B := by
  intro C D ⟨hc, hd', hcd, hu⟩
  have hcs : Sub C (Union A B) := by
    intro x hx
    rw [← hu]
    exact Or.inl hx
  have hds : Sub D (Union A B) := by
    intro x hx
    rw [← hu]
    exact Or.inr hx
  have ce := connected_subset_one hc.2 (triple_nonempty hc.1) hcs he
  have de := connected_subset_one hd'.2 (triple_nonempty hd'.1) hds he
  rcases ce with ca | cb <;> rcases de with da | db
  · have ec := triple_sub_eq hc.1 ha.1 ca
    have ed := triple_sub_eq hd'.1 ha.1 da
    obtain ⟨x, hx⟩ := triple_nonempty ha.1
    exact False.elim (hcd x (ec ▸ hx) (ed ▸ hx))
  · exact Or.inl ⟨triple_sub_eq hc.1 ha.1 ca, triple_sub_eq hd'.1 hb.1 db⟩
  · exact Or.inr ⟨triple_sub_eq hc.1 hb.1 cb, triple_sub_eq hd'.1 ha.1 da⟩
  · have ec := triple_sub_eq hc.1 hb.1 cb
    have ed := triple_sub_eq hd'.1 hb.1 db
    obtain ⟨x, hx⟩ := triple_nonempty hb.1
    exact False.elim (hcd x (ec ▸ hx) (ed ▸ hx))

end LockedTromino
