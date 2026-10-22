import Strips

namespace LockedTromino

/-- The coordinate-list interface uses ordinary lists, interpreted as cell sets. -/
def Cells (xs : List Cell) : Region := fun x => x ∈ xs

def TreeEdges (a b c : Cell) : Prop :=
  (Adj a b ∧ Adj a c) ∨ (Adj a b ∧ Adj b c) ∨ (Adj a c ∧ Adj b c)

instance (x y : Cell) : Decidable (Adj x y) := by unfold Adj; infer_instance
instance (a b c : Cell) : Decidable (TreeEdges a b c) := by unfold TreeEdges; infer_instance

theorem connected_three_neighbor {a b c : Cell} (hab : a ≠ b) (hac : a ≠ c)
    (hc : Connected (Three a b c)) : Adj a b ∨ Adj a c := by
  by_cases he : Adj a b ∨ Adj a c
  · exact he
  · have hn : NoEdges (fun x => x = a) (fun x => x = b ∨ x = c) := by
      intro x y hx hy hxy
      subst x
      rcases hy with rfl | rfl
      · exact he (Or.inl hxy)
      · exact he (Or.inr hxy)
    have hsub : Sub (Three a b c) (Union (fun x => x = a) (fun x => x = b ∨ x = c)) :=
      fun _ hx => hx
    rcases connected_subset_one hc ⟨a,Or.inl rfl⟩ hsub hn with h | h
    · have hb := h b (Or.inr (Or.inl rfl))
      exact False.elim (hab hb.symm)
    · have ha := h a (Or.inl rfl)
      exact False.elim (ha.elim hab hac)

theorem connected_three_tree {a b c : Cell} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hc : Connected (Three a b c)) : TreeEdges a b c := by
  have habc := connected_three_neighbor hab hac hc
  have hperm : Three a b c = Three b a c := by apply region_ext; intro x; simp [Three]; grind
  have hbac := connected_three_neighbor hab.symm hbc (hperm ▸ hc)
  have hperm' : Three a b c = Three c a b := by apply region_ext; intro x; simp [Three]; grind
  have hcab := connected_three_neighbor hac.symm hbc.symm (hperm' ▸ hc)
  unfold TreeEdges
  have hsymm : Adj b a → Adj a b := fun h => adj_symm h
  have hsymm' : Adj c a → Adj a c := fun h => adj_symm h
  have hsymm'' : Adj c b → Adj b c := fun h => adj_symm h
  grind

theorem tree_connected {a b c : Cell} (he : TreeEdges a b c) : Connected (Three a b c) := by
  rcases he with ⟨hab,hac⟩ | ⟨hab,hbc⟩ | ⟨hac,hbc⟩
  · have hperm : Three b a c = Three a b c := by apply region_ext; intro x; simp [Three]; grind
    exact hperm ▸ connected_three_chain b a c (adj_symm hab) hac
  · exact connected_three_chain a b c hab hbc
  · have hperm : Three a c b = Three a b c := by apply region_ext; intro x; simp [Three]; grind
    exact hperm ▸ connected_three_chain a c b hac (adj_symm hbc)

/-- A computable predicate equivalent to being a three-cell connected tile. -/
def tileCheck : List Cell → Bool
  | [a,b,c] => decide (a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ TreeEdges a b c)
  | _ => false

theorem cells_three (a b c : Cell) : Cells [a,b,c] = Three a b c := by
  apply region_ext
  intro x
  simp [Cells, Three]

theorem tileCheck_sound {xs : List Cell} (hc : tileCheck xs = true) : Tile (Cells xs) := by
  match xs with
  | [a,b,c] =>
    have ht : a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ TreeEdges a b c := of_decide_eq_true hc
    rw [cells_three]
    exact ⟨⟨a,b,c,ht.1,ht.2.1,ht.2.2.1,fun _ => Iff.rfl⟩, tree_connected ht.2.2.2⟩
  | [] | [_] | [_,_] | _::_::_::_::_ => simp [tileCheck] at hc

theorem triple_length {xs : List Cell} (hn : xs.Nodup) (ht : Triple (Cells xs)) : xs.length = 3 := by
  obtain ⟨a,b,c,hab,hac,hbc,h⟩ := ht
  have hnd : [a,b,c].Nodup := by simp [hab,hac,hbc]
  have hsub : xs ⊆ [a,b,c] := by intro x hx; simpa using (h x).mp hx
  have hsup : [a,b,c] ⊆ xs := by intro x hx; apply (h x).mpr; simpa using hx
  have hle := hn.length_le_of_subset hsub
  have hge := hnd.length_le_of_subset hsup
  simp only [List.length_cons, List.length_nil] at hle hge
  omega

theorem tileCheck_complete {xs : List Cell} (hn : xs.Nodup) (ht : Tile (Cells xs)) :
    tileCheck xs = true := by
  have hlen := triple_length hn ht.1
  obtain ⟨a,b,c,heq⟩ : ∃ a b c, xs = [a,b,c] := by
    cases xs with
    | nil => simp at hlen
    | cons a ys => cases ys with
      | nil => simp at hlen
      | cons b zs => cases zs with
        | nil => simp at hlen
        | cons c ws =>
          have hw : ws = [] := by simpa using hlen
          subst ws
          exact ⟨a,b,c,rfl⟩
  subst xs
  rw [cells_three] at ht
  have hne : a ≠ b ∧ a ≠ c ∧ b ≠ c := by simpa [and_assoc] using hn
  exact decide_eq_true (And.intro hne.1 ⟨hne.2.1,hne.2.2,
    connected_three_tree hne.1 hne.2.1 hne.2.2 ht.2⟩)

/-- Set equality on finite lists, expressed with bounded decidable quantifiers. -/
def SameCells (xs ys : List Cell) : Prop :=
  (∀ x ∈ xs, x ∈ ys) ∧ (∀ x ∈ ys, x ∈ xs)

instance (xs ys : List Cell) : Decidable (SameCells xs ys) := by unfold SameCells; infer_instance

theorem sameCells_eq {xs ys : List Cell} (h : SameCells xs ys) : Cells xs = Cells ys := by
  apply region_ext
  exact fun x => ⟨h.1 x,h.2 x⟩

def remainder (pool candidate : List Cell) : List Cell :=
  pool.filter (fun x => decide (x ∉ candidate))

/-- Exhaust all ordered triples from the six cells. The complement, rather than
another independent search over triples, is the only possible second tile. -/
def PairCheck (xs ys : List Cell) : Prop :=
  (xs ++ ys).Nodup ∧
  ∀ a ∈ xs ++ ys, ∀ b ∈ xs ++ ys, ∀ c ∈ xs ++ ys,
    tileCheck [a,b,c] = true → tileCheck (remainder (xs ++ ys) [a,b,c]) = true →
    SameCells [a,b,c] xs ∨ SameCells [a,b,c] ys

instance (xs ys : List Cell) : Decidable (PairCheck xs ys) := by unfold PairCheck; infer_instance

theorem remainder_eq {xs ys candidate : List Cell} {D : Region}
    (hs : Split (Cells xs) (Cells ys) (Cells candidate) D) :
    Cells (remainder (xs ++ ys) candidate) = D := by
  apply region_ext
  intro x
  have hu : (Cells candidate x ∨ D x) ↔ (Cells xs x ∨ Cells ys x) :=
    Iff.of_eq (congrFun hs.2.2.2 x)
  have hd := hs.2.2.1 x
  simp only [Cells, remainder, List.mem_filter, List.mem_append, decide_eq_true_eq] at *
  grind

theorem split_other {A B D : Region} (hd : Disjoint A B) (hs : Split A B A D) : D = B := by
  apply region_ext
  intro x
  have hu : (A x ∨ D x) ↔ (A x ∨ B x) := Iff.of_eq (congrFun hs.2.2.2 x)
  have had := hs.2.2.1 x
  have hab := hd x
  grind

/-- Soundness of the finite pair check for the exact metagraph move rule. -/
theorem pairCheck_sound {xs ys : List Cell} (hp : PairCheck xs ys) :
    Rigid (Cells xs) (Cells ys) := by
  intro C D hs
  obtain ⟨a,b,c,hab,hac,hbc,hC⟩ := hs.1.1
  have hc : C = Cells [a,b,c] := by
    apply region_ext
    intro x
    simpa [Cells] using hC x
  subst C
  have hmember : ∀ x, Cells [a,b,c] x → x ∈ xs ++ ys := by
    intro x hx
    have hu : (Cells [a,b,c] x ∨ D x) ↔ (Cells xs x ∨ Cells ys x) :=
      Iff.of_eq (congrFun hs.2.2.2 x)
    simpa [Cells] using hu.mp (Or.inl hx)
  have hnodup : [a,b,c].Nodup := by simp [hab,hac,hbc]
  have htc := tileCheck_complete hnodup hs.1
  have hrem := remainder_eq hs
  have hremnodup : (remainder (xs ++ ys) [a,b,c]).Nodup := by
    exact hp.1.sublist (List.filter_sublist)
  have htd := tileCheck_complete hremnodup (hrem.symm ▸ hs.2.1)
  have hchoice := hp.2 a (hmember a (by simp [Cells]))
    b (hmember b (by simp [Cells])) c (hmember c (by simp [Cells])) htc htd
  have dis : Disjoint (Cells xs) (Cells ys) := by
    intro x hx hy
    have hnd := hp.1
    have hpair := List.pairwise_append.mp hnd
    exact hpair.2.2 x hx x hy rfl
  rcases hchoice with h | h
  · have heq := sameCells_eq h
    refine Or.inl ⟨heq, ?_⟩
    rw [heq] at hs
    exact split_other dis hs
  · have heq := sameCells_eq h
    refine Or.inr ⟨heq, ?_⟩
    rw [heq] at hs
    have hu : Union (Cells xs) (Cells ys) = Union (Cells ys) (Cells xs) :=
      region_ext fun _ => Or.comm
    exact split_other (fun x hx hy => dis x hy hx)
      ⟨hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.trans hu⟩

end LockedTromino
