import Core

namespace LockedTromino

/-- Strict integer cuts; thus each intermediate strip contains at least one row. -/
def IncreasingCuts (f : Nat → Int) : Prop := ∀ i, f i < f (i + 1)

theorem cuts_mono {f : Nat → Int} (hf : IncreasingCuts f) {i j : Nat}
    (hij : i ≤ j) : f i ≤ f j := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst i
    omega
  | succ j ih =>
    by_cases h : i ≤ j
    · have := ih h; have := hf j; omega
    · have : i = j + 1 := by omega
      subst i
      omega

def InInterval (f : Nat → Int) (i : Nat) (x : Int) : Prop :=
  f i ≤ x ∧ x < f (i + 1)

theorem interval_index_unique {f : Nat → Int} (hf : IncreasingCuts f)
    {i j : Nat} {x : Int} (hi : InInterval f i x) (hj : InInterval f j x) : i = j := by
  by_cases hij : i < j
  · have := cuts_mono hf (show i + 1 ≤ j by omega)
    unfold InInterval at *; omega
  · by_cases hji : j < i
    · have := cuts_mono hf (show j + 1 ≤ i by omega)
      unfold InInterval at *; omega
    · omega

theorem interval_indices_near {f : Nat → Int} (hf : IncreasingCuts f)
    {i j : Nat} {x y : Int} (hi : InInterval f i x) (hj : InInterval f j y)
    (hd : x - 1 ≤ y ∧ y ≤ x + 1) : i = j ∨ i + 1 = j ∨ j + 1 = i := by
  by_cases hij : i + 2 ≤ j
  · have hm := cuts_mono hf hij
    have hs := hf (i + 1)
    have he : i + 1 + 1 = i + 2 := by omega
    rw [he] at hs
    unfold InInterval at *; omega
  · by_cases hji : j + 2 ≤ i
    · have hm := cuts_mono hf hji
      have hs := hf (j + 1)
      have he : j + 1 + 1 = j + 2 := by omega
      rw [he] at hs
      unfold InInterval at *; omega
    · omega

theorem interval_cover {f : Nat → Int} (_hf : IncreasingCuts f) (n : Nat)
    {x : Int} (hx : f 0 ≤ x ∧ x < f n) : ∃ i, i < n ∧ InInterval f i x := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : x < f n
    · obtain ⟨i, hi, hix⟩ := ih ⟨hx.1, h⟩
      exact ⟨i, by omega, hix⟩
    · exact ⟨n, by omega, by unfold InInterval; omega⟩

def GridBox (rows cols : Nat → Int) (i j : Nat) : Region :=
  fun x => InInterval rows i x.1 ∧ InInterval cols j x.2

def SideNeighbors (i j k l : Nat) : Prop :=
  (j = l ∧ (i + 1 = k ∨ k + 1 = i)) ∨
  (i = k ∧ (j + 1 = l ∨ l + 1 = j))

/-- A grid edge joins the same box or two boxes sharing a whole side.
In particular corner-touching boxes cannot interact. -/
theorem edge_boxes {rows cols : Nat → Int}
    (hr : IncreasingCuts rows) (hc : IncreasingCuts cols)
    {i j k l : Nat} {x y : Cell}
    (hx : GridBox rows cols i j x) (hy : GridBox rows cols k l y)
    (he : Adj x y) : (i = k ∧ j = l) ∨ SideNeighbors i j k l := by
  rcases he with ⟨hre, hce⟩ | ⟨hce, hre⟩
  · have hir : i = k := interval_index_unique hr hx.1 (hre ▸ hy.1)
    have hnear := interval_indices_near hc hx.2 hy.2 (by rcases hce with h | h <;> omega)
    rcases hnear with h | h | h
    · exact Or.inl ⟨hir, h⟩
    · exact Or.inr (Or.inr ⟨hir, Or.inl h⟩)
    · exact Or.inr (Or.inr ⟨hir, Or.inr h⟩)
  · have hic : j = l := interval_index_unique hc hx.2 (hce ▸ hy.2)
    have hnear := interval_indices_near hr hx.1 hy.1 (by rcases hre with h | h <;> omega)
    rcases hnear with h | h | h
    · exact Or.inl ⟨h, hic⟩
    · exact Or.inr (Or.inl ⟨hic, Or.inl h⟩)
    · exact Or.inr (Or.inl ⟨hic, Or.inr h⟩)

theorem nonneighbor_noEdges {rows cols : Nat → Int}
    (hr : IncreasingCuts rows) (hc : IncreasingCuts cols)
    {i j k l : Nat} {A B : Region}
    (ha : Sub A (GridBox rows cols i j)) (hb : Sub B (GridBox rows cols k l))
    (hdiff : ¬ (i = k ∧ j = l)) (hside : ¬ SideNeighbors i j k l) : NoEdges A B := by
  intro x y hx hy he
  rcases edge_boxes hr hc (ha x hx) (hb y hy) he with h | h
  · exact hdiff h
  · exact hside h

/-- Cuts are constructed from positive strip lengths, not geometrically assumed. -/
def Prefix (sizes : Nat → Nat) : Nat → Int
  | 0 => 0
  | n + 1 => Prefix sizes n + sizes n

theorem prefix_increasing {sizes : Nat → Nat} (hs : ∀ i, 0 < sizes i) :
    IncreasingCuts (Prefix sizes) := by
  intro i
  simp only [Prefix]
  have := hs i
  omega

end LockedTromino
