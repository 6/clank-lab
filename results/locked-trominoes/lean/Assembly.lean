import Geometry

namespace LockedTromino

theorem tiling_tile_sub {R : Region} {T : Region → Prop} (ht : Tiling R T)
    {A : Region} (ha : T A) : Sub A R := by
  intro x hx
  exact (ht.2.1 x).mpr ⟨A, ha, hx⟩

/-- The assembled collection consists of the actual cell sets in each placed block. -/
def GridTiles (blocks : Nat → Nat → Region → Prop) (nr nc : Nat) : Region → Prop :=
  fun A => ∃ i, i < nr ∧ ∃ j, j < nc ∧ blocks i j A

def GridRegion (rows cols : Nat → Int) (nr nc : Nat) : Region :=
  fun x => rows 0 ≤ x.1 ∧ x.1 < rows nr ∧ cols 0 ≤ x.2 ∧ x.2 < cols nc

theorem grid_tiling {rows cols : Nat → Int}
    (hr : IncreasingCuts rows) (hc : IncreasingCuts cols)
    {blocks : Nat → Nat → Region → Prop} {nr nc : Nat}
    (ht : ∀ i, i < nr → ∀ j, j < nc → Tiling (GridBox rows cols i j) (blocks i j)) :
    Tiling (GridRegion rows cols nr nc) (GridTiles blocks nr nc) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A ⟨i, hi, j, hj, ha⟩
    exact (ht i hi j hj).1 A ha
  · intro x
    constructor
    · intro hx
      obtain ⟨i, hi, hir⟩ := interval_cover hr nr ⟨hx.1, hx.2.1⟩
      obtain ⟨j, hj, hjc⟩ := interval_cover hc nc ⟨hx.2.2.1, hx.2.2.2⟩
      obtain ⟨A, ha, hax⟩ := ((ht i hi j hj).2.1 x).mp ⟨hir, hjc⟩
      exact ⟨A, ⟨i, hi, j, hj, ha⟩, hax⟩
    · intro ⟨A, ⟨i, hi, j, hj, ha⟩, hax⟩
      have hbox := tiling_tile_sub (ht i hi j hj) ha x hax
      have hr0 := cuts_mono hr (Nat.zero_le i)
      have hrn := cuts_mono hr (show i + 1 ≤ nr by omega)
      have hc0 := cuts_mono hc (Nat.zero_le j)
      have hcn := cuts_mono hc (show j + 1 ≤ nc by omega)
      unfold GridRegion
      rcases hbox with ⟨⟨_, _⟩, ⟨_, _⟩⟩
      omega
  · intro A B ⟨i, hi, j, hj, ha⟩ ⟨k, hk, l, hl, hb⟩ hne x hax hbx
    have hxa := tiling_tile_sub (ht i hi j hj) ha x hax
    have hxb := tiling_tile_sub (ht k hk l hl) hb x hbx
    have hik := interval_index_unique hr hxa.1 hxb.1
    have hjl := interval_index_unique hc hxa.2 hxb.2
    subst k; subst l
    exact (ht i hi j hj).2.2 A B ha hb hne x hax hbx

/-- Completeness of local checking: no diagonal or distant check is a hypothesis. -/
theorem grid_pairwiseRigid {rows cols : Nat → Int}
    (hr : IncreasingCuts rows) (hc : IncreasingCuts cols)
    {blocks : Nat → Nat → Region → Prop} {nr nc : Nat}
    (ht : ∀ i, i < nr → ∀ j, j < nc → Tiling (GridBox rows cols i j) (blocks i j))
    (hi : ∀ i, i < nr → ∀ j, j < nc → PairwiseRigid (blocks i j))
    (hs : ∀ i, i < nr → ∀ j, j < nc → ∀ k, k < nr → ∀ l, l < nc →
      SideNeighbors i j k l →
      ∀ A B, blocks i j A → blocks k l B → Rigid A B) :
    PairwiseRigid (GridTiles blocks nr nc) := by
  intro A B ⟨i, hir, j, hjc, ha⟩ ⟨k, hkr, l, hlc, hb⟩ hne
  by_cases same : i = k ∧ j = l
  · obtain ⟨hik, hjl⟩ := same
    subst k; subst l
    exact hi i hir j hjc A B ha hb hne
  · by_cases side : SideNeighbors i j k l
    · exact hs i hir j hjc k hkr l hlc side A B ha hb
    · have whole := grid_tiling hr hc ht
      exact noEdges_rigid ((ht i hir j hjc).1 A ha) ((ht k hkr l hlc).1 B hb)
        (whole.2.2 A B ⟨i, hir, j, hjc, ha⟩ ⟨k, hkr, l, hlc, hb⟩ hne)
        (nonneighbor_noEdges hr hc (tiling_tile_sub (ht i hir j hjc) ha)
          (tiling_tile_sub (ht k hkr l hlc) hb) same side)

/-- Concrete rectangular assembly, including its geometric partition proof. -/
theorem rectangular_assembly {heights widths : Nat → Nat}
    (hh : ∀ i, 0 < heights i) (hw : ∀ j, 0 < widths j)
    {blocks : Nat → Nat → Region → Prop} {nr nc h w : Nat}
    (hend : Prefix heights nr = h) (wend : Prefix widths nc = w)
    (ht : ∀ i, i < nr → ∀ j, j < nc →
      Tiling (GridBox (Prefix heights) (Prefix widths) i j) (blocks i j))
    (hi : ∀ i, i < nr → ∀ j, j < nc → PairwiseRigid (blocks i j))
    (hs : ∀ i, i < nr → ∀ j, j < nc → ∀ k, k < nr → ∀ l, l < nc →
      SideNeighbors i j k l → ∀ A B, blocks i j A → blocks k l B → Rigid A B) :
    Tiling (Rectangle h w) (GridTiles blocks nr nc) ∧
    PairwiseRigid (GridTiles blocks nr nc) := by
  have heq : GridRegion (Prefix heights) (Prefix widths) nr nc = Rectangle h w := by
    apply region_ext
    intro x
    simp only [GridRegion, Prefix, Rectangle, hend, wend]
  exact ⟨heq ▸ grid_tiling (prefix_increasing hh) (prefix_increasing hw) ht,
    grid_pairwiseRigid (prefix_increasing hh) (prefix_increasing hw) ht hi hs⟩

end LockedTromino
