import Assembly
import Arithmetic
import Translation
import Nonunique

namespace LockedTromino

/-- Only these obligations are finite. All geometric propagation is proved below.
The two seam fields quantify over EVERY ordered pair, including self pairs. -/
structure Palette (H W : Nat → Prop) where
  tiles : Nat → Nat → Region → Prop
  partition : ∀ h w, H h → W w → Tiling (Rectangle h w) (tiles h w)
  internal : ∀ h w, H h → W w → PairwiseRigid (tiles h w)
  vertical : ∀ h k w, H h → H k → W w → ∀ A B,
    tiles h w A → tiles k w B → Rigid A (Shift (h, 0) B)
  horizontal : ∀ h w v, H h → W w → W v → ∀ A B,
    tiles h w A → tiles h v B → Rigid A (Shift (0, w) B)

def Placed {H W : Nat → Prop} (p : Palette H W)
    (heights widths : Nat → Nat) (i j : Nat) : Region → Prop :=
  ShiftTiles (Prefix heights i, Prefix widths j) (p.tiles (heights i) (widths j))

theorem shift_rectangle (heights widths : Nat → Nat) (i j : Nat) :
    Shift (Prefix heights i, Prefix widths j) (Rectangle (heights i) (widths j)) =
    GridBox (Prefix heights) (Prefix widths) i j := by
  apply region_ext
  intro x
  simp only [Shift, Add, Neg, Rectangle, GridBox, InInterval, Prefix]
  omega

theorem placed_tiling {H W : Nat → Prop} (p : Palette H W)
    (heights widths : Nat → Nat) (i j : Nat) (hh : H (heights i)) (hw : W (widths j)) :
    Tiling (GridBox (Prefix heights) (Prefix widths) i j) (Placed p heights widths i j) := by
  have ht := shift_tiling (Prefix heights i, Prefix widths j)
    (p.partition (heights i) (widths j) hh hw)
  rw [shift_rectangle] at ht
  exact ht

theorem placed_down {H W : Nat → Prop} (p : Palette H W)
    (heights widths : Nat → Nat) (i j : Nat)
    (hh : H (heights i)) (hk : H (heights (i+1))) (hw : W (widths j))
    {A B : Region} (ha : Placed p heights widths i j A)
    (hb : Placed p heights widths (i+1) j B) : Rigid A B := by
  obtain ⟨C,hc,heq⟩ := ha
  obtain ⟨D,hd,heq'⟩ := hb
  subst A; subst B
  have ht := shift_rigid (Prefix heights i, Prefix widths j)
    (p.vertical (heights i) (heights (i+1)) (widths j) hh hk hw C D hc hd)
  rw [shift_comp] at ht
  have he : Add (Prefix heights i, Prefix widths j) ((heights i : Int), 0) =
      (Prefix heights (i+1), Prefix widths j) := by
    apply Prod.ext <;> simp only [Add, Prefix] <;> omega
  rw [he] at ht
  exact ht

theorem placed_right {H W : Nat → Prop} (p : Palette H W)
    (heights widths : Nat → Nat) (i j : Nat)
    (hh : H (heights i)) (hw : W (widths j)) (hv : W (widths (j+1)))
    {A B : Region} (ha : Placed p heights widths i j A)
    (hb : Placed p heights widths i (j+1) B) : Rigid A B := by
  obtain ⟨C,hc,heq⟩ := ha
  obtain ⟨D,hd,heq'⟩ := hb
  subst A; subst B
  have ht := shift_rigid (Prefix heights i, Prefix widths j)
    (p.horizontal (heights i) (widths j) (widths (j+1)) hh hw hv C D hc hd)
  rw [shift_comp] at ht
  have he : Add (Prefix heights i, Prefix widths j) (0, (widths j : Int)) =
      (Prefix heights i, Prefix widths (j+1)) := by
    apply Prod.ext <;> simp only [Add, Prefix] <;> omega
  rw [he] at ht
  exact ht

theorem all_side_checks {blocks : Nat → Nat → Region → Prop} {nr nc : Nat}
    (hd : ∀ i, i + 1 < nr → ∀ j, j < nc →
      ∀ A B, blocks i j A → blocks (i+1) j B → Rigid A B)
    (hr : ∀ i, i < nr → ∀ j, j + 1 < nc →
      ∀ A B, blocks i j A → blocks i (j+1) B → Rigid A B) :
    ∀ i, i < nr → ∀ j, j < nc → ∀ k, k < nr → ∀ l, l < nc →
      SideNeighbors i j k l → ∀ A B, blocks i j A → blocks k l B → Rigid A B := by
  intro i hi j hj k hk l hl hside A B ha hb
  rcases hside with ⟨hjl,hik | hki⟩ | ⟨hik,hjl | hlj⟩
  · subst l; subst k
    exact hd i hk j hj A B ha hb
  · subst l; subst i
    exact rigid_symm (hd k hi j hj B A hb ha)
  · subst k; subst l
    exact hr i hi j hl A B ha hb
  · subst k; subst j
    exact rigid_symm (hr i hi l hj B A hb ha)

/-- A finite palette gives an actual tiling on any rectangular grid made from
its dimensions. No existence or geometry is hidden in the conclusion. -/
theorem palette_assembly {H W : Nat → Prop} (p : Palette H W)
    (heights widths : Nat → Nat) (nr nc h w : Nat)
    (hhpos : ∀ i, 0 < heights i) (hwpos : ∀ j, 0 < widths j)
    (hh : ∀ i, i < nr → H (heights i)) (hw : ∀ j, j < nc → W (widths j))
    (hend : Prefix heights nr = h) (wend : Prefix widths nc = w) :
    ∃ T, Tiling (Rectangle h w) T ∧ PairwiseRigid T := by
  refine ⟨GridTiles (Placed p heights widths) nr nc, ?_⟩
  apply rectangular_assembly hhpos hwpos hend wend
  · intro i hi j hj
    exact placed_tiling p heights widths i j (hh i hi) (hw j hj)
  · intro i hi j hj
    exact shift_pairwiseRigid _ (p.internal _ _ (hh i hi) (hw j hj))
  · apply all_side_checks
    · intro i hi j hj A B ha hb
      exact placed_down p heights widths i j (hh i (by omega)) (hh (i+1) hi) (hw j hj) ha hb
    · intro i hi j hj A B ha hb
      exact placed_right p heights widths i j (hh i hi) (hw j (by omega)) (hw (j+1) hj) ha hb

/-- The proposed 6/9 by 8/9 palette would establish the entire n>=56 tail.
The actual checked palette is supplied in Generated/Tail.lean. -/
theorem six_nine_eight_nine_tail
    (p : Palette (fun h => h = 6 ∨ h = 9) (fun w => w = 8 ∨ w = 9))
    (m n : Nat) (hm : 6 ≤ m) (hd : 3 ∣ m) (hn : 56 ≤ n) :
    ∃ T, Locked (Rectangle m n) T := by
  obtain ⟨a,b,hab⟩ := height_six_nine m hm hd
  obtain ⟨c,d,hcd⟩ := width_eight_nine n hn
  have hh : ∀ i, TwoSizes a 6 9 i = 6 ∨ TwoSizes a 6 9 i = 9 := by
    intro i; unfold TwoSizes; split <;> simp
  have hw : ∀ i, TwoSizes c 8 9 i = 8 ∨ TwoSizes c 8 9 i = 9 := by
    intro i; unfold TwoSizes; split <;> simp
  obtain ⟨T,ht,hr⟩ := palette_assembly p (TwoSizes a 6 9) (TwoSizes c 8 9)
    (a+b) (c+d) m n (twoSizes_positive (by decide) (by decide))
    (twoSizes_positive (by decide) (by decide)) (fun i _ => hh i) (fun i _ => hw i)
    (by rw [prefix_twoSizes]; omega) (by rw [prefix_twoSizes]; omega)
  exact ⟨T, locked_of_rigid hm hd (by omega) ht hr⟩

end LockedTromino
