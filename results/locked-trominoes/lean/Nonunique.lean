import Core

namespace LockedTromino

def Three (a b c : Cell) : Region := fun x => x = a ∨ x = b ∨ x = c

theorem walk_start {A : Region} {x y : Cell} (h : Walk A x y) : A x := by
  induction h with
  | refl hx => exact hx
  | step _ _ _ ih => exact ih

theorem walk_trans {A : Region} {x y z : Cell} (p : Walk A x y) (q : Walk A y z) :
    Walk A x z := by
  induction q with
  | refl _ => exact p
  | step _ hz he ih => exact Walk.step ih hz he

theorem walk_symm {A : Region} {x y : Cell} (p : Walk A x y) : Walk A y x := by
  induction p with
  | refl hx => exact Walk.refl hx
  | @step y z p hz he ih =>
    exact walk_trans (Walk.step (Walk.refl hz) (walk_start ih) (adj_symm he)) ih

theorem connected_three_chain (a b c : Cell) (hab : Adj a b) (hbc : Adj b c) :
    Connected (Three a b c) := by
  have ha : Three a b c a := Or.inl rfl
  have hb : Three a b c b := Or.inr (Or.inl rfl)
  have hc : Three a b c c := Or.inr (Or.inr rfl)
  have pab : Walk (Three a b c) a b := Walk.step (Walk.refl ha) hb hab
  have pac : Walk (Three a b c) a c := Walk.step pab hc hbc
  have from_a : ∀ x, Three a b c x → Walk (Three a b c) a x := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact Walk.refl ha
    · exact pab
    · exact pac
  exact fun x y hx hy => walk_trans (walk_symm (from_a x hx)) (from_a y hy)

def Vertical (r c : Int) : Region := Three (r, c) (r + 1, c) (r + 2, c)
def Horizontal (r c : Int) : Region := Three (r, c) (r, c + 1) (r, c + 2)

theorem vertical_mem (r c : Int) (x : Cell) :
    Vertical r c x ↔ x.2 = c ∧ r ≤ x.1 ∧ x.1 < r + 3 := by
  simp only [Vertical, Three, Prod.ext_iff]
  omega

theorem horizontal_mem (r c : Int) (x : Cell) :
    Horizontal r c x ↔ x.1 = r ∧ c ≤ x.2 ∧ x.2 < c + 3 := by
  simp only [Horizontal, Three, Prod.ext_iff]
  omega

theorem vertical_tile (r c : Int) : Tile (Vertical r c) := by
  refine ⟨⟨(r,c), (r+1,c), (r+2,c), ?_, ?_, ?_, fun _ => Iff.rfl⟩, ?_⟩
  · intro he; have := congrArg Prod.fst he; dsimp at this; omega
  · intro he; have := congrArg Prod.fst he; dsimp at this; omega
  · intro he; have := congrArg Prod.fst he; dsimp at this; omega
  · apply connected_three_chain <;> unfold Adj <;> dsimp <;> omega

theorem horizontal_tile (r c : Int) : Tile (Horizontal r c) := by
  refine ⟨⟨(r,c), (r,c+1), (r,c+2), ?_, ?_, ?_, fun _ => Iff.rfl⟩, ?_⟩
  · intro he; have := congrArg Prod.snd he; dsimp at this; omega
  · intro he; have := congrArg Prod.snd he; dsimp at this; omega
  · intro he; have := congrArg Prod.snd he; dsimp at this; omega
  · apply connected_three_chain <;> unfold Adj <;> dsimp <;> omega

/-- Straight vertical triples in the columns at or above `lo`. -/
def VerticalFamily (h w : Nat) (lo : Int) : Region → Prop :=
  fun A => ∃ k c : Int, 0 ≤ k ∧ 3*k + 3 ≤ h ∧ lo ≤ c ∧ c < w ∧ A = Vertical (3*k) c

def HorizontalFamily (h : Nat) : Region → Prop :=
  fun A => ∃ r : Int, 0 ≤ r ∧ r < h ∧ A = Horizontal r 0

def MixedFamily (h w : Nat) : Region → Prop :=
  fun A => VerticalFamily h w 3 A ∨ HorizontalFamily h A

theorem verticalFamily_tile {h w : Nat} {lo : Int} {A : Region}
    (ha : VerticalFamily h w lo A) : Tile A := by
  obtain ⟨k,c,_,_,_,_,rfl⟩ := ha
  exact vertical_tile _ _

theorem verticalFamily_disjoint {h w : Nat} {lo : Int} {A B : Region}
    (ha : VerticalFamily h w lo A) (hb : VerticalFamily h w lo B) (hne : A ≠ B) :
    Disjoint A B := by
  obtain ⟨k,c,_,_,_,_,rfl⟩ := ha
  obtain ⟨l,d,_,_,_,_,rfl⟩ := hb
  intro x hx hy
  rw [vertical_mem] at hx hy
  have hk : k = l := by omega
  have hc : c = d := by omega
  subst l; subst d
  exact hne rfl

theorem verticalFamily_cover (q w : Nat) (lo : Int) (x : Cell) :
    (0 ≤ x.1 ∧ x.1 < 3*q ∧ lo ≤ x.2 ∧ x.2 < w) ↔
    ∃ A, VerticalFamily (3*q) w lo A ∧ A x := by
  constructor
  · intro hx
    refine ⟨Vertical (3*(x.1/3)) x.2, ?_, ?_⟩
    · refine ⟨x.1/3, x.2, ?_, ?_, hx.2.2.1, hx.2.2.2, rfl⟩ <;> omega
    · rw [vertical_mem]; omega
  · intro ⟨A, ha, hx⟩
    obtain ⟨k,c,hk,hkh,hc,hcw,heq⟩ := ha
    subst A
    rw [vertical_mem] at hx
    omega

theorem vertical_tiling (q w : Nat) : Tiling (Rectangle (3*q) w) (VerticalFamily (3*q) w 0) := by
  refine ⟨fun _ ha => verticalFamily_tile ha, ?_, ?_⟩
  · intro x
    exact verticalFamily_cover q w 0 x
  · intro A B ha hb hne
    exact verticalFamily_disjoint ha hb hne

theorem mixed_tiling (q w : Nat) (hw : 3 ≤ w) :
    Tiling (Rectangle (3*q) w) (MixedFamily (3*q) w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A ha
    rcases ha with ha | ⟨r,_,_,rfl⟩
    · exact verticalFamily_tile ha
    · exact horizontal_tile _ _
  · intro x
    constructor
    · intro hx
      by_cases hc : 3 ≤ x.2
      · obtain ⟨A, ha, hax⟩ := (verticalFamily_cover q w 3 x).mp ⟨hx.1, hx.2.1, hc, hx.2.2.2⟩
        exact ⟨A, Or.inl ha, hax⟩
      · refine ⟨Horizontal x.1 0, Or.inr ⟨x.1, hx.1, hx.2.1, rfl⟩, ?_⟩
        rw [horizontal_mem]
        exact ⟨rfl, hx.2.2.1, by omega⟩
    · intro ⟨A, ha, hax⟩
      rcases ha with hv | ⟨r,hr,hrh,rfl⟩
      · have := (verticalFamily_cover q w 3 x).mpr ⟨A,hv,hax⟩
        unfold Rectangle
        omega
      · rw [horizontal_mem] at hax
        unfold Rectangle
        omega
  · intro A B ha hb hne x hax hbx
    rcases ha with hv | ⟨r,hr,hrh,rfl⟩ <;> rcases hb with hv' | ⟨s,hs,hsh,rfl⟩
    · exact verticalFamily_disjoint hv hv' hne x hax hbx
    · obtain ⟨k,c,_,_,hc,_,rfl⟩ := hv
      rw [vertical_mem] at hax
      rw [horizontal_mem] at hbx
      omega
    · obtain ⟨k,c,_,_,hc,_,rfl⟩ := hv'
      rw [horizontal_mem] at hax
      rw [vertical_mem] at hbx
      omega
    · rw [horizontal_mem] at hax hbx
      have he : r = s := by omega
      subst s
      exact hne rfl

theorem horizontal_ne_vertical (r c k d : Int) : Horizontal r c ≠ Vertical k d := by
  intro he
  have h0 : Horizontal r c (r,c) := Or.inl rfl
  have h1 : Horizontal r c (r,c+1) := Or.inr (Or.inl rfl)
  rw [he, vertical_mem] at h0 h1
  dsimp at h0 h1
  omega

theorem two_tilings (q w : Nat) (hq : 0 < q) (hw : 3 ≤ w) :
    ∃ U V : Region → Prop, Tiling (Rectangle (3*q) w) U ∧
      Tiling (Rectangle (3*q) w) V ∧ U ≠ V := by
  refine ⟨VerticalFamily (3*q) w 0, MixedFamily (3*q) w,
    vertical_tiling q w, mixed_tiling q w hw, ?_⟩
  intro he
  have hm : MixedFamily (3*q) w (Horizontal 0 0) := Or.inr ⟨0, by omega, by omega, rfl⟩
  rw [← he] at hm
  obtain ⟨k,c,_,_,_,_,hbad⟩ := hm
  exact horizontal_ne_vertical 0 0 (3*k) c hbad

/-- No finite witness needs to certify the extra-tiling condition. -/
theorem locked_of_rigid {m w : Nat} (hm : 6 ≤ m) (hd : 3 ∣ m) (hw : 4 ≤ w)
    {T : Region → Prop} (ht : Tiling (Rectangle m w) T) (hr : PairwiseRigid T) :
    Locked (Rectangle m w) T := by
  obtain ⟨q,hq⟩ := hd
  subst m
  have hqpos : 0 < q := by omega
  obtain ⟨U,V,hu,hv,hne⟩ := two_tilings q w hqpos (by omega)
  refine ⟨ht, hr, ?_⟩
  by_cases he : U = T
  · exact ⟨V, hv, fun h => hne (he.trans h.symm)⟩
  · exact ⟨U, hu, he⟩

end LockedTromino
