import Core

namespace LockedTromino

def Add (d x : Cell) : Cell := (x.1 + d.1, x.2 + d.2)
def Neg (d : Cell) : Cell := (-d.1, -d.2)
def Shift (d : Cell) (A : Region) : Region := fun x => A (Add (Neg d) x)
def ShiftTiles (d : Cell) (T : Region → Prop) : Region → Prop :=
  fun B => ∃ A, T A ∧ B = Shift d A

@[simp] theorem add_neg (d x : Cell) : Add (Neg d) (Add d x) = x := by
  apply Prod.ext <;> dsimp [Add, Neg] <;> omega

@[simp] theorem neg_add (d x : Cell) : Add d (Add (Neg d) x) = x := by
  apply Prod.ext <;> dsimp [Add, Neg] <;> omega

@[simp] theorem shift_mem_add (d : Cell) (A : Region) (x : Cell) :
    Shift d A (Add d x) ↔ A x := by simp [Shift]

@[simp] theorem shift_inverse (d : Cell) (A : Region) : Shift (Neg d) (Shift d A) = A := by
  apply region_ext
  intro x
  have h : Neg (Neg d) = d := by
    apply Prod.ext <;> dsimp [Neg] <;> omega
  simp only [Shift, h, add_neg]

theorem shift_injective (d : Cell) {A B : Region} (h : Shift d A = Shift d B) : A = B := by
  have := congrArg (Shift (Neg d)) h
  simpa using this

theorem shift_comp (d e : Cell) (A : Region) : Shift d (Shift e A) = Shift (Add d e) A := by
  apply region_ext
  intro x
  have heq : Add (Neg e) (Add (Neg d) x) = Add (Neg (Add d e)) x := by
    apply Prod.ext <;> dsimp [Add, Neg] <;> omega
  change A (Add (Neg e) (Add (Neg d) x)) ↔ A (Add (Neg (Add d e)) x)
  rw [heq]

theorem shift_adj (d : Cell) {x y : Cell} (he : Adj x y) : Adj (Add d x) (Add d y) := by
  unfold Adj Add at *
  rcases he with ⟨h, h' | h'⟩ | ⟨h, h' | h'⟩ <;> omega

theorem shift_triple (d : Cell) {A : Region} (ht : Triple A) : Triple (Shift d A) := by
  obtain ⟨a, b, c, hab, hac, hbc, ht⟩ := ht
  refine ⟨Add d a, Add d b, Add d c, ?_, ?_, ?_, ?_⟩
  · intro h; have := congrArg (Add (Neg d)) h; simp only [add_neg] at this; exact hab this
  · intro h; have := congrArg (Add (Neg d)) h; simp only [add_neg] at this; exact hac this
  · intro h; have := congrArg (Add (Neg d)) h; simp only [add_neg] at this; exact hbc this
  · intro x
    change A (Add (Neg d) x) ↔ _
    rw [ht]
    have inv := neg_add d x
    constructor
    · intro h
      rcases h with h | h | h
      · exact Or.inl (by rw [← h]; exact inv.symm)
      · exact Or.inr (Or.inl (by rw [← h]; exact inv.symm))
      · exact Or.inr (Or.inr (by rw [← h]; exact inv.symm))
    · intro h
      rcases h with rfl | rfl | rfl <;> simp

theorem shift_walk (d : Cell) {A : Region} {x y : Cell} (h : Walk A x y) :
    Walk (Shift d A) (Add d x) (Add d y) := by
  induction h with
  | refl hx => exact Walk.refl ((shift_mem_add d A _).mpr hx)
  | step _ hz he ih => exact Walk.step ih ((shift_mem_add d A _).mpr hz) (shift_adj d he)

theorem shift_tile (d : Cell) {A : Region} (ht : Tile A) : Tile (Shift d A) := by
  refine ⟨shift_triple d ht.1, ?_⟩
  intro x y hx hy
  have p := shift_walk d (ht.2 (Add (Neg d) x) (Add (Neg d) y) hx hy)
  simpa using p

theorem shift_disjoint (d : Cell) {A B : Region} (hd : Disjoint A B) :
    Disjoint (Shift d A) (Shift d B) := fun x hx hy => hd (Add (Neg d) x) hx hy

@[simp] theorem shift_union (d : Cell) (A B : Region) :
    Shift d (Union A B) = Union (Shift d A) (Shift d B) := rfl

theorem shift_split (d : Cell) {A B C D : Region} (hs : Split A B C D) :
    Split (Shift d A) (Shift d B) (Shift d C) (Shift d D) := by
  refine ⟨shift_tile d hs.1, shift_tile d hs.2.1, shift_disjoint d hs.2.2.1, ?_⟩
  exact congrArg (Shift d) hs.2.2.2

theorem rigid_symm {A B : Region} (h : Rigid A B) : Rigid B A := by
  intro C D hs
  have hu : Union A B = Union B A := region_ext fun _ => Or.comm
  have hs' : Split A B C D := ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.trans hu.symm⟩
  exact (h C D hs').symm

theorem shift_rigid (d : Cell) {A B : Region} (h : Rigid A B) :
    Rigid (Shift d A) (Shift d B) := by
  intro C D hs
  have hs' := shift_split (Neg d) hs
  simp only [shift_inverse] at hs'
  rcases h _ _ hs' with ⟨hca, hdb⟩ | ⟨hcb, hda⟩
  · exact Or.inl ⟨shift_injective (Neg d) (by simpa using hca),
      shift_injective (Neg d) (by simpa using hdb)⟩
  · exact Or.inr ⟨shift_injective (Neg d) (by simpa using hcb),
      shift_injective (Neg d) (by simpa using hda)⟩

theorem shift_tiling (d : Cell) {R : Region} {T : Region → Prop} (ht : Tiling R T) :
    Tiling (Shift d R) (ShiftTiles d T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨A, ha, heq⟩ := hB
    subst B
    exact shift_tile d (ht.1 A ha)
  · intro x
    constructor
    · intro hx
      obtain ⟨A, ha, hax⟩ := (ht.2.1 (Add (Neg d) x)).mp hx
      exact ⟨Shift d A, ⟨A, ha, rfl⟩, hax⟩
    · intro ⟨B, hB, hax⟩
      obtain ⟨A, ha, heq⟩ := hB
      subst B
      exact (ht.2.1 (Add (Neg d) x)).mpr ⟨A, ha, hax⟩
  · intro A B hA hB hne
    obtain ⟨C, hc, heq⟩ := hA
    obtain ⟨D, hd, heq'⟩ := hB
    subst A; subst B
    exact shift_disjoint d (ht.2.2 C D hc hd (fun h => hne (congrArg (Shift d) h)))

theorem shift_pairwiseRigid (d : Cell) {T : Region → Prop} (hi : PairwiseRigid T) :
    PairwiseRigid (ShiftTiles d T) := by
  intro A B hA hB hne
  obtain ⟨C, hc, heq⟩ := hA
  obtain ⟨D, hd, heq'⟩ := hB
  subst A; subst B
  exact shift_rigid d (hi C D hc hd (fun h => hne (congrArg (Shift d) h)))

end LockedTromino
