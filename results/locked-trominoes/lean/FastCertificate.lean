import SubsetCertificate

namespace LockedTromino

/-- A proved shortcut: a disconnected six-cell union cannot recombine.
The original complete enumerator remains the fallback for interacting tiles. -/
def NoEdgeCheck (xs ys : List Cell) : Prop :=
  ∀ x ∈ xs, ∀ y ∈ ys, ¬ Adj x y

instance (xs ys : List Cell) : Decidable (NoEdgeCheck xs ys) := by
  unfold NoEdgeCheck; infer_instance

def FastPairCheck (xs ys : List Cell) : Prop :=
  (xs ++ ys).Nodup ∧ (NoEdgeCheck xs ys ∨ SubsetPairCheck xs ys)

instance (xs ys : List Cell) : Decidable (FastPairCheck xs ys) := by
  unfold FastPairCheck; infer_instance

theorem fastPairCheck_sound {xs ys : List Cell} (hx : Tile (Cells xs)) (hy : Tile (Cells ys))
    (hp : FastPairCheck xs ys) : Rigid (Cells xs) (Cells ys) := by
  rcases hp.2 with hn | hp'
  · have hd : Disjoint (Cells xs) (Cells ys) := by
      intro x hx' hy'
      exact (List.pairwise_append.mp hp.1).2.2 x hx' x hy' rfl
    exact noEdges_rigid hx hy hd (fun x y hx' hy' => hn x hx' y hy')
  · exact subsetPairCheck_sound hp'

def FastBlockCheck (h w : Nat) (ts : List (List Cell)) : Prop :=
  (∀ xs ∈ ts, tileCheck xs = true) ∧
  SameCells ts.flatten (rectangleCells h w) ∧
  ∀ xs ∈ ts, ∀ ys ∈ ts, xs ≠ ys → FastPairCheck xs ys

instance (h w : Nat) (ts : List (List Cell)) : Decidable (FastBlockCheck h w ts) := by
  unfold FastBlockCheck; infer_instance

theorem fastBlockCheck_tiling {h w : Nat} {ts : List (List Cell)} (hb : FastBlockCheck h w ts) :
    Tiling (Rectangle h w) (CoordinateTiles ts) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A ha
    obtain ⟨xs,hxs,heq⟩ := ha
    subst A
    exact tileCheck_sound (hb.1 xs hxs)
  · intro x
    constructor
    · intro hx
      have hmem := hb.2.1.2 x ((rectangleCells_mem h w x).mpr hx)
      obtain ⟨xs,hxs,hx⟩ := List.mem_flatten.mp hmem
      exact ⟨Cells xs, ⟨xs,hxs,rfl⟩, hx⟩
    · intro ⟨A,ha,hax⟩
      obtain ⟨xs,hxs,heq⟩ := ha
      subst A
      exact (rectangleCells_mem h w x).mp (hb.2.1.1 x (List.mem_flatten.mpr ⟨xs,hxs,hax⟩))
  · intro A B ha hb' hne
    obtain ⟨xs,hxs,heq⟩ := ha
    obtain ⟨ys,hys,heq'⟩ := hb'
    subst A; subst B
    have hpair := hb.2.2 xs hxs ys hys (fun h => hne (congrArg Cells h))
    intro x hx hy
    exact (List.pairwise_append.mp hpair.1).2.2 x hx x hy rfl

theorem fastBlockCheck_rigid {h w : Nat} {ts : List (List Cell)} (hb : FastBlockCheck h w ts) :
    PairwiseRigid (CoordinateTiles ts) := by
  intro A B ha hb' hne
  obtain ⟨xs,hxs,heq⟩ := ha
  obtain ⟨ys,hys,heq'⟩ := hb'
  subst A; subst B
  exact fastPairCheck_sound (tileCheck_sound (hb.1 xs hxs)) (tileCheck_sound (hb.1 ys hys))
    (hb.2.2 xs hxs ys hys (fun h => hne (congrArg Cells h)))

def fastCheckedBlock {h w : Nat} {ts : List (List Cell)}
    (hb : FastBlockCheck h w ts) : RigidBlock h w :=
  ⟨CoordinateTiles ts, fastBlockCheck_tiling hb, fastBlockCheck_rigid hb⟩

def FastSeamCheck (d : Cell) (ts us : List (List Cell)) : Prop :=
  ∀ xs ∈ ts, ∀ ys ∈ us, FastPairCheck xs (shiftCells d ys)

instance (d : Cell) (ts us : List (List Cell)) : Decidable (FastSeamCheck d ts us) := by
  unfold FastSeamCheck; infer_instance

theorem fastSeamCheck_sound {d : Cell} {ts us : List (List Cell)}
    (ht : ∀ xs ∈ ts, tileCheck xs = true) (hu : ∀ ys ∈ us, tileCheck ys = true)
    (hs : FastSeamCheck d ts us) :
    ∀ A B, CoordinateTiles ts A → CoordinateTiles us B → Rigid A (Shift d B) := by
  intro A B ha hb
  obtain ⟨xs,hxs,heq⟩ := ha
  obtain ⟨ys,hys,heq'⟩ := hb
  subst A; subst B
  have hyt : Tile (Cells (shiftCells d ys)) := by
    rw [shiftCells_eq]
    exact shift_tile d (tileCheck_sound (hu ys hys))
  have hp := fastPairCheck_sound (tileCheck_sound (ht xs hxs)) hyt (hs xs hxs ys hys)
  rw [shiftCells_eq] at hp
  exact hp

example : FastPairCheck [(0,0),(1,0),(2,0)] [(0,3),(1,3),(2,3)] := by decide
example : ¬ FastPairCheck [(0,0),(1,0),(2,0)] [(0,1),(1,1),(2,1)] := by decide
example : FastBlockCheck 3 1 [[(0,0),(1,0),(2,0)]] := by decide
example : ¬ FastBlockCheck 3 1 [[(0,0),(1,0),(3,0)]] := by decide

end LockedTromino
