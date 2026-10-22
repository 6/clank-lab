import FastCertificate

namespace LockedTromino

instance (h w : Nat) (x : Cell) : Decidable (Rectangle h w x) := by
  unfold Rectangle; infer_instance

def Ownership (ts : List (List Cell)) (owner : Cell → List Cell) : Prop :=
  ∀ xs ∈ ts, ∀ x ∈ xs, owner x = xs

instance (ts : List (List Cell)) (owner : Cell → List Cell) : Decidable (Ownership ts owner) := by
  unfold Ownership; infer_instance

/-- Checking an owner for each cell proves disjointness without a quadratic
comparison of every tile pair. Bounds and coverage remain exact finite checks. -/
def OwnerPartitionCheck (h w : Nat) (ts : List (List Cell)) (owner : Cell → List Cell) : Prop :=
  (∀ xs ∈ ts, tileCheck xs = true) ∧
  Ownership ts owner ∧
  (∀ xs ∈ ts, ∀ x ∈ xs, Rectangle h w x) ∧
  (∀ x ∈ rectangleCells h w, owner x ∈ ts ∧ x ∈ owner x)

instance (h w : Nat) (ts : List (List Cell)) (owner : Cell → List Cell) :
    Decidable (OwnerPartitionCheck h w ts owner) := by
  unfold OwnerPartitionCheck; infer_instance

theorem ownerPartition_tiling {h w : Nat} {ts : List (List Cell)} {owner : Cell → List Cell}
    (hp : OwnerPartitionCheck h w ts owner) : Tiling (Rectangle h w) (CoordinateTiles ts) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A ha
    obtain ⟨xs,hxs,heq⟩ := ha
    subst A
    exact tileCheck_sound (hp.1 xs hxs)
  · intro x
    constructor
    · intro hx
      obtain ⟨hm,hx'⟩ := hp.2.2.2 x ((rectangleCells_mem h w x).mpr hx)
      exact ⟨Cells (owner x), ⟨owner x,hm,rfl⟩, hx'⟩
    · intro ⟨A,ha,hx⟩
      obtain ⟨xs,hxs,heq⟩ := ha
      subst A
      exact hp.2.2.1 xs hxs x hx
  · intro A B ha hb hne x hx hy
    obtain ⟨xs,hxs,heq⟩ := ha
    obtain ⟨ys,hys,heq'⟩ := hb
    subst A; subst B
    exact hne (congrArg Cells ((hp.2.1 xs hxs x hx).symm.trans (hp.2.1 ys hys x hy)))

/-- All four integer-grid neighbors, with proved completeness. -/
def neighbors (x : Cell) : List Cell :=
  [(x.1-1,x.2),(x.1+1,x.2),(x.1,x.2-1),(x.1,x.2+1)]

theorem adj_neighbor {x y : Cell} (ha : Adj x y) : y ∈ neighbors x := by
  simp only [neighbors, List.mem_cons, List.not_mem_nil, or_false, Prod.ext_iff]
  unfold Adj at ha
  omega

structure LocalEntry where
  cells : List Cell
  links : List (List Cell)
  deriving DecidableEq

def EntryTiles (es : List LocalEntry) : List (List Cell) := es.map LocalEntry.cells

def CertifiedLinks (es : List LocalEntry) : Prop :=
  ∀ e ∈ es, ∀ ys ∈ e.links, Rigid (Cells e.cells) (Cells ys)

/-- The guarded edge cover is linear in cells and a small neighbor list, rather
than in all tile pairs. The guard is the exact placed target rectangle. -/
def EdgeCoverCheck (es : List LocalEntry) (owner : Cell → List Cell)
    (r c : Int) (h w : Nat) : Prop :=
  ∀ e ∈ es, ∀ x ∈ e.cells, ∀ y ∈ neighbors x,
    Shift (r,c) (Rectangle h w) y → owner y = e.cells ∨ owner y ∈ e.links

instance (es : List LocalEntry) (owner : Cell → List Cell) (r c : Int) (h w : Nat) :
    Decidable (EdgeCoverCheck es owner r c h w) := by
  unfold EdgeCoverCheck
  exact @List.decidableBAll LocalEntry _ (fun e =>
    @List.decidableBAll Cell _ (fun x =>
      @List.decidableBAll Cell _ (fun y => by
        unfold Shift Add Neg Rectangle
        infer_instance) (neighbors x)) e.cells) es

theorem entry_edge_rigid {es : List LocalEntry} {ts : List (List Cell)}
    {owner : Cell → List Cell} {r c : Int} {h w : Nat}
    (ht : Tiling (Shift (r,c) (Rectangle h w)) (CoordinateTiles ts))
    (hs : ∀ xs ∈ EntryTiles es, Tile (Cells xs))
    (ho : Ownership ts owner) (hl : CertifiedLinks es)
    (hc : EdgeCoverCheck es owner r c h w)
    (hd : ∀ A B, CoordinateTiles (EntryTiles es) A → CoordinateTiles ts B →
      A ≠ B → Disjoint A B) :
    ∀ A B, CoordinateTiles (EntryTiles es) A → CoordinateTiles ts B → A ≠ B → Rigid A B := by
  classical
  intro A B ha hb hne
  obtain ⟨xs,hxs,heq⟩ := ha
  obtain ⟨ys,hys,heq'⟩ := hb
  subst A; subst B
  by_cases hn : NoEdges (Cells xs) (Cells ys)
  · exact noEdges_rigid (hs xs hxs) (ht.1 _ ⟨ys,hys,rfl⟩)
      (hd _ _ ⟨xs,hxs,rfl⟩ ⟨ys,hys,rfl⟩ hne) hn
  · have hedge : ∃ x y, x ∈ xs ∧ y ∈ ys ∧ Adj x y := by
      apply Classical.byContradiction
      intro he
      apply hn
      intro x y hx hy hadj
      exact he ⟨x,y,hx,hy,hadj⟩
    obtain ⟨x,y,hx,hy,hxy⟩ := hedge
    obtain ⟨e,he,hex⟩ := List.mem_map.mp hxs
    have hry : Shift (r,c) (Rectangle h w) y := (ht.2.1 y).mpr ⟨Cells ys,⟨ys,hys,rfl⟩,hy⟩
    have hcover := hc e he x (hex.symm ▸ hx) y (adj_neighbor hxy) hry
    rw [ho ys hys y hy, hex] at hcover
    rcases hcover with same | link
    · exact False.elim (hne (congrArg Cells same.symm))
    · exact hex ▸ hl e he ys link

theorem localBlock_rigid {h w : Nat} {es : List LocalEntry} {owner : Cell → List Cell}
    (hp : OwnerPartitionCheck h w (EntryTiles es) owner)
    (hl : CertifiedLinks es) (hc : EdgeCoverCheck es owner 0 0 h w) :
    PairwiseRigid (CoordinateTiles (EntryTiles es)) := by
  have ht := ownerPartition_tiling hp
  have hshift : Shift (0,0) (Rectangle h w) = Rectangle h w := by
    apply region_ext; intro x; simp [Shift, Add, Neg]
  apply entry_edge_rigid (hshift.symm ▸ ht) (fun xs hxs => tileCheck_sound (hp.1 xs hxs)) hp.2.1 hl hc
  exact ht.2.2

def localCheckedBlock {h w : Nat} {es : List LocalEntry} {owner : Cell → List Cell}
    (hp : OwnerPartitionCheck h w (EntryTiles es) owner)
    (hl : CertifiedLinks es) (hc : EdgeCoverCheck es owner 0 0 h w) : RigidBlock h w :=
  ⟨CoordinateTiles (EntryTiles es),ownerPartition_tiling hp,localBlock_rigid hp hl hc⟩

/-- Translation of a coordinate-family partition and its cell owner. -/
def shiftOwner (d : Cell) (owner : Cell → List Cell) : Cell → List Cell :=
  fun x => shiftCells d (owner (Add (Neg d) x))

theorem shift_ownership {ts : List (List Cell)} {owner : Cell → List Cell}
    (ho : Ownership ts owner) (d : Cell) :
    Ownership (ts.map (shiftCells d)) (shiftOwner d owner) := by
  intro xs hxs x hx
  obtain ⟨ys,hys,heq⟩ := List.mem_map.mp hxs
  subst xs
  obtain ⟨y,hy,heq⟩ := List.mem_map.mp hx
  subst x
  unfold shiftOwner
  rw [add_neg, ho ys hys y hy]

theorem coordinate_shift (d : Cell) (ts : List (List Cell)) :
    CoordinateTiles (ts.map (shiftCells d)) = ShiftTiles d (CoordinateTiles ts) := by
  funext A
  apply propext
  constructor
  · intro ⟨xs,hxs,heq⟩
    obtain ⟨ys,hys,hshift⟩ := List.mem_map.mp hxs
    subst xs
    exact ⟨Cells ys,⟨ys,hys,rfl⟩,heq.trans (shiftCells_eq d ys)⟩
  · intro ⟨B,⟨ys,hys,heq⟩,heq'⟩
    subst B
    exact ⟨shiftCells d ys,List.mem_map.mpr ⟨ys,hys,rfl⟩,heq'.trans (shiftCells_eq d ys).symm⟩

theorem localSeam_rigid {h w k v : Nat} {ts : List (List Cell)}
    {es : List LocalEntry} {owner : Cell → List Cell} {r c : Int}
    (hs : Tiling (Rectangle h w) (CoordinateTiles (EntryTiles es)))
    (ht : OwnerPartitionCheck k v ts owner)
    (hl : CertifiedLinks es) (hc : EdgeCoverCheck es (shiftOwner (r,c) owner) r c k v)
    (hd : Disjoint (Rectangle h w) (Shift (r,c) (Rectangle k v))) :
    ∀ A B, CoordinateTiles (EntryTiles es) A → CoordinateTiles ts B → Rigid A (Shift (r,c) B) := by
  have htarget := shift_tiling (r,c) (ownerPartition_tiling ht)
  rw [← coordinate_shift] at htarget
  have hcross := entry_edge_rigid htarget
    (fun xs hxs => hs.1 _ ⟨xs,hxs,rfl⟩) (shift_ownership ht.2.1 (r,c)) hl hc
    (fun A B ha hb _hne x hx hy => hd x ((hs.2.1 x).mpr ⟨A,ha,hx⟩)
      ((htarget.2.1 x).mpr ⟨B,hb,hy⟩))
  intro A B ha hb
  apply hcross A (Shift (r,c) B) ha
  · rw [coordinate_shift]
    exact ⟨B,hb,rfl⟩
  · intro heq
    obtain ⟨x,hx⟩ := triple_nonempty (hs.1 A ha).1
    exact hd x ((hs.2.1 x).mpr ⟨A,ha,hx⟩)
      ((htarget.2.1 x).mpr ⟨Shift (r,c) B,by rw [coordinate_shift]; exact ⟨B,hb,rfl⟩,heq ▸ hx⟩)

theorem rigid_from_pattern (d : Cell) {p q xs ys : List Cell}
    (hp : Rigid (Cells p) (Cells q))
    (hx : SameCells xs (shiftCells d p)) (hy : SameCells ys (shiftCells d q)) :
    Rigid (Cells xs) (Cells ys) := by
  rw [sameCells_eq hx, sameCells_eq hy, shiftCells_eq, shiftCells_eq]
  exact shift_rigid d hp

end LockedTromino
