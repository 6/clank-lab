import Finite

namespace LockedTromino

def rectangleCells (h w : Nat) : List Cell :=
  (List.range h).flatMap fun (r : Nat) => (List.range w).map fun (c : Nat) => ((r : Int), (c : Int))

theorem rectangleCells_mem (h w : Nat) (x : Cell) :
    x ∈ rectangleCells h w ↔ Rectangle h w x := by
  simp only [rectangleCells, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · intro ⟨r,hr,c,hc,heq⟩
    have her := congrArg Prod.fst heq
    have hec := congrArg Prod.snd heq
    unfold Rectangle
    dsimp at her hec
    omega
  · intro hx
    have hx0 := hx.1
    have hxc0 := hx.2.2.1
    refine ⟨x.1.toNat, by have := hx.2.1; omega, x.2.toNat, by have := hx.2.2.2; omega, ?_⟩
    apply Prod.ext <;> dsimp
    · exact Int.toNat_of_nonneg hx.1
    · exact Int.toNat_of_nonneg hx.2.2.1

def CoordinateTiles (ts : List (List Cell)) : Region → Prop :=
  fun A => ∃ xs, xs ∈ ts ∧ A = Cells xs

/-- A fully decidable certificate for a rigid rectangle partition.
The search implementation plays no role in the soundness theorem. -/
def BlockCheck (h w : Nat) (ts : List (List Cell)) : Prop :=
  (∀ xs ∈ ts, tileCheck xs = true) ∧
  SameCells ts.flatten (rectangleCells h w) ∧
  ∀ xs ∈ ts, ∀ ys ∈ ts, xs ≠ ys → PairCheck xs ys

instance (h w : Nat) (ts : List (List Cell)) : Decidable (BlockCheck h w ts) := by
  unfold BlockCheck
  infer_instance

theorem pairCheck_disjoint {xs ys : List Cell} (h : PairCheck xs ys) : Disjoint (Cells xs) (Cells ys) := by
  intro x hx hy
  exact (List.pairwise_append.mp h.1).2.2 x hx x hy rfl

theorem blockCheck_tiling {h w : Nat} {ts : List (List Cell)} (hb : BlockCheck h w ts) :
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
    have hdiff : xs ≠ ys := fun h => hne (congrArg Cells h)
    exact pairCheck_disjoint (hb.2.2 xs hxs ys hys hdiff)

theorem blockCheck_rigid {h w : Nat} {ts : List (List Cell)} (hb : BlockCheck h w ts) :
    PairwiseRigid (CoordinateTiles ts) := by
  intro A B ha hb' hne
  obtain ⟨xs,hxs,heq⟩ := ha
  obtain ⟨ys,hys,heq'⟩ := hb'
  subst A; subst B
  exact pairCheck_sound (hb.2.2 xs hxs ys hys (fun h => hne (congrArg Cells h)))

def checkedBlock {h w : Nat} {ts : List (List Cell)} (hb : BlockCheck h w ts) : RigidBlock h w :=
  ⟨CoordinateTiles ts, blockCheck_tiling hb, blockCheck_rigid hb⟩

def shiftCells (d : Cell) (xs : List Cell) : List Cell := xs.map (Add d)

theorem shiftCells_eq (d : Cell) (xs : List Cell) : Cells (shiftCells d xs) = Shift d (Cells xs) := by
  apply region_ext
  intro x
  simp only [Cells, shiftCells, List.mem_map]
  constructor
  · intro ⟨y,hy,heq⟩
    subst x
    change Add (Neg d) (Add d y) ∈ xs
    simpa using hy
  · intro hx
    exact ⟨Add (Neg d) x, hx, neg_add d x⟩

/-- The same exact finite pair checker applies to arbitrary placed side seams. -/
def SeamCheck (d : Cell) (ts us : List (List Cell)) : Prop :=
  ∀ xs ∈ ts, ∀ ys ∈ us, PairCheck xs (shiftCells d ys)

instance (d : Cell) (ts us : List (List Cell)) : Decidable (SeamCheck d ts us) := by
  unfold SeamCheck
  infer_instance

theorem seamCheck_sound {d : Cell} {ts us : List (List Cell)} (hs : SeamCheck d ts us) :
    ∀ A B, CoordinateTiles ts A → CoordinateTiles us B → Rigid A (Shift d B) := by
  intro A B ha hb
  obtain ⟨xs,hxs,heq⟩ := ha
  obtain ⟨ys,hys,heq'⟩ := hb
  subst A; subst B
  have hp := pairCheck_sound (hs xs hxs ys hys)
  rw [shiftCells_eq] at hp
  exact hp

/-! Kernel-evaluated positive and corruption controls for the finite bridge.
These small controls make no claim about any target witness. -/
example : tileCheck [(0,0),(0,1),(1,1)] = true := by decide
example : tileCheck [(0,0),(0,0),(0,1)] = false := by decide
example : tileCheck [(0,0),(0,1),(2,1)] = false := by decide
example : PairCheck [(0,0),(1,0),(2,0)] [(0,3),(1,3),(2,3)] := by decide
example : ¬ PairCheck [(0,0),(1,0),(2,0)] [(0,1),(1,1),(2,1)] := by decide
example : BlockCheck 3 1 [[(0,0),(1,0),(2,0)]] := by decide
example : ¬ BlockCheck 3 1 [[(0,0),(1,0),(1,0)]] := by decide
example : ¬ BlockCheck 3 1 [[(0,0),(1,0),(3,0)]] := by decide

end LockedTromino
