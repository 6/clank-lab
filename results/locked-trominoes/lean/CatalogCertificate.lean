import LocalCertificate

namespace LockedTromino

abbrev Pattern := List Cell × List Cell
structure LinkData where
  target : List Cell
  index : Nat
  offset : Cell
  flip : Bool
  deriving DecidableEq
structure EntryData where
  cells : List Cell
  links : List LinkData
  deriving DecidableEq

def localEntries (es : List EntryData) : List LocalEntry :=
  es.map fun e => ⟨e.cells, e.links.map LinkData.target⟩

def MatchLink (catalog : Nat → Pattern) (xs : List Cell) (link : LinkData) : Prop :=
  let p := catalog link.index
  let a := if link.flip then p.2 else p.1
  let b := if link.flip then p.1 else p.2
  SameCells xs (shiftCells link.offset a) ∧
    SameCells link.target (shiftCells link.offset b)

instance (catalog : Nat → Pattern) (xs : List Cell) (link : LinkData) :
    Decidable (MatchLink catalog xs link) := by unfold MatchLink; infer_instance

def CatalogLinksCheck (catalog : Nat → Pattern) (es : List EntryData) : Prop :=
  ∀ e ∈ es, ∀ link ∈ e.links, MatchLink catalog e.cells link

instance (catalog : Nat → Pattern) (es : List EntryData) : Decidable (CatalogLinksCheck catalog es) := by
  unfold CatalogLinksCheck
  exact @List.decidableBAll EntryData _ (fun e =>
    @List.decidableBAll LinkData _ (fun _ => inferInstance) e.links) es

theorem catalogLinks_sound {catalog : Nat → Pattern}
    (hp : ∀ k, Rigid (Cells (catalog k).1) (Cells (catalog k).2))
    {es : List EntryData} (hc : CatalogLinksCheck catalog es) : CertifiedLinks (localEntries es) := by
  intro e he ys hys
  obtain ⟨entry,hentry,heq⟩ := List.mem_map.mp he
  subst e
  obtain ⟨link,hlink,heq⟩ := List.mem_map.mp hys
  subst ys
  have hm := hc entry hentry link hlink
  unfold MatchLink at hm
  cases hf : link.flip
  · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hm
    exact rigid_from_pattern link.offset (hp link.index) hm.1 hm.2
  · simp only [hf, ↓reduceIte] at hm
    exact rigid_from_pattern link.offset (rigid_symm (hp link.index)) hm.1 hm.2

theorem catalog_getD_sound {ps : List Pattern} {fallback : Pattern}
    (hp : ∀ p ∈ ps, Rigid (Cells p.1) (Cells p.2))
    (hf : Rigid (Cells fallback.1) (Cells fallback.2)) :
    ∀ k : Nat, Rigid (Cells (ps[k]?.getD fallback).1) (Cells (ps[k]?.getD fallback).2) := by
  intro k
  cases he : ps[k]? with
  | none => exact hf
  | some p => exact hp p (List.mem_of_getElem? he)

/-- An owner table uses the natural-coordinate row-major index. Out-of-range
values do not matter: every use is guarded by the exact rectangle. -/
def tableOwner (w : Nat) (ts : List (List Cell)) (indices : List Nat) : Cell → List Cell :=
  fun x => ts[indices[x.1.toNat * w + x.2.toNat]?.getD 0]?.getD []

theorem side_disjoint (h w k v : Nat) :
    Disjoint (Rectangle h w) (Shift (h,0) (Rectangle k v)) ∧
    Disjoint (Rectangle h w) (Shift (0,w) (Rectangle k v)) := by
  constructor <;> intro x hx hy <;> unfold Rectangle at hx <;>
    unfold Shift Rectangle Add Neg at hy <;> dsimp at hy <;> omega

end LockedTromino
