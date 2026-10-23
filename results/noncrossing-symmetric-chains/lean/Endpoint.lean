import Std

/-
Endpoint specification, written before the first proof in this folder.
The complex-linear representation/classification interface remains semantic:
`eligible` means exactly finite well-generated complex reflection data and
`coxeter` means componentwise regular elements of largest invariant degree.
No axiom asserts either predicate or the endpoint.  The proved combinatorial
transfer lemmas operate on the explicit interval, rank and cover definitions.
-/
namespace NoncrossingSCD

universe u

structure IntervalData (W : Type u) where
  mul : W → W → W
  inv : W → W
  reflectionLength : W → Nat
  essentialRank : Nat

def AbsoluteLE {W : Type u} (D : IntervalData W) (x y : W) : Prop :=
  D.reflectionLength x + D.reflectionLength (D.mul (D.inv x) y) =
    D.reflectionLength y

def Interval {W : Type u} (D : IntervalData W) (c : W) :=
  {x : W // AbsoluteLE D x c}

def Cover {α : Type u} (le : α → α → Prop) (x y : α) : Prop :=
  le x y ∧ x ≠ y ∧ ∀ z, le x z → le z y → z = x ∨ z = y

/-- A rank-indexed partition into nonempty saturated symmetric chains. -/
structure SCD (α : Type u) (cover : α → α → Prop) (rank : α → Nat) (n : Nat) where
  Label : Type u
  label : α → Label
  bottom : Label → Nat
  top : Label → Nat
  nonempty : ∀ a, bottom a ≤ top a
  symmetric : ∀ a, bottom a + top a = n
  point : (a : Label) → (i : Nat) → bottom a ≤ i → i ≤ top a → α
  point_label : ∀ a i lo hi, label (point a i lo hi) = a
  point_rank : ∀ a i lo hi, rank (point a i lo hi) = i
  bounds : ∀ x, bottom (label x) ≤ rank x ∧ rank x ≤ top (label x)
  recover : ∀ x, point (label x) (rank x) (bounds x).1 (bounds x).2 = x
  saturated : ∀ a i lo hi,
    cover (point a i lo (Nat.le_trans (Nat.le_succ i) hi))
      (point a (i+1) (Nat.le_trans lo (Nat.le_succ i)) hi)

/-- The desired endpoint. `eligible` and `coxeter` are explicit semantic
interfaces, not axioms or silently supplied evidence; this is a proposition
specification and is not proved as an unconditional Lean theorem. -/
def GeneralEndpoint
    (eligible : (W : Type u) → IntervalData W → Prop)
    (coxeter : {W : Type u} → IntervalData W → W → Prop) : Prop :=
  ∀ (W : Type u) (D : IntervalData W), eligible W D → ∀ c, coxeter D c →
    Nonempty (SCD (Interval D c)
      (Cover (fun x y => AbsoluteLE D x.val y.val))
      (fun x => D.reflectionLength x.val) D.essentialRank)

end NoncrossingSCD
