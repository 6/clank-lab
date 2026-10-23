import Std

/- Exact cover-certificate logic, independent of the group implementation.
   E is multiplication by a reflection, q is rank(I-w), z is identity.
   A length-n walk from c to z is reduced when q(c)=n and q(z)=0.
   No global equality of reflection length and codimension is assumed. -/
namespace IntervalCertificate

universe u
variable {V : Type u}

inductive Walk (E : V → V → Prop) : Nat → V → V → Prop where
  | nil (x : V) : Walk E 0 x x
  | cons {k : Nat} {x y z : V} : E x y → Walk E k y z → Walk E (k+1) x z

def Descent (E : V → V → Prop) (q : V → Nat) (x y : V) : Prop :=
  E x y ∧ q y + 1 = q x

def GeodesicInterval (E : V → V → Prop) (c z : V) (n : Nat) (x : V) : Prop :=
  ∃ k l, k + l = n ∧ Walk E k c x ∧ Walk E l x z

theorem rank_bound {E : V → V → Prop} {q : V → Nat}
    (step : ∀ x y, E x y → q x ≤ q y + 1)
    {k : Nat} {x y : V} (p : Walk E k x y) : q x ≤ q y + k := by
  induction p with
  | nil => omega
  | @cons k x v y edge rest ih =>
    have h := step x v edge
    omega

theorem tight_walk_descends {E : V → V → Prop} {q : V → Nat}
    (step : ∀ x y, E x y → q x ≤ q y + 1)
    {k : Nat} {x y : V} (p : Walk E k x y)
    (tight : q x = q y + k) : Walk (Descent E q) k x y := by
  induction p with
  | nil => exact Walk.nil _
  | @cons k x v y edge rest ih =>
    have h := step x v edge
    have b := rank_bound step rest
    have d : q v + 1 = q x := by omega
    have t : q v = q y + k := by omega
    exact Walk.cons ⟨edge, d⟩ (ih t)

theorem closed_walk {E : V → V → Prop} {S : V → Prop}
    (closed : ∀ x y, S x → E x y → S y)
    {k : Nat} {x y : V} (p : Walk E k x y) (start : S x) : S y := by
  induction p with
  | nil => exact start
  | cons edge rest ih => exact ih (closed _ _ start edge)

/-- Exhaustive closure under rank-decreasing reflection edges cannot miss any
    element on a reduced word from c to identity. -/
theorem complete_cover {E : V → V → Prop} {q : V → Nat}
    {S : V → Prop} {c z : V} {n : Nat}
    (step : ∀ x y, E x y → q x ≤ q y + 1)
    (top : q c = n) (bottom : q z = 0)
    (contains_top : S c)
    (closed : ∀ x y, S x → Descent E q x y → S y)
    {x : V} (member : GeodesicInterval E c z n x) : S x := by
  rcases member with ⟨k, l, total, left, right⟩
  have a := rank_bound step left
  have b := rank_bound step right
  have tight : q c = q x + k := by omega
  exact closed_walk closed (tight_walk_descends step left tight) contains_top

/-- Word witnesses in both directions certify membership; exhaustive closure
    certifies completeness. All hypotheses are explicit checker obligations. -/
theorem exact_interval {E : V → V → Prop} {q : V → Nat}
    {S : V → Prop} {c z : V} {n : Nat}
    (step : ∀ x y, E x y → q x ≤ q y + 1)
    (top : q c = n) (bottom : q z = 0)
    (contains_top : S c)
    (closed : ∀ x y, S x → Descent E q x y → S y)
    (words : ∀ x, S x → GeodesicInterval E c z n x) :
    ∀ x, S x ↔ GeodesicInterval E c z n x := by
  intro x
  constructor
  · exact words x
  · exact complete_cover step top bottom contains_top closed

/-- Each certified vertex has codimension equal to its remaining word length. -/
theorem certified_rank {E : V → V → Prop} {q : V → Nat}
    {c z x : V} {n k l : Nat}
    (step : ∀ x y, E x y → q x ≤ q y + 1)
    (top : q c = n) (bottom : q z = 0)
    (total : k + l = n) (left : Walk E k c x) (right : Walk E l x z) :
    q x = l := by
  have a := rank_bound step left
  have b := rank_bound step right
  omega

#print axioms exact_interval
#print axioms certified_rank
end IntervalCertificate
