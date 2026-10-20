import Uniform5.CompositionCaseBActualDomains
import Uniform5.CompositionFanHalfspaces

/-! Coordinate-independent geometric instances of the paper's W input.
Only finite parameter instances enter the classification. The compact
rescaled boundary charts are not represented by ambient limiting halfspaces.
The input asserts the finite restriction of the two W inequalities; incidence and the
identification of an actual fan with an instance are separate proof tasks. -/
noncomputable section
namespace Uniform5.Composition.Wedge
open Set
open scoped RealInnerProductSpace

abbrev Parameter := CaseB.PolygonParameter

/-- The compactified polygon chord, including its literal value at infinity. -/
def parameterChord : Parameter → ℝ
  | none => 2
  | some n => CaseB.chord n

/-- The vertex-figure hyperplane is normalized to allow infinite radii:
finite fans have offset 1/(2R), and compact boundary fans have offset zero. -/
structure Geometry where
  root : Space 5
  normal : Space 5
  offset : ℝ
  vertices : Finset (Space 5)
  ends : Finset (Space 5)
  halfspaces : Set (Set (Space 5))
  specialPair : Space 5 → Space 5 → Prop

def Geometry.OnFigureSphere (F : Geometry) (p : Space 5) : Prop :=
  dist p F.root = 1 ∧ ⟪p - F.root, F.normal⟫ = F.offset

def Geometry.Admissible (F : Geometry) (p : Space 5) : Prop :=
  F.OnFigureSphere p ∧ (∀ H ∈ F.halfspaces, p ∈ H) ∧
    ∀ a ∈ F.vertices, 1 ≤ dist p a

def Geometry.Allowed (F : Geometry) (p : Space 5) : Prop :=
  p ∈ F.vertices ∧ p ∉ F.ends

def atInfinity (n : Parameter) : CaseB.WFan → Prop
  | .pairedI m _ | .pairedII m => n = none ∨ m = none
  | _ => n = none

def pair (a b p q : Space 5) : Prop := (p = a ∧ q = b) ∨ (p = b ∧ q = a)

/-- A finite fan facet's supporting cone hyperplane is oriented by the
other fan vertices and the strict centre direction. No containment of any
parent polytope is assumed. -/
def SupportingHalfspace (F : Geometry) (B H : Set (Space 5)) : Prop :=
  ∃ L : Space 5 →L[ℝ] ℝ, L ≠ 0 ∧
    H = {p | L (p - F.root) ≤ 0} ∧
    (affineSpan ℝ (insert F.root B) : Set (Space 5)) =
      {p | L (p - F.root) = 0} ∧
    (∀ p ∈ F.vertices, L (p - F.root) ≤ 0) ∧
    L F.normal < 0

/-- Common literal data of a fan: all vertices on its figure sphere,
all whole fan facets, and their uniquely oriented supporting halfspaces. -/
def Realizes (n : Parameter) (f : CaseB.WFan) (F : Geometry)
    (points : Finset (Space 5)) (facets : Set (Set (Space 5)))
    (ends : Finset (Space 5)) (special : Space 5 → Space 5 → Prop) : Prop :=
  ‖F.normal‖ = 1 ∧ 0 ≤ F.offset ∧ F.offset < 1 ∧
    (F.offset = 0 ↔ atInfinity n f) ∧
    F.vertices = points ∧ F.ends = ends ∧ F.specialPair = special ∧
    (∀ p ∈ points, F.OnFigureSphere p) ∧
    (∀ B ∈ facets, ∃ H, SupportingHalfspace F B H) ∧
    F.halfspaces = {H | ∃ B ∈ facets, SupportingHalfspace F B H}

/-- Type-I lateral points are the vertices, in cyclic order, of their
actual planar convex polygon. This excludes star-polygon orderings. -/
structure TypeIShape (n : Parameter) (c : List Parameter) where
  length_ge : 3 ≤ c.length
  length_le : c.length ≤ 5
  a : Space 5
  b : Space 5
  x : Fin c.length → Space 5
  ab : dist a b = parameterChord n
  cross_a : ∀ i, dist a (x i) = Real.sqrt 2
  cross_b : ∀ i, dist b (x i) = Real.sqrt 2
  consecutive : ∀ i, dist (x i) (x (finRotate c.length i)) = parameterChord (c.get i)
  planar : affineDimension (convexHull ℝ (Set.range x)) = 2
  vertices : (convexHull ℝ (Set.range x)).extremePoints ℝ = Set.range x
  cyclic_edges : ∀ i, Edge (convexHull ℝ (Set.range x)) (x i) (x (finRotate c.length i))
  injective : Function.Injective x

namespace TypeIShape
variable {n : Parameter} {c : List Parameter} (T : TypeIShape n c)
def points : Finset (Space 5) := {T.a, T.b} ∪ Finset.univ.image T.x
def facets : Set (Set (Space 5)) := Set.range fun i : Fin c.length =>
  convexHull ℝ ({T.a, T.b, T.x i, T.x (finRotate c.length i)} : Set (Space 5))
def diagonal (p q : Space 5) : Prop :=
  ∃ i j, i ≠ j ∧ finRotate c.length i ≠ j ∧ finRotate c.length j ≠ i ∧
    p = T.x i ∧ q = T.x j
noncomputable def first : Fin c.length := ⟨0, by have := T.length_ge; omega⟩
def partner (p q : Space 5) : Prop := pair (T.x T.first) (T.x (finRotate c.length T.first)) p q
end TypeIShape

/-- The trapezoid is specified by all six exact F3 distances. -/
structure Trapezoid (n : Parameter) where
  a : Space 5
  b : Space 5
  x : Space 5
  y : Space 5
  ab : dist a b = parameterChord n
  xy : dist x y = 1
  ax : dist a x = 1
  by_ : dist b y = 1
  ay : dist a y ^ 2 = 1 + parameterChord n
  bx : dist b x ^ 2 = 1 + parameterChord n

structure TypeIIShape (n m : Parameter) extends Trapezoid n where
  z₁ : Space 5
  z₂ : Space 5
  apex_distances : ∀ z ∈ ({z₁, z₂} : Finset (Space 5)),
    ∀ p ∈ ({a, b, x, y} : Finset (Space 5)), dist p z = Real.sqrt 2
  partner_chord : dist z₁ z₂ = parameterChord m

namespace TypeIIShape
variable {n m : Parameter} (T : TypeIIShape n m)
def points : Finset (Space 5) := {T.a, T.b, T.x, T.y, T.z₁, T.z₂}
def facets : Set (Set (Space 5)) :=
  {convexHull ℝ ({T.a, T.b, T.x, T.y, T.z₁} : Set (Space 5)),
   convexHull ℝ ({T.a, T.b, T.x, T.y, T.z₂} : Set (Space 5)),
   convexHull ℝ ({T.a, T.b, T.z₁, T.z₂} : Set (Space 5))}
end TypeIIShape

structure TypeIIIShape (n : Parameter) (q₁ q₂ : ℕ) extends Trapezoid n where
  z₁ : Space 5
  z₂ : Space 5
  w : Space 5
  apex_distances : ∀ z ∈ ({z₁, z₂} : Finset (Space 5)),
    ∀ p ∈ ({a, b, x, y} : Finset (Space 5)), dist p z = Real.sqrt 2
  lateral_a : dist a w = Real.sqrt 2
  lateral_b : dist b w = Real.sqrt 2
  first_chord : dist z₁ w = CaseB.chord q₁
  second_chord : dist w z₂ = CaseB.chord q₂
  apex_distinct : z₁ ≠ z₂

namespace TypeIIIShape
variable {n : Parameter} {q₁ q₂ : ℕ} (T : TypeIIIShape n q₁ q₂)
def points : Finset (Space 5) := {T.a, T.b, T.x, T.y, T.z₁, T.z₂, T.w}
def facets : Set (Set (Space 5)) :=
  {convexHull ℝ ({T.a, T.b, T.x, T.y, T.z₁} : Set (Space 5)),
   convexHull ℝ ({T.a, T.b, T.x, T.y, T.z₂} : Set (Space 5)),
   convexHull ℝ ({T.a, T.b, T.z₁, T.w} : Set (Space 5)),
   convexHull ℝ ({T.a, T.b, T.w, T.z₂} : Set (Space 5))}
end TypeIIIShape

/-- The literal fan list in W, with the same paired endpoints and the
same exempt type-I diagonals as the paper. -/
def RealizesFiniteFan (n : Parameter) : CaseB.WFan → Geometry → Prop
  | .unpairedI c, F => ∃ T : TypeIShape n (c.map fun q => some (q : ℝ)),
      Realizes n (.unpairedI c) F T.points T.facets {T.a, T.b}
        (fun p q => pair T.a T.b p q ∨ T.diagonal p q)
  | .pairedI m c, F => ∃ T : TypeIShape n (m :: c.map fun q => some (q : ℝ)),
      Realizes n (.pairedI m c) F T.points T.facets
        {T.a, T.b, T.x T.first, T.x (finRotate _ T.first)}
        (fun p q => pair T.a T.b p q ∨ T.partner p q ∨ T.diagonal p q)
  | .unpairedII q, F => ∃ T : TypeIIShape n (some (q : ℝ)),
      Realizes n (.unpairedII q) F T.points T.facets {T.a, T.b} (pair T.a T.b)
  | .pairedII m, F => ∃ T : TypeIIShape n m,
      Realizes n (.pairedII m) F T.points T.facets {T.a, T.b, T.z₁, T.z₂}
        (fun p q => pair T.a T.b p q ∨ pair T.z₁ T.z₂ p q)
  | .unpairedIII q₁ q₂, F => ∃ T : TypeIIIShape n q₁ q₂,
      Realizes n (.unpairedIII q₁ q₂) F T.points T.facets {T.a, T.b} (pair T.a T.b)

/-- Actual polygon parameters are finite. -/
def finiteParameters (n : Parameter) (f : CaseB.WFan) : Prop := ¬ atInfinity n f

/-- The finite-parameter restriction of the paper's W domain. The unused
`p1` argument preserves the application interface; listing still depends on
P1 through `WListed`. No ambient-halfspace limit is a certified W chart. -/
def RealizesWFan (_p1 : CaseB.P1) (n : Parameter) (f : CaseB.WFan) (F : Geometry) : Prop :=
  finiteParameters n f ∧ RealizesFiniteFan n f F

/-- The finite-parameter restriction of computed W, with its exact listed
real/integer parameter ranges, admissibility, endpoint exclusions and both
distance conclusions. This is weaker than the paper's full rescaled-chart
claim and is sufficient for actual polytopes. It is an explicit parameter. -/
structure W (p1 : CaseB.P1) : Prop where
  no_long_pair : ∀ n f, CaseB.LargeParameter n → CaseB.WListed p1 n f →
    ∀ F, RealizesWFan p1 n f F → ∀ p q,
    (F.Admissible p ∨ F.Allowed p) → (F.Admissible q ∨ F.Allowed q) →
    CaseB.chord 17 ≤ dist p q → p ∈ F.vertices ∧ q ∈ F.vertices
  fan_distances : ∀ n f, CaseB.LargeParameter n → CaseB.WListed p1 n f →
    ∀ F, RealizesWFan p1 n f F → ∀ p ∈ F.vertices, ∀ q ∈ F.vertices,
    ¬ F.specialPair p q → dist p q < CaseB.chord 17

end Uniform5.Composition.Wedge
