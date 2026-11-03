import Mathlib.Algebra.Group.End
import Mathlib.Algebra.PresentedMonoid.Basic
import Mathlib.Basic.Finite.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Relation

/-! Exact locality-sensitive statement of Collina–D’Andrea
Conjecture 8.1, proved by Faithful.full_endpoint. Ordinary endomorphism
multiplication composes rightmost first. -/

noncomputable section
namespace CD13
universe u v

variable {V : Type u}

def Acyclic (E : V → V → Prop) : Prop := ∀ i, ¬ Relation.TransGen E i i

def Independent (E : V → V → Prop) (i j : V) : Prop :=
  i ≠ j ∧ ¬ E i j ∧ ¬ E j i

inductive HKRel (E : V → V → Prop) : FreeMonoid V → FreeMonoid V → Prop
  | idem (i) : HKRel E [i, i] [i]
  | commute (i j) (h : Independent E i j) : HKRel E [i, j] [j, i]
  | edge_left (i j) (h : E i j) : HKRel E [i, j, i] [i, j]
  | edge_right (i j) (h : E i j) : HKRel E [j, i, j] [i, j]

abbrev HK (E : V → V → Prop) := PresentedMonoid (HKRel E)

structure LocalSystem (E : V → V → Prop) where
  S : V → Type v
  finite : ∀ i, Finite (S i)
  nonempty : ∀ i, Nonempty (S i)
  localFn : ∀ i, ((j : {j // E i j}) → S j.val) → S i

abbrev State {E : V → V → Prop} (D : LocalSystem E) := ∀ i, D.S i

def update {E : V → V → Prop} (D : LocalSystem E) (i : V) :
    Function.End (State D) := by
  classical
  exact fun s => Function.update s i (D.localFn i (fun j => s j.val))

def eval {E : V → V → Prop} (D : LocalSystem E) :
    FreeMonoid V →* Function.End (State D) := FreeMonoid.lift (update D)

/-- The full finite-DAG theorem, including the explicit faithful induced
homomorphism and the bridge through all admissible local evaluation kernels.
No nonempty-vertex assumption, self-coordinate input, degree bound, or
transitivity assumption is present. Conjecture 8.2 is outside this statement. -/
def FullEndpoint : Prop :=
  ∀ (V : Type u) [Finite V] (E : V → V → Prop), Acyclic E →
    ∃ (D : LocalSystem.{u, u} E)
      (ρ : HK E →* Function.End (State D)),
      Function.Injective ρ ∧
      (∀ i, ρ (PresentedMonoid.of (HKRel E) i) = update D i) ∧
      (∀ a b : FreeMonoid V,
        (∀ A : LocalSystem.{u, u} E, eval A a = eval A b) ↔
          PresentedMonoid.mk (HKRel E) a = PresentedMonoid.mk (HKRel E) b)

/-- Chronological schedules use the reverse of a written HK word. Quantifying
all occurrence pairs is equivalent to quantifying consecutive ones. -/
def RepeatProperty (E : V → V → Prop) (w : List V) : Prop :=
  ∀ a p m s, w = p ++ [a] ++ m ++ [a] ++ s →
    (∃ b ∈ m, E b a) ∧ (∃ b ∈ m, E a b)

end CD13
