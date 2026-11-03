import Antony24.Basic

/-! Local colour facts. Every finite table is
proved by Lean's kernel-evaluated `decide`; no native evaluator is used. -/
namespace Antony24

def Extreme (a : Colour) : Prop := a = 0 ∨ a = 3

def StarOK (a b c d : Colour) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧
    diff a b ≠ diff a c ∧ diff a b ≠ diff a d ∧ diff a c ≠ diff a d

def PathOK (a x y b : Colour) : Prop :=
  a ≠ x ∧ x ≠ y ∧ y ≠ b ∧
    diff a x ≠ diff x y ∧ diff x y ≠ diff y b

instance (a b c d : Colour) : Decidable (StarOK a b c d) := by
  unfold StarOK
  infer_instance

instance (a x y b : Colour) : Decidable (PathOK a x y b) := by
  unfold PathOK
  infer_instance

instance (a : Colour) : Decidable (Extreme a) := by
  unfold Extreme
  infer_instance

/-- A cubic vertex uses one of the two extreme colours. -/
theorem star_extreme (a b c d : Colour) (h : StarOK a b c d) : Extreme a := by
  revert a b c d
  decide

/-- Its three port differences are a permutation of 1, 2, 3. -/
theorem star_ports (a b c d : Colour) (h : StarOK a b c d) :
    (diff a b = 1 ∧ diff a c = 2 ∧ diff a d = 3) ∨
    (diff a b = 1 ∧ diff a c = 3 ∧ diff a d = 2) ∨
    (diff a b = 2 ∧ diff a c = 1 ∧ diff a d = 3) ∨
    (diff a b = 2 ∧ diff a c = 3 ∧ diff a d = 1) ∨
    (diff a b = 3 ∧ diff a c = 1 ∧ diff a d = 2) ∨
    (diff a b = 3 ∧ diff a c = 2 ∧ diff a d = 1) := by
  revert a b c d
  decide

def starPort (a b c d : Colour) (i : Fin 3) : ℕ :=
  if i = 0 then diff a b else if i = 1 then diff a c else diff a d

/-- Each possible nonzero difference occurs at exactly one of the three ports. -/
theorem star_exists_unique_port (a b c d : Colour) (h : StarOK a b c d)
    (k : Fin 3) : ∃! i : Fin 3, starPort a b c d i = k.val + 1 := by
  revert a b c d k
  unfold ExistsUnique
  decide

/-- Complete port table for a length-three path with extreme endpoints. -/
theorem path_ports (a x y b : Colour) (ha : Extreme a) (hb : Extreme b)
    (h : PathOK a x y b) :
    (a ≠ b ∧ diff a x = 2 ∧ diff b y = 2) ∨
    (a = b ∧ ((diff a x = 1 ∧ diff b y = 3) ∨
      (diff a x = 3 ∧ diff b y = 1) ∨
      (diff a x = 2 ∧ diff b y = 3) ∨
      (diff a x = 3 ∧ diff b y = 2))) := by
  revert a x y b
  decide

theorem path_one_three (a x y b : Colour) (ha : Extreme a) (hb : Extreme b)
    (h : PathOK a x y b) (hp : diff a x = 1) : diff b y = 3 := by
  revert a x y b
  decide

theorem path_two_cases (a x y b : Colour) (ha : Extreme a) (hb : Extreme b)
    (h : PathOK a x y b) (hp : diff a x = 2) :
    diff b y = 2 ∨ diff b y = 3 := by
  revert a x y b
  decide

theorem path_three_cases (a x y b : Colour) (ha : Extreme a) (hb : Extreme b)
    (h : PathOK a x y b) (hp : diff a x = 3) :
    diff b y = 1 ∨ diff b y = 2 := by
  revert a x y b
  decide

theorem path_opposite_iff (a x y b : Colour) (ha : Extreme a) (hb : Extreme b)
    (h : PathOK a x y b) :
    (a ≠ b ↔ diff a x = 2 ∧ diff b y = 2) := by
  revert a x y b
  decide

theorem path_same_iff (a x y b : Colour) (ha : Extreme a) (hb : Extreme b)
    (h : PathOK a x y b) :
    (a = b ↔ diff a x ≠ 2 ∨ diff b y ≠ 2) := by
  revert a x y b
  decide

theorem path_reverse (a x y b : Colour) (h : PathOK a x y b) :
    PathOK b y x a := by
  revert a x y b
  decide

/-- Exact existence table, including all witnesses needed by the converse. -/
theorem exists_path_iff (a b p q : Colour) (ha : Extreme a) (hb : Extreme b) :
    (∃ x y : Colour, PathOK a x y b ∧ diff a x = p.val ∧ diff b y = q.val) ↔
    ((a ≠ b ∧ p = 2 ∧ q = 2) ∨
      (a = b ∧ ((p = 1 ∧ q = 3) ∨ (p = 3 ∧ q = 1) ∨
        (p = 2 ∧ q = 3) ∨ (p = 3 ∧ q = 2)))) := by
  revert a b p q
  decide

/-- The unique colour at distance `p` from an extreme endpoint. -/
def portColour (a p : Colour) : Colour :=
  if a = 0 then p else ⟨3 - p.val, by omega⟩

theorem diff_portColour (a p : Colour) (ha : Extreme a) :
    diff a (portColour a p) = p.val := by
  revert a p
  decide

/-- A deterministic choice of the two interior colours for every allowed pair. -/
theorem path_portColour (a b p q : Colour) (ha : Extreme a) (hb : Extreme b)
    (hpq : (a ≠ b ∧ p = 2 ∧ q = 2) ∨
      (a = b ∧ ((p = 1 ∧ q = 3) ∨ (p = 3 ∧ q = 1) ∨
        (p = 2 ∧ q = 3) ∨ (p = 3 ∧ q = 2)))) :
    PathOK a (portColour a p) (portColour b q) b := by
  revert a b p q
  decide

end Antony24
