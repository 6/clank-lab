/-!
# Köhler-Schindler–Steif, Question 2.1: a monotone counterexample

Points of {0,1}^5 are the naturals x < 32, with coordinate x_i = x.testBit i.
The measure is uniform (p = 1/2), so an expectation is a sum over the 32
points divided by 32. A set of queried bits is a mask m.

Statement (`answer` at the end):
* `f1` is monotone;
* every query algorithm that stops only once f1 is determined makes, summed
  over the 32 inputs, at least 104 queries until f1 is determined, and one
  makes exactly 104: a(f1, π_{1/2}) = 104/32 = 13/4;
* an explicit subcube partition on whose cells f1 is constant has summed
  codimension 102: sc(f1, π_{1/2}) ≤ 102/32 = 51/16 < 13/4.

Core Lean only; finite facts are checked with `decide +kernel`.
-/

set_option linter.deprecated false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

namespace KS24

/-- f1 = x1 x2 x3 ∨ x0 x4 (x1 ∨ x2 ∨ x3). -/
def f1 (x : Nat) : Bool :=
  (x.testBit 1 && x.testBit 2 && x.testBit 3) ||
  (x.testBit 0 && x.testBit 4 && (x.testBit 1 || x.testBit 2 || x.testBit 3))

/-- Monotone: x ≤ y coordinatewise implies f1 x ≤ f1 y. -/
def Monotone : Prop :=
  ∀ x < 32, ∀ y < 32, (∀ i < 5, x.testBit i = true → y.testBit i = true) →
    f1 x = true → f1 y = true

/-- After querying the bits in m on input x, f1 is determined: every point
agreeing with x on m has the same value. -/
def Determined (m x : Nat) : Prop :=
  ∀ y < 32, y &&& m = x &&& m → f1 y = f1 x

instance (m x : Nat) : Decidable (Determined m x) := by
  unfold Determined; exact inferInstance

/-- An adaptive query algorithm (a decision tree): `query i t0 t1` asks for
x_i and continues with t0 if x_i = 0, with t1 if x_i = 1. -/
inductive Alg where
  | stop : Alg
  | query : Fin 5 → Alg → Alg → Alg

/-- The number of queries made on x, having already queried m, until f1 is
determined. -/
def cost : Alg → Nat → Nat → Nat
  | .stop, _, _ => 0
  | .query i t0 t1, m, x =>
      if Determined m x then 0
      else 1 + (if x.testBit i then cost t1 (m ||| 2 ^ i.val) x else cost t0 (m ||| 2 ^ i.val) x)

/-- The algorithm only stops once f1 is determined. -/
def Correct : Alg → Nat → Nat → Prop
  | .stop, m, x => Determined m x
  | .query i t0 t1, m, x =>
      Determined m x ∨
        (if x.testBit i then Correct t1 (m ||| 2 ^ i.val) x else Correct t0 (m ||| 2 ^ i.val) x)

/-- Σ_{x < k} g x. -/
def bsum : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | k + 1, g => bsum k g + g k

/-- Summed query count over the 32 equally likely inputs (32 · expectation). -/
def totalCost (A : Alg) : Nat := bsum 32 (fun x => cost A 0 x)

/-- A subcube is a pair (m, v): the points y with y &&& m = v. -/
def inCube (c : Nat × Nat) (y : Nat) : Bool := y &&& c.1 == c.2

/-- The number of the five bits a mask fixes. -/
def codim (m : Nat) : Nat := ((List.range 5).filter (fun i => m.testBit i)).length

/-- Every point lies in exactly one cell. -/
def IsPartition (P : List (Nat × Nat)) : Prop :=
  ∀ x < 32, (P.filter (fun c => inCube c x)).length = 1

/-- f1 is constant on every cell. -/
def Determines (P : List (Nat × Nat)) : Prop :=
  ∀ c ∈ P, ∀ y < 32, ∀ z < 32, inCube c y = true → inCube c z = true → f1 y = f1 z

/-- The codimension of the cell containing x. -/
def cellCodim (P : List (Nat × Nat)) (x : Nat) : Nat :=
  match P.find? (fun c => inCube c x) with
  | some c => codim c.1
  | none => 0

/-- Summed codimension over the 32 inputs (32 · expectation). -/
def totalCodim (P : List (Nat × Nat)) : Nat := bsum 32 (cellCodim P)

/-! ## The witnesses -/

def tree : Alg :=
  (.query 0 (.query 1 .stop (.query 2 .stop (.query 3 .stop .stop)))
    (.query 1 (.query 4 .stop (.query 2 (.query 3 .stop .stop) .stop))
      (.query 4 (.query 2 .stop (.query 3 .stop .stop)) .stop)))

/-- 00***; 01*0*; *111*; 0101*; 1*0*0; 110*1; 101*0; 10*11; 1*101; 10001;
11100 (character i is x_i), as (mask, value) pairs. -/
def partition : List (Nat × Nat) :=
  [(3, 0), (11, 2), (14, 14), (15, 10), (21, 1), (23, 19), (23, 5), (27, 25),
   (29, 21), (31, 17), (31, 7)]

/-! ## The dynamic program -/

def detB (m v : Nat) : Bool := (List.range 32).all (fun y => y &&& m != v || f1 y == f1 v)

def cnt (m v : Nat) : Nat := bsum 32 (fun x => if x &&& m = v then 1 else 0)

def minFree (m : Nat) (g : Nat → Nat) : Nat :=
  (List.range 5).foldr (fun i acc => if m.testBit i then acc else min (g i) acc) 1000

/-- Optimal summed query count over the points of the cube (m, v), k free bits. -/
def V : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | k + 1, m, v =>
      if detB m v then 0
      else minFree m (fun i => cnt m v + V k (m ||| 2 ^ i) v + V k (m ||| 2 ^ i) (v ||| 2 ^ i))

/-- The number of free bits. -/
def fc (m : Nat) : Nat := ((List.range 5).filter (fun i => !m.testBit i)).length

theorem V_root : V 5 0 0 = 104 := by decide +kernel

/-! ## Lemmas -/

theorem bsum_congr {k : Nat} {f g : Nat → Nat} (h : ∀ x < k, f x = g x) :
    bsum k f = bsum k g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [bsum]
    rw [ih (fun x hx => h x (by omega)), h k (by omega)]

theorem bsum_add (k : Nat) (f g : Nat → Nat) :
    bsum k (fun x => f x + g x) = bsum k f + bsum k g := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [bsum, ih]; omega

theorem minFree_le_aux (m : Nat) (g : Nat → Nat) (l : List Nat) (i : Nat)
    (hi : i ∈ l) (hm : m.testBit i = false) :
    l.foldr (fun i acc => if m.testBit i then acc else min (g i) acc) 1000 ≤ g i := by
  induction l with
  | nil => cases hi
  | cons j l ih =>
    simp only [List.foldr]
    cases List.mem_cons.mp hi with
    | inl h => subst h; simp [hm, Nat.min_le_left]
    | inr h =>
      have := ih h
      split
      · exact this
      · exact Nat.le_trans (Nat.min_le_right _ _) this

theorem minFree_le (m : Nat) (g : Nat → Nat) (i : Nat) (hi : i < 5)
    (hm : m.testBit i = false) : minFree m g ≤ g i :=
  minFree_le_aux m g _ i (List.mem_range.mpr hi) hm

/-! Finite bit facts, checked by the kernel. -/

theorem fact_split0 : ∀ i < 5, ∀ m < 32, ∀ v < 32, ∀ x < 32,
    m.testBit i = false → v &&& m = v →
    (x &&& (m ||| 2 ^ i) = v ↔ (x &&& m = v ∧ x.testBit i = false)) := by decide +kernel

theorem fact_split1 : ∀ i < 5, ∀ m < 32, ∀ v < 32, ∀ x < 32,
    m.testBit i = false → v &&& m = v →
    (x &&& (m ||| 2 ^ i) = v ||| 2 ^ i ↔ (x &&& m = v ∧ x.testBit i = true)) := by
  decide +kernel

theorem fact_fixed : ∀ i < 5, ∀ m < 32, ∀ v < 32, ∀ x < 32,
    m.testBit i = true → x &&& m = v → x.testBit i = v.testBit i := by decide +kernel

theorem fact_or_fixed : ∀ i < 5, ∀ m < 32, m.testBit i = true → m ||| 2 ^ i = m := by
  decide +kernel

theorem fact_free : ∀ i < 5, ∀ m < 32, ∀ v < 32, m.testBit i = false → v &&& m = v →
    m ||| 2 ^ i < 32 ∧ v ||| 2 ^ i < 32 ∧ v &&& (m ||| 2 ^ i) = v ∧
    (v ||| 2 ^ i) &&& (m ||| 2 ^ i) = v ||| 2 ^ i := by decide +kernel

theorem fact_fc' : ∀ i < 5, ∀ m < 32, m.testBit i = false → fc (m ||| 2 ^ i) + 1 = fc m := by
  decide +kernel

theorem det_iff (m v x : Nat) (hv : v < 32) (hx32 : x < 32) (hvm : v &&& m = v)
    (hx : x &&& m = v) : Determined m x ↔ detB m v = true := by
  unfold Determined detB
  rw [List.all_eq_true]
  constructor
  · intro h y hy
    by_cases hc : y &&& m = v
    · have h1 := h y (List.mem_range.mp hy) (by rw [hc, hx])
      have h2 := h v hv (by rw [hvm, hx])
      simp [h1, h2]
    · simp [hc]
  · intro h y hy hc
    have h1 := h y (List.mem_range.mpr hy)
    have h2 := h x (List.mem_range.mpr hx32)
    simp [hc, hx] at h1 h2
    rw [h1, h2]

/-! ## The lower bound -/

theorem main_lb (A : Alg) : ∀ (k m v : Nat), m < 32 → v < 32 → v &&& m = v → fc m = k →
    (∀ x < 32, x &&& m = v → Correct A m x) →
    V k m v ≤ bsum 32 (fun x => if x &&& m = v then cost A m x else 0) := by
  induction A with
  | stop =>
    intro k m v hm hv hvm hk hc
    cases k with
    | zero => simp [V]
    | succ k =>
      have hd : detB m v = true := (det_iff m v v hv hv hvm hvm).mp (hc v hv hvm)
      simp [V, hd]
  | query i t0 t1 ih0 ih1 =>
    intro k m v hm hv hvm hk hc
    cases k with
    | zero => simp [V]
    | succ k =>
      by_cases hd : detB m v = true
      · simp [V, hd]
      have hnd : ∀ x < 32, x &&& m = v → ¬ Determined m x := fun x hx32 hx h =>
        hd ((det_iff m v x hv hx32 hvm hx).mp h)
      have hcostx : ∀ x < 32, x &&& m = v → cost (.query i t0 t1) m x =
          1 + (if x.testBit i.val then cost t1 (m ||| 2 ^ i.val) x
            else cost t0 (m ||| 2 ^ i.val) x) := by
        intro x hx32 hx; simp only [cost, if_neg (hnd x hx32 hx)]
      have hcorr : ∀ x < 32, x &&& m = v →
          (if x.testBit i.val then Correct t1 (m ||| 2 ^ i.val) x
            else Correct t0 (m ||| 2 ^ i.val) x) := by
        intro x hx32 hx
        have := hc x hx32 hx
        simp only [Correct] at this
        exact this.resolve_left (hnd x hx32 hx)
      have hi5 : i.val < 5 := i.isLt
      cases hb : m.testBit i.val with
      | true =>
        have hmm : m ||| 2 ^ i.val = m := fact_or_fixed i.val hi5 m hm hb
        have hbr : ∀ x < 32, x &&& m = v → x.testBit i.val = v.testBit i.val :=
          fun x hx32 hx => fact_fixed i.val hi5 m hm v hv x hx32 hb hx
        cases hvb : v.testBit i.val with
        | false =>
          have key := ih0 (k + 1) m v hm hv hvm hk (fun x hx32 hx => by
            have := hcorr x hx32 hx
            rw [hbr x hx32 hx, hvb, hmm] at this
            simpa using this)
          have heq : bsum 32 (fun x => if x &&& m = v then cost (.query i t0 t1) m x else 0) =
              bsum 32 (fun x => (if x &&& m = v then 1 else 0) +
                (if x &&& m = v then cost t0 m x else 0)) := by
            apply bsum_congr; intro x hx32
            by_cases hx : x &&& m = v
            · rw [if_pos hx, if_pos hx, if_pos hx, hcostx x hx32 hx, hbr x hx32 hx, hvb, hmm]
              simp
            · simp [hx]
          rw [heq, bsum_add]; omega
        | true =>
          have key := ih1 (k + 1) m v hm hv hvm hk (fun x hx32 hx => by
            have := hcorr x hx32 hx
            rw [hbr x hx32 hx, hvb, hmm] at this
            simpa using this)
          have heq : bsum 32 (fun x => if x &&& m = v then cost (.query i t0 t1) m x else 0) =
              bsum 32 (fun x => (if x &&& m = v then 1 else 0) +
                (if x &&& m = v then cost t1 m x else 0)) := by
            apply bsum_congr; intro x hx32
            by_cases hx : x &&& m = v
            · rw [if_pos hx, if_pos hx, if_pos hx, hcostx x hx32 hx, hbr x hx32 hx, hvb, hmm]
              simp
            · simp [hx]
          rw [heq, bsum_add]; omega
      | false =>
        obtain ⟨hm', hv', hvm', hvm''⟩ := fact_free i.val hi5 m hm v hv hb hvm
        have hk' : fc (m ||| 2 ^ i.val) = k := by
          have := fact_fc' i.val hi5 m hm hb; omega
        have k0 := ih0 k _ v hm' hv hvm' hk' (fun x hx32 hx => by
          obtain ⟨hx1, hx2⟩ := (fact_split0 i.val hi5 m hm v hv x hx32 hb hvm).mp hx
          have := hcorr x hx32 hx1
          rw [hx2] at this
          simpa using this)
        have k1 := ih1 k _ (v ||| 2 ^ i.val) hm' hv' hvm'' hk' (fun x hx32 hx => by
          obtain ⟨hx1, hx2⟩ := (fact_split1 i.val hi5 m hm v hv x hx32 hb hvm).mp hx
          have := hcorr x hx32 hx1
          rw [hx2] at this
          simpa using this)
        have heq : bsum 32 (fun x => if x &&& m = v then cost (.query i t0 t1) m x else 0) =
            bsum 32 (fun x => (if x &&& m = v then 1 else 0) +
              ((if x &&& (m ||| 2 ^ i.val) = v then cost t0 (m ||| 2 ^ i.val) x else 0) +
               (if x &&& (m ||| 2 ^ i.val) = v ||| 2 ^ i.val
                then cost t1 (m ||| 2 ^ i.val) x else 0))) := by
          apply bsum_congr; intro x hx32
          have s0 := fact_split0 i.val hi5 m hm v hv x hx32 hb hvm
          have s1 := fact_split1 i.val hi5 m hm v hv x hx32 hb hvm
          by_cases hx : x &&& m = v
          · rw [if_pos hx, if_pos hx, hcostx x hx32 hx]
            cases hxb : x.testBit i.val with
            | false =>
              have e0 : x &&& (m ||| 2 ^ i.val) = v := s0.mpr ⟨hx, hxb⟩
              have e1 : ¬ (x &&& (m ||| 2 ^ i.val) = v ||| 2 ^ i.val) := fun h => by
                have := (s1.mp h).2; rw [hxb] at this; cases this
              rw [if_pos e0, if_neg e1]; simp
            | true =>
              have e0 : ¬ (x &&& (m ||| 2 ^ i.val) = v) := fun h => by
                have := (s0.mp h).2; rw [hxb] at this; cases this
              have e1 : x &&& (m ||| 2 ^ i.val) = v ||| 2 ^ i.val := s1.mpr ⟨hx, hxb⟩
              rw [if_neg e0, if_pos e1]; simp
          · have n0 : ¬ (x &&& (m ||| 2 ^ i.val) = v) := fun h => hx (s0.mp h).1
            have n1 : ¬ (x &&& (m ||| 2 ^ i.val) = v ||| 2 ^ i.val) := fun h => hx (s1.mp h).1
            rw [if_neg hx, if_neg hx, if_neg n0, if_neg n1]
        have hmin : V (k + 1) m v ≤
            cnt m v + V k (m ||| 2 ^ i.val) v + V k (m ||| 2 ^ i.val) (v ||| 2 ^ i.val) := by
          have hd' : detB m v = false := by cases h : detB m v <;> simp_all
          simp only [V, hd', Bool.false_eq_true, if_false]
          exact minFree_le m _ i.val hi5 hb
        rw [heq, bsum_add, bsum_add]
        unfold cnt at hmin
        omega

theorem lower_bound (A : Alg) (hA : ∀ x < 32, Correct A 0 x) : 104 ≤ totalCost A := by
  have h := main_lb A 5 0 0 (by decide) (by decide) (by decide) (by decide)
    (fun x hx _ => hA x hx)
  rw [V_root] at h
  unfold totalCost
  have e : bsum 32 (fun x => if x &&& 0 = 0 then cost A 0 x else 0) =
      bsum 32 (fun x => cost A 0 x) := bsum_congr (fun x _ => by simp)
  omega

/-! ## The upper bound and the partition -/

def correctB : Alg → Nat → Nat → Bool
  | .stop, m, x => decide (Determined m x)
  | .query i t0 t1, m, x =>
      decide (Determined m x) ||
        (if x.testBit i then correctB t1 (m ||| 2 ^ i.val) x else correctB t0 (m ||| 2 ^ i.val) x)

theorem correctB_sound (A : Alg) : ∀ m x, correctB A m x = true → Correct A m x := by
  induction A with
  | stop =>
    intro m x h
    simp only [correctB] at h
    show Determined m x
    exact of_decide_eq_true h
  | query i t0 t1 ih0 ih1 =>
    intro m x h
    simp only [correctB, Bool.or_eq_true] at h
    simp only [Correct]
    cases h with
    | inl h => exact Or.inl (of_decide_eq_true h)
    | inr h =>
      right
      by_cases hb : x.testBit i.val = true
      · rw [if_pos hb] at h ⊢; exact ih1 _ _ h
      · rw [if_neg hb] at h ⊢; exact ih0 _ _ h

theorem tree_correct : ∀ x < 32, Correct tree 0 x := by
  have h : ∀ x < 32, correctB tree 0 x = true := by decide +kernel
  exact fun x hx => correctB_sound tree 0 x (h x hx)

theorem tree_cost : totalCost tree = 104 := by decide +kernel

theorem f1_monotone : Monotone := by unfold Monotone; decide +kernel

theorem partition_ok : IsPartition partition ∧ Determines partition ∧
    totalCodim partition = 102 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold IsPartition; decide +kernel
  · unfold Determines; decide +kernel
  · decide +kernel

/-- The answer to Question 2.1: f1 is monotone, a(f1, π_{1/2}) = 104/32 = 13/4,
and sc(f1, π_{1/2}) ≤ 102/32 = 51/16 < 13/4. -/
theorem answer :
    Monotone ∧
    (∀ A : Alg, (∀ x < 32, Correct A 0 x) → 104 ≤ totalCost A) ∧
    (∃ A : Alg, (∀ x < 32, Correct A 0 x) ∧ totalCost A = 104) ∧
    (∃ P : List (Nat × Nat), IsPartition P ∧ Determines P ∧ totalCodim P = 102) :=
  ⟨f1_monotone, lower_bound, ⟨tree, tree_correct, tree_cost⟩, ⟨partition, partition_ok⟩⟩

/-- The gap: every correct algorithm's summed query count exceeds the
partition's summed codimension. -/
theorem gap : ∃ P : List (Nat × Nat), IsPartition P ∧ Determines P ∧
    ∀ A : Alg, (∀ x < 32, Correct A 0 x) → totalCodim P < totalCost A :=
  ⟨partition, partition_ok.1, partition_ok.2.1, fun A hA => by
    have := lower_bound A hA; have := partition_ok.2.2; omega⟩

end KS24
