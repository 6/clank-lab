import ProductCover
import ChartCoordinates

namespace ADKZPricing
open Matrix Finset
noncomputable section
variable {𝕜 : Type*} [Field 𝕜]

/-- Literal row concatenation, with one shared chart coordinate. The first
    n labels are the left rows and the next m labels are the right rows. -/
def orderedProduct {R : Type*} [Zero R] {n m d e : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) R)
    (B : Matrix (Fin m) (Fin (e + 1)) R) :
    Matrix (Fin (n + m)) (Fin (d + e + 1)) R :=
  Fin.append
    (fun i => Fin.cons (A i 0) (Fin.append (fun j => A i j.succ) (fun _ => 0)))
    (fun i => Fin.cons (B i 0) (Fin.append (fun _ => 0) (fun j => B i j.succ)))

def productLeft {d e : ℕ} (v : Fin (d + e + 1) → 𝕜) : Fin (d + 1) → 𝕜 :=
  Fin.cons (v 0) (fun j => v (Fin.castAdd e j).succ)

def productRight {d e : ℕ} (v : Fin (d + e + 1) → 𝕜) : Fin (e + 1) → 𝕜 :=
  Fin.cons (v 0) (fun j => v (Fin.natAdd d j).succ)

theorem orderedProduct_left_value {n m d e : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) 𝕜)
    (B : Matrix (Fin m) (Fin (e + 1)) 𝕜)
    (v : Fin (d + e + 1) → 𝕜) (i : Fin n) :
    orderedProduct A B (Fin.castAdd m i) ⬝ᵥ v = A i ⬝ᵥ productLeft v := by
  simp [orderedProduct, productLeft, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_add]

theorem orderedProduct_right_value {n m d e : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) 𝕜)
    (B : Matrix (Fin m) (Fin (e + 1)) 𝕜)
    (v : Fin (d + e + 1) → 𝕜) (i : Fin m) :
    orderedProduct A B (Fin.natAdd n i) ⬝ᵥ v = B i ⬝ᵥ productRight v := by
  simp [orderedProduct, productRight, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_add]

omit [Field 𝕜] in
theorem product_projections_injective {d e : ℕ} :
    Function.Injective (fun v : Fin (d + e + 1) → 𝕜 => (productLeft v, productRight v)) := by
  intro u v huv
  have hl := congrArg Prod.fst huv
  have hr := congrArg Prod.snd huv
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact congrFun hl 0
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · exact congrFun hl k.succ
    · exact congrFun hr k.succ

/-- Zero sets retain original indices, including rows on the shared facet. -/
theorem orderedProduct_zero_labels {n m d e : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) 𝕜)
    (B : Matrix (Fin m) (Fin (e + 1)) 𝕜) (v : Fin (d + e + 1) → 𝕜) :
    (∀ i, orderedProduct A B (Fin.castAdd m i) ⬝ᵥ v = 0 ↔ A i ⬝ᵥ productLeft v = 0) ∧
    (∀ i, orderedProduct A B (Fin.natAdd n i) ⬝ᵥ v = 0 ↔ B i ⬝ᵥ productRight v = 0) := by
  simp only [orderedProduct_left_value, orderedProduct_right_value, implies_true, and_self]

/-- None is the central cell; some i reverses only row i. Closed inequalities
    keep all shared facets. There are exactly n+1 such sign patterns. -/
def starSign {R : Type*} [Ring R] {n : ℕ} (cell : Option (Fin n)) (i : Fin n) : R :=
  if cell = some i then -1 else 1

def StarFeasible {R : Type*} [Ring R] [LinearOrder R] {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) R)
    (cell : Option (Fin n)) (v : Fin (d + 1) → R) : Prop :=
  ∀ i, 0 ≤ starSign cell i * (A i ⬝ᵥ v)

def leftStar {n m : ℕ} : Option (Fin (n + m)) → Option (Fin n)
  | none => none
  | some i => (finSumFinEquiv.symm i).getLeft?

def rightStar {n m : ℕ} : Option (Fin (n + m)) → Option (Fin m)
  | none => none
  | some i => (finSumFinEquiv.symm i).getRight?

theorem starSign_left {n m : ℕ} (c : Option (Fin (n + m))) (i : Fin n) :
    starSign c (Fin.castAdd m i) = (starSign (leftStar c) i : 𝕜) := by
  cases c with
  | none => simp [starSign, leftStar]
  | some j =>
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simp [starSign, leftStar, finSumFinEquiv]
    · have hn : Fin.natAdd n k ≠ Fin.castAdd m i := by
        intro h
        have he := congrArg Fin.val h
        change n + k.val = i.val at he
        omega
      simp [starSign, leftStar, finSumFinEquiv, hn]

theorem starSign_right {n m : ℕ} (c : Option (Fin (n + m))) (i : Fin m) :
    starSign c (Fin.natAdd n i) = (starSign (rightStar c) i : 𝕜) := by
  cases c with
  | none => simp [starSign, rightStar]
  | some j =>
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · have hn : Fin.castAdd m k ≠ Fin.natAdd n i := by
        intro h
        have he := congrArg Fin.val h
        change k.val = n + i.val at he
        omega
      simp [starSign, rightStar, finSumFinEquiv, hn]
    · simp [starSign, rightStar, finSumFinEquiv]

/-- Every one of the 81 product-star cells splits into its two actual factor
    cells. The exceptional row can occur in only one factor. -/
theorem orderedProduct_star_iff [LinearOrder 𝕜] {n m d e : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) 𝕜)
    (B : Matrix (Fin m) (Fin (e + 1)) 𝕜)
    (c : Option (Fin (n + m))) (v : Fin (d + e + 1) → 𝕜) :
    StarFeasible (orderedProduct A B) c v ↔
      StarFeasible A (leftStar c) (productLeft v) ∧
      StarFeasible B (rightStar c) (productRight v) := by
  constructor
  · intro h
    constructor
    · intro i
      simpa only [starSign_left, orderedProduct_left_value] using h (Fin.castAdd m i)
    · intro i
      simpa only [starSign_right, orderedProduct_right_value] using h (Fin.natAdd n i)
  · rintro ⟨hl, hr⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [starSign_left, orderedProduct_left_value] using hl j
    · simpa only [starSign_right, orderedProduct_right_value] using hr j

theorem star_split_one_exception {n m : ℕ} (c : Option (Fin (n + m))) :
    leftStar c = none ∨ rightStar c = none := by
  cases c with
  | none => exact Or.inl rfl
  | some i =>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [leftStar, rightStar, finSumFinEquiv]

theorem orderedProduct_star_strict_chart [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {n m d e : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) 𝕜)
    (B : Matrix (Fin m) (Fin (e + 1)) 𝕜)
    (hA : ∀ c v, StarFeasible A c v → v ≠ 0 → 0 < v 0)
    (hB : ∀ c v, StarFeasible B c v → v ≠ 0 → 0 < v 0)
    (c : Option (Fin (n + m))) (v : Fin (d + e + 1) → 𝕜)
    (hv : StarFeasible (orderedProduct A B) c v) (hne : v ≠ 0) :
    0 < v 0 ∧ productLeft v ≠ 0 ∧ productRight v ≠ 0 := by
  have hf := (orderedProduct_star_iff A B c v).mp hv
  have ht : 0 < v 0 := by
    by_cases hl : productLeft v = 0
    · have hr : productRight v ≠ 0 := by
        intro hr
        apply hne
        apply product_projections_injective
        change (productLeft v, productRight v) = (productLeft 0, productRight 0)
        rw [hl, hr]
        congr 1 <;> ext i <;> refine Fin.cases (by rfl) (fun _ => rfl) i
      exact hB _ _ hf.2 hr
    · exact hA _ _ hf.1 hl
  refine ⟨ht, ?_, ?_⟩ <;> intro hz
  · have h := congrFun hz 0
    exact ht.ne' h
  · have h := congrFun hz 0
    exact ht.ne' h

theorem product_star_cell_count : Fintype.card (Option (Fin (40 + 40))) = 81 := by decide

#print axioms orderedProduct_star_iff
#print axioms orderedProduct_star_strict_chart
#print axioms product_projections_injective
end
end ADKZPricing
