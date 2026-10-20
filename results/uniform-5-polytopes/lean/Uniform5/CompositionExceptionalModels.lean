import Uniform5.CompositionLowerModels
import Uniform5.CaseBProducts
import Mathlib.Data.Real.GoldenRatio

/-!
# Exact coordinates for the exceptional four-dimensional models

The coordinates use the exact 600-cell construction: eight axis
points, sixteen half-sign points, and ninety-six even permutations of
`(φ/2, 1/2, (φ-1)/2, 0)`, scaled by φ. Integer pairs encode `(a+b*φ)/2`
so finite cardinality checks use exact kernel computation, not floating
point or an external evaluator. The two removed grand-antiprism decagon
planes are pinned by exact linear equations.

These are concrete hulls and geometric sanity checks, not assertions of
uniformity or a lower-dimensional classification.
-/

noncomputable section
namespace Uniform5.Composition
open scoped RealInnerProductSpace

/-- Exact coefficient pair for `(a+b*φ)/2`. -/
abbrev GoldenPair := ℤ × ℤ
abbrev GoldenPoint4 := Fin 4 → GoldenPair

noncomputable def goldenPairValue (x : GoldenPair) : ℝ :=
  ((x.1 : ℝ) + (x.2 : ℝ) * goldenRatio) / 2

noncomputable def goldenPairMulPhi (x : GoldenPair) : GoldenPair :=
  (x.2, x.1 + x.2)

noncomputable def goldenPairNeg (x : GoldenPair) : GoldenPair := (-x.1, -x.2)

noncomputable def goldenPointValue (x : GoldenPoint4) : Space 4 :=
  fun i => goldenRatio * goldenPairValue (x i)

/-- The twelve even permutations, acting by coordinate pullback. -/
noncomputable def evenPermutation4 : Fin 12 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![0, 2, 3, 1], ![0, 3, 1, 2],
    ![1, 0, 3, 2], ![1, 2, 0, 3], ![1, 3, 2, 0],
    ![2, 0, 1, 3], ![2, 1, 3, 0], ![2, 3, 0, 1],
    ![3, 0, 2, 1], ![3, 1, 0, 2], ![3, 2, 1, 0]]

noncomputable def coordinateSign (b : Bool) : ℤ := if b then -1 else 1

noncomputable def rawAxisPoint (j : Fin 4) (b : Bool) : GoldenPoint4 :=
  fun i => if i = j then (2 * coordinateSign b, 0) else (0, 0)

noncomputable def rawHalfPoint (s : Fin 4 → Bool) : GoldenPoint4 :=
  fun i => (coordinateSign (s i), 0)

noncomputable def rawSkewBase (s : Fin 3 → Bool) : GoldenPoint4 :=
  ![(0, coordinateSign (s 0)), (coordinateSign (s 1), 0),
    (-coordinateSign (s 2), coordinateSign (s 2)), (0, 0)]

noncomputable def rawSkewPoint (j : Fin 12) (s : Fin 3 → Bool) : GoldenPoint4 :=
  fun i => rawSkewBase s (evenPermutation4 j i)

noncomputable def rawAxisPoints : Finset GoldenPoint4 :=
  Finset.univ.image (fun p : Fin 4 × Bool => rawAxisPoint p.1 p.2)

noncomputable def rawHalfPoints : Finset GoldenPoint4 :=
  Finset.univ.image rawHalfPoint

noncomputable def rawSnub24Points : Finset GoldenPoint4 :=
  Finset.univ.image (fun p : Fin 12 × (Fin 3 → Bool) => rawSkewPoint p.1 p.2)

noncomputable def raw600CellPoints : Finset GoldenPoint4 :=
  rawAxisPoints ∪ rawHalfPoints ∪ rawSnub24Points

noncomputable def rawDecagonPlaneOne (x : GoldenPoint4) : Prop :=
  x 3 = (0, 0) ∧ goldenPairMulPhi (x 2) = x 1

noncomputable def rawDecagonPlaneTwo (x : GoldenPoint4) : Prop :=
  x 0 = (0, 0) ∧ x 2 = goldenPairNeg (goldenPairMulPhi (x 1))

instance : DecidablePred rawDecagonPlaneOne := fun x =>
  inferInstanceAs (Decidable (x 3 = (0, 0) ∧ goldenPairMulPhi (x 2) = x 1))

instance : DecidablePred rawDecagonPlaneTwo := fun x =>
  inferInstanceAs (Decidable (x 0 = (0, 0) ∧ x 2 = goldenPairNeg (goldenPairMulPhi (x 1))))

noncomputable def rawDecagonOne : Finset GoldenPoint4 :=
  raw600CellPoints.filter rawDecagonPlaneOne

noncomputable def rawDecagonTwo : Finset GoldenPoint4 :=
  raw600CellPoints.filter rawDecagonPlaneTwo

noncomputable def rawGrandAntiprismPoints : Finset GoldenPoint4 :=
  raw600CellPoints \ (rawDecagonOne ∪ rawDecagonTwo)

theorem evenPermutation4_bijective (j : Fin 12) :
    Function.Bijective (evenPermutation4 j) := by
  fin_cases j <;> decide

/-- The inversion count is even for every listed permutation. -/
theorem evenPermutation4_even (j : Fin 12) :
    (∑ i : Fin 4, ∑ k : Fin 4,
      if i < k ∧ evenPermutation4 j k < evenPermutation4 j i then 1 else 0) % 2 = 0 := by
  fin_cases j <;> decide

/-- Coefficients of the sum of squared, unhalved coordinates. -/
noncomputable def goldenSquaredSum (x : GoldenPoint4) : GoldenPair :=
  ((∑ i, ((x i).1 ^ 2 + (x i).2 ^ 2)),
   (∑ i, (2 * (x i).1 * (x i).2 + (x i).2 ^ 2)))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- All finite counts are checked by kernel reduction of exact integers. -/
theorem exceptional_raw_counts :
    raw600CellPoints.card = 120 ∧ rawSnub24Points.card = 96 ∧
    rawDecagonOne.card = 10 ∧ rawDecagonTwo.card = 10 ∧
    (rawDecagonOne ∪ rawDecagonTwo).card = 20 ∧
    rawGrandAntiprismPoints.card = 100 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem raw600CellPoints_sphere :
    ∀ x ∈ raw600CellPoints, goldenSquaredSum x = (4, 0) := by
  decide +kernel

theorem goldenPairValue_injective : Function.Injective goldenPairValue := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have hi : Irrational goldenRatio := gold_irrational
  have he : (a : ℝ) + (b : ℝ) * goldenRatio = (c : ℝ) + (d : ℝ) * goldenRatio := by
    dsimp [goldenPairValue] at h
    linarith
  have hbd : b = d := by
    by_cases hne : b = d
    · exact hne
    exfalso
    have hirr := (hi.intCast_mul (sub_ne_zero.mpr hne)).intCast_add (a - c)
    apply hirr.ne_zero
    push_cast
    linarith
  have hac : a = c := by
    rw [hbd] at he
    exact_mod_cast (show (a : ℝ) = c by linarith)
  exact Prod.ext hac hbd

theorem goldenPointValue_injective : Function.Injective goldenPointValue := by
  intro x y h
  have hp : goldenRatio ≠ 0 := (show Irrational goldenRatio from gold_irrational).ne_zero
  funext i
  apply goldenPairValue_injective
  have hi := congrArg (fun z : Space 4 => z i) h
  exact mul_left_cancel₀ hp hi

theorem goldenPairValue_mulPhi (x : GoldenPair) :
    goldenPairValue (goldenPairMulPhi x) = goldenRatio * goldenPairValue x := by
  dsimp [goldenPairValue, goldenPairMulPhi]
  push_cast
  ring_nf
  rw [goldenRatio_sq]
  ring

theorem goldenPairValue_neg (x : GoldenPair) :
    goldenPairValue (goldenPairNeg x) = -goldenPairValue x := by
  simp [goldenPairValue, goldenPairNeg]
  ring

theorem goldenPairValue_sq (x : GoldenPair) :
    goldenPairValue x ^ 2 =
      (((x.1 ^ 2 + x.2 ^ 2 : ℤ) : ℝ) +
        ((2 * x.1 * x.2 + x.2 ^ 2 : ℤ) : ℝ) * goldenRatio) / 4 := by
  dsimp [goldenPairValue]
  push_cast
  ring_nf
  rw [goldenRatio_sq]
  ring

theorem sum_goldenPairValue_sq (x : GoldenPoint4) :
    (∑ i, goldenPairValue (x i) ^ 2) =
      (((goldenSquaredSum x).1 : ℝ) + ((goldenSquaredSum x).2 : ℝ) * goldenRatio) / 4 := by
  simp only [goldenSquaredSum, goldenPairValue_sq, Int.cast_sum, Int.cast_add,
    Finset.sum_add_distrib, add_mul, add_div, Finset.sum_div, Finset.sum_mul]

theorem goldenPointValue_norm {x : GoldenPoint4} (hx : goldenSquaredSum x = (4, 0)) :
    ‖goldenPointValue x‖ = goldenRatio := by
  have hp : 0 ≤ goldenRatio := by dsimp [goldenRatio]; positivity
  apply (sq_eq_sq₀ (norm_nonneg _) hp).mp
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp only [goldenPointValue, Real.norm_eq_abs, sq_abs, mul_pow, ← Finset.mul_sum,
    sum_goldenPairValue_sq, hx]
  norm_num

/-- The exact first decagon plane, in the source generator's coordinates. -/
noncomputable def decagonPlaneOne : Set (Space 4) :=
  {x | x 3 = 0 ∧ goldenRatio * x 2 = x 1}

/-- Its orthogonal complementary plane. -/
noncomputable def decagonPlaneTwo : Set (Space 4) :=
  {x | x 0 = 0 ∧ x 2 = -(goldenRatio * x 1)}

theorem goldenPointValue_coordinate_zero_iff (x : GoldenPoint4) (i : Fin 4) :
    goldenPointValue x i = 0 ↔ x i = (0, 0) := by
  have hp : goldenRatio ≠ 0 := (show Irrational goldenRatio from gold_irrational).ne_zero
  change goldenRatio * goldenPairValue (x i) = 0 ↔ _
  rw [mul_eq_zero]
  simp only [hp, false_or]
  have hz : goldenPairValue (0, 0) = 0 := by norm_num [goldenPairValue]
  rw [← hz, goldenPairValue_injective.eq_iff]

theorem rawDecagonPlaneOne_iff (x : GoldenPoint4) :
    rawDecagonPlaneOne x ↔ goldenPointValue x ∈ decagonPlaneOne := by
  have hp : goldenRatio ≠ 0 := (show Irrational goldenRatio from gold_irrational).ne_zero
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [goldenPointValue_coordinate_zero_iff]
  apply and_congr_right
  intro _
  constructor
  · intro h
    have he := congrArg goldenPairValue h
    rw [goldenPairValue_mulPhi] at he
    change goldenRatio * (goldenRatio * goldenPairValue (x 2)) =
      goldenRatio * goldenPairValue (x 1)
    exact congrArg (goldenRatio * ·) he
  · intro h
    change goldenRatio * (goldenRatio * goldenPairValue (x 2)) =
      goldenRatio * goldenPairValue (x 1) at h
    rw [← goldenPairValue_mulPhi] at h
    exact goldenPairValue_injective (mul_left_cancel₀ hp h)

theorem rawDecagonPlaneTwo_iff (x : GoldenPoint4) :
    rawDecagonPlaneTwo x ↔ goldenPointValue x ∈ decagonPlaneTwo := by
  have hp : goldenRatio ≠ 0 := (show Irrational goldenRatio from gold_irrational).ne_zero
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [goldenPointValue_coordinate_zero_iff]
  apply and_congr_right
  intro _
  constructor
  · intro h
    have he := congrArg goldenPairValue h
    rw [goldenPairValue_neg, goldenPairValue_mulPhi] at he
    change goldenRatio * goldenPairValue (x 2) =
      -(goldenRatio * (goldenRatio * goldenPairValue (x 1)))
    rw [he]
    ring
  · intro h
    apply goldenPairValue_injective
    apply mul_left_cancel₀ hp
    rw [goldenPairValue_neg, goldenPairValue_mulPhi]
    change goldenRatio * goldenPairValue (x 2) =
      -(goldenRatio * (goldenRatio * goldenPairValue (x 1))) at h
    rw [h]
    ring

theorem decagon_planes_orthogonal {x y : Space 4}
    (hx : x ∈ decagonPlaneOne) (hy : y ∈ decagonPlaneTwo) : ⟪x, y⟫ = 0 := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
  simp only [star_trivial]
  change y 0 * x 0 + (y 1 * x 1 + (y 2 * x 2 + (y 3 * x 3 + 0))) = 0
  rw [hx0, hy0, hy1, ← hx1]
  ring

noncomputable def cell600Points : Finset (Space 4) := raw600CellPoints.image goldenPointValue
noncomputable def snub24Points : Finset (Space 4) := rawSnub24Points.image goldenPointValue
noncomputable def grandAntiprismPoints : Finset (Space 4) :=
  rawGrandAntiprismPoints.image goldenPointValue
noncomputable def decagonOnePoints : Finset (Space 4) := rawDecagonOne.image goldenPointValue
noncomputable def decagonTwoPoints : Finset (Space 4) := rawDecagonTwo.image goldenPointValue

theorem cell600Points_card : cell600Points.card = 120 := by
  rw [cell600Points, Finset.card_image_of_injective _ goldenPointValue_injective]
  exact exceptional_raw_counts.1

theorem snub24Points_card : snub24Points.card = 96 := by
  rw [snub24Points, Finset.card_image_of_injective _ goldenPointValue_injective]
  exact exceptional_raw_counts.2.1

theorem grandAntiprismPoints_card : grandAntiprismPoints.card = 100 := by
  rw [grandAntiprismPoints, Finset.card_image_of_injective _ goldenPointValue_injective]
  exact exceptional_raw_counts.2.2.2.2.2

theorem decagonOnePoints_card : decagonOnePoints.card = 10 := by
  rw [decagonOnePoints, Finset.card_image_of_injective _ goldenPointValue_injective]
  exact exceptional_raw_counts.2.2.1

theorem decagonTwoPoints_card : decagonTwoPoints.card = 10 := by
  rw [decagonTwoPoints, Finset.card_image_of_injective _ goldenPointValue_injective]
  exact exceptional_raw_counts.2.2.2.1

theorem cell600Points_norm {x : Space 4} (hx : x ∈ cell600Points) : ‖x‖ = goldenRatio := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  exact goldenPointValue_norm (raw600CellPoints_sphere p hp)

theorem snub24Points_subset : snub24Points ⊆ cell600Points := by
  apply Finset.image_subset_image
  exact Finset.subset_union_right

theorem grandAntiprismPoints_subset : grandAntiprismPoints ⊆ cell600Points := by
  apply Finset.image_subset_image
  exact Finset.sdiff_subset

/-- The real grand-antiprism point set removes exactly the two pinned planes. -/
theorem mem_grandAntiprismPoints_iff (x : Space 4) :
    x ∈ grandAntiprismPoints ↔
      x ∈ cell600Points ∧ x ∉ decagonPlaneOne ∧ x ∉ decagonPlaneTwo := by
  constructor
  · intro hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hp, hnot⟩ := Finset.mem_sdiff.mp hp
    refine ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_, ?_⟩
    · intro h
      apply hnot
      exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hp, (rawDecagonPlaneOne_iff p).mpr h⟩)
    · intro h
      apply hnot
      exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hp, (rawDecagonPlaneTwo_iff p).mpr h⟩)
  · rintro ⟨hx, h1, h2⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_image.mpr
    refine ⟨p, Finset.mem_sdiff.mpr ⟨hp, ?_⟩, rfl⟩
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact h1 ((rawDecagonPlaneOne_iff p).mp (Finset.mem_filter.mp h).2)
    · exact h2 ((rawDecagonPlaneTwo_iff p).mp (Finset.mem_filter.mp h).2)

noncomputable def cell600Model : Set (Space 4) := convexHull ℝ (cell600Points : Set (Space 4))
noncomputable def snub24Model : Set (Space 4) := convexHull ℝ (snub24Points : Set (Space 4))
noncomputable def grandAntiprismModel : Set (Space 4) :=
  convexHull ℝ (grandAntiprismPoints : Set (Space 4))

private theorem exceptional_finitePolytope {V : Finset (Space 4)} (hn : 0 < V.card) :
    FinitePolytope (convexHull ℝ (V : Set (Space 4))) :=
  ⟨V, Finset.card_pos.mp hn, rfl⟩

theorem cell600Model_finitePolytope : FinitePolytope cell600Model :=
  exceptional_finitePolytope (by rw [cell600Points_card]; omega)

theorem snub24Model_finitePolytope : FinitePolytope snub24Model :=
  exceptional_finitePolytope (by rw [snub24Points_card]; omega)

theorem grandAntiprismModel_finitePolytope : FinitePolytope grandAntiprismModel :=
  exceptional_finitePolytope (by rw [grandAntiprismPoints_card]; omega)

private theorem exceptional_extremePoints {V : Finset (Space 4)}
    (hV : V ⊆ cell600Points) :
    (convexHull ℝ (V : Set (Space 4))).extremePoints ℝ = (V : Set (Space 4)) := by
  apply Set.Subset.antisymm (extremePoints_convexHull_subset (𝕜 := ℝ))
  apply CaseB.cospherical_extremePoints (c := 0) (R := goldenRatio)
  intro x hx
  rw [Metric.mem_sphere, dist_zero_right]
  exact cell600Points_norm (hV hx)

theorem cell600Model_extremePoints : cell600Model.extremePoints ℝ = (cell600Points : Set (Space 4)) :=
  exceptional_extremePoints (Finset.Subset.refl _)

theorem snub24Model_extremePoints : snub24Model.extremePoints ℝ = (snub24Points : Set (Space 4)) :=
  exceptional_extremePoints snub24Points_subset

theorem grandAntiprismModel_extremePoints :
    grandAntiprismModel.extremePoints ℝ = (grandAntiprismPoints : Set (Space 4)) :=
  exceptional_extremePoints grandAntiprismPoints_subset

theorem cell600Model_extremePoints_ncard : (cell600Model.extremePoints ℝ).ncard = 120 := by
  rw [cell600Model_extremePoints, Set.ncard_coe_Finset, cell600Points_card]

theorem snub24Model_extremePoints_ncard : (snub24Model.extremePoints ℝ).ncard = 96 := by
  rw [snub24Model_extremePoints, Set.ncard_coe_Finset, snub24Points_card]

theorem grandAntiprismModel_extremePoints_ncard :
    (grandAntiprismModel.extremePoints ℝ).ncard = 100 := by
  rw [grandAntiprismModel_extremePoints, Set.ncard_coe_Finset, grandAntiprismPoints_card]

noncomputable def IsSnub24 {E : Type*} [PseudoMetricSpace E] (P : Set E) : Prop :=
  Congruent P snub24Model
noncomputable def IsGrandAntiprism {E : Type*} [PseudoMetricSpace E] (P : Set E) : Prop :=
  Congruent P grandAntiprismModel

end Uniform5.Composition
