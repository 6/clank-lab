import Uniform5.CompositionCubeOrbits

/-! Unit Cartesian cubes, their actual Euclidean products, and B3/B4 hulls. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical

noncomputable def unitCubeCorners (n : ℕ) : Set (Space n) :=
  {x | ∀ i, x i = 0 ∨ x i = 1}

noncomputable def unitCube (n : ℕ) : Set (Space n) := convexHull ℝ (unitCubeCorners n)

noncomputable def cubeCenter (n : ℕ) : Space n ≃ᵃⁱ[ℝ] Space n :=
  AffineIsometryEquiv.constVAdd ℝ (Space n) (fun _ => -(1 / 2 : ℝ))

theorem cubeCenter_apply (n : ℕ) (x : Space n) (i : Fin n) :
    cubeCenter n x i = x i - 1 / 2 := by
  change -(1 / 2 : ℝ) + x i = x i - 1 / 2
  ring

theorem cubeCenter_corners (n : ℕ) : cubeCenter n '' unitCubeCorners n = halfCubeCorners n := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    rw [cubeCenter_apply]
    rcases hx i with h | h <;> rw [h] <;> norm_num
  · intro hy
    let x : Space n := fun i => y i + 1 / 2
    refine ⟨x, ?_, ?_⟩
    · intro i
      rcases hy i with h | h <;> norm_num [x, h]
    · ext i
      rw [cubeCenter_apply]
      dsimp [x]
      ring

theorem congruent_unitCube_halfCube (n : ℕ) :
    Congruent (unitCube n) (convexHull ℝ (halfCubeCorners n)) := by
  have he : cubeCenter n '' unitCube n = convexHull ℝ (halfCubeCorners n) := by
    change (cubeCenter n).toAffineEquiv.toAffineMap '' convexHull ℝ _ = _
    rw [(cubeCenter n).toAffineEquiv.toAffineMap.image_convexHull]
    change convexHull ℝ (cubeCenter n '' unitCubeCorners n) = _
    rw [cubeCenter_corners]
  rw [← he]
  exact congruent_affineIsometry_image (cubeCenter n).toAffineIsometry _

theorem congruent_unitCube3_b3 : Congruent (unitCube 3) (WythoffHull rootsB3 cubeCorner3) := by
  rw [WythoffHull, cubeCorner3_orbit]
  exact congruent_unitCube_halfCube 3

theorem congruent_unitCube4_b4 : Congruent (unitCube 4) (WythoffHull rootsB4 cubeCorner4) := by
  rw [WythoffHull, cubeCorner4_orbit]
  exact congruent_unitCube_halfCube 4

theorem unitCube_one : unitCube 1 = unitInterval := by
  have hv : unitCubeCorners 1 = ({0, !₂[1]} : Set (Space 1)) := by
    ext x
    constructor
    · intro hx
      rcases hx 0 with h | h
      · left; ext i; fin_cases i; exact h
      · right; apply mem_singleton_iff.mpr; ext i; fin_cases i; exact h
    · rintro (rfl | hx)
      · intro i; exact Or.inl rfl
      · have := mem_singleton_iff.mp hx; subst x
        intro i; fin_cases i; exact Or.inr rfl
  rw [unitCube, hv, convexHull_pair]
  rfl

theorem flattenProduct_apply_sum {a b : ℕ}
    (x : EuclideanSpace ℝ (Fin a ⊕ Fin b)) (i : Fin a ⊕ Fin b) :
    flattenProduct a b x (finSumFinEquiv i) = x i := by
  change x (finSumFinEquiv.symm (finSumFinEquiv i)) = x i
  rw [Equiv.symm_apply_apply]

theorem flattenProduct_cube_corners (a b : ℕ) :
    flattenProduct a b '' product (unitCubeCorners a) (unitCubeCorners b) = unitCubeCorners (a + b) := by
  ext z
  constructor
  · rintro ⟨w, ⟨x, hx, y, hy, rfl⟩, rfl⟩ j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective j
    rw [flattenProduct_apply_sum]
    cases i with
    | inl i => exact hx i
    | inr i => exact hy i
  · intro hz
    let x : Space a := fun i => z (finSumFinEquiv (Sum.inl i))
    let y : Space b := fun i => z (finSumFinEquiv (Sum.inr i))
    refine ⟨productPoint x y, ⟨x, fun i => hz _, y, fun i => hz _, rfl⟩, ?_⟩
    ext j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective j
    rw [flattenProduct_apply_sum]
    cases i <;> rfl

theorem flattenProduct_unitCube (a b : ℕ) :
    flattenProduct a b '' product (unitCube a) (unitCube b) = unitCube (a + b) := by
  rw [unitCube, unitCube, product_convexHull]
  change (flattenProduct a b).toAffineEquiv.toAffineMap '' convexHull ℝ _ = _
  rw [(flattenProduct a b).toAffineEquiv.toAffineMap.image_convexHull]
  change convexHull ℝ (flattenProduct a b '' product (unitCubeCorners a) (unitCubeCorners b)) = _
  rw [flattenProduct_cube_corners]
  rfl

theorem congruent_product_unitCube (a b : ℕ) :
    Congruent (product (unitCube a) (unitCube b)) (unitCube (a + b)) := by
  rw [← flattenProduct_unitCube]
  exact congruent_affineIsometry_image (flattenProduct a b).toAffineIsometry _

theorem congruent_unitCube_two_square : Congruent (unitCube 2) (unitPolygon 4) := by
  have hp := congruent_product_unitCube 1 1
  rw [unitCube_one] at hp
  exact congruent_trans (congruent_symm hp) congruent_interval_product_square

theorem congruent_cubePrism_b4 :
    Congruent (polyhedralPrismModel (WythoffHull rootsB3 cubeCorner3))
      (WythoffHull rootsB4 cubeCorner4) := by
  have hI : Congruent unitInterval (unitCube 1) := by rw [unitCube_one]; exact congruent_refl _
  exact congruent_trans (congruent_product (congruent_symm congruent_unitCube3_b3) hI)
    (congruent_trans (congruent_product_unitCube 3 1) congruent_unitCube4_b4)

theorem congruent_squareDuoprism_b4 :
    Congruent (duoprismModel 4 4) (WythoffHull rootsB4 cubeCorner4) :=
  congruent_trans (congruent_product (congruent_symm congruent_unitCube_two_square)
    (congruent_symm congruent_unitCube_two_square))
    (congruent_trans (congruent_product_unitCube 2 2) congruent_unitCube4_b4)

end Uniform5.Composition
