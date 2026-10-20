import Uniform5.CompositionGeometry
import Uniform5.CompositionModels

/-!
# Concrete lower-dimensional library models

The rank-four node order is that of paper Appendix Names. Roots need not have unit norm: the existing
`WythoffSeed` uses their actual norms and imposes signed mirror distance
one half. These are definitions of actual reflection-orbit hulls, not
claims of uniformity, finiteness, or classification completeness.
-/

noncomputable section
namespace Uniform5.Composition
open scoped RealInnerProductSpace

/-- A4 is represented in its canonical sum-zero hyperplane in R5. -/
noncomputable def rootsA4 (i : Fin 4) : ModelSpace 5 :=
  coordinateVector i.castSucc - coordinateVector i.succ

/-- B4 has the short root at node 3: the diagram is 3,3,4. -/
noncomputable def rootsB4 (i : Fin 4) : ModelSpace 4 :=
  if h : i.val < 3 then
    coordinateVector i - coordinateVector ⟨i.val + 1, by omega⟩
  else coordinateVector i

/-- D4 has central node 1, adjacent to nodes 0,2,3. -/
noncomputable def rootsD4 (i : Fin 4) : ModelSpace 4 :=
  if h : i.val < 3 then
    coordinateVector i - coordinateVector ⟨i.val + 1, by omega⟩
  else coordinateVector (2 : Fin 4) + coordinateVector (⟨3, by decide⟩ : Fin 4)

/-- F4 has diagram 3,4,3, with long roots at nodes 0 and 1. -/
noncomputable def rootsF4 : Fin 4 → ModelSpace 4 :=
  ![coordinateVector 1 - coordinateVector 2,
    coordinateVector 2 - coordinateVector (⟨3, by decide⟩ : Fin 4),
    coordinateVector (⟨3, by decide⟩ : Fin 4),
    (1 / 2 : ℝ) • (coordinateVector 0 - coordinateVector 1 -
      coordinateVector 2 - coordinateVector (⟨3, by decide⟩ : Fin 4))]

noncomputable def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

/-- Unit H4 roots with the order-five link between nodes 0 and 1. -/
noncomputable def rootsH4 : Fin 4 → ModelSpace 4 :=
  ![coordinateVector 0,
    (-goldenRatio / 2) • coordinateVector 0 + (1 / 2 : ℝ) • coordinateVector 1 +
      ((goldenRatio - 1) / 2) • coordinateVector 2,
    -coordinateVector 1,
    (1 / 2 : ℝ) • coordinateVector 1 + (-goldenRatio / 2) • coordinateVector 2 +
      ((goldenRatio - 1) / 2) • coordinateVector (⟨3, by decide⟩ : Fin 4)]

theorem goldenRatio_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  unfold goldenRatio
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

/-- The special H4 Gram entry is exactly the order-five mirror cosine. -/
theorem goldenRatio_half_eq_cos_pi_fifth : goldenRatio / 2 = Real.cos (Real.pi / 5) := by
  rw [Real.cos_pi_div_five, goldenRatio]
  ring

/-- Exact Gram matrix of the A4 simple roots. -/
theorem rootsA4_gram (i j : Fin 4) :
    ⟪rootsA4 i, rootsA4 j⟫ =
      !![(2 : ℝ), -1, 0, 0; -1, 2, -1, 0; 0, -1, 2, -1; 0, 0, -1, 2] i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [rootsA4, coordinateVector, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_succ, EuclideanSpace.single_apply, Fin.isValue, Fin.mk.injEq, Fin.succ]

/-- Exact Gram matrix of B4, including its short terminal root. -/
theorem rootsB4_gram (i j : Fin 4) :
    ⟪rootsB4 i, rootsB4 j⟫ =
      !![(2 : ℝ), -1, 0, 0; -1, 2, -1, 0; 0, -1, 2, -1; 0, 0, -1, 1] i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [rootsB4, coordinateVector, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_succ, EuclideanSpace.single_apply, Fin.isValue, Fin.mk.injEq, Fin.succ]

/-- Exact Gram matrix checks D4's branch at node 1. -/
theorem rootsD4_gram (i j : Fin 4) :
    ⟪rootsD4 i, rootsD4 j⟫ =
      !![(2 : ℝ), -1, 0, 0; -1, 2, -1, -1; 0, -1, 2, 0; 0, -1, 0, 2] i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [rootsD4, coordinateVector, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_succ, EuclideanSpace.single_apply, Fin.isValue, Fin.mk.injEq, Fin.succ] <;>
    simp only [Fin.ext_iff] <;> norm_num [Fin.instOfNat, Fin.ofNat']

/-- Exact Gram matrix checks F4's central order-four link. -/
theorem rootsF4_gram (i j : Fin 4) :
    ⟪rootsF4 i, rootsF4 j⟫ =
      !![(2 : ℝ), -1, 0, 0; -1, 2, -1, 0; 0, -1, 1, -1 / 2; 0, 0, -1 / 2, 1] i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [rootsF4, coordinateVector, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_succ, EuclideanSpace.single_apply, Fin.isValue, Fin.mk.injEq, Fin.succ] <;>
    simp only [Fin.ext_iff] <;> norm_num [Fin.instOfNat, Fin.ofNat']

/-- Exact Gram matrix of unit H4 roots, giving the diagram 5,3,3. -/
theorem rootsH4_gram (i j : Fin 4) :
    ⟪rootsH4 i, rootsH4 j⟫ =
      !![(1 : ℝ), -goldenRatio / 2, 0, 0;
        -goldenRatio / 2, 1, -1 / 2, 0;
        0, -1 / 2, 1, -1 / 2; 0, 0, -1 / 2, 1] i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [rootsH4, coordinateVector, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_succ, EuclideanSpace.single_apply, Fin.isValue, Fin.mk.injEq, Fin.succ] <;>
    simp only [Fin.ext_iff] <;> norm_num [Fin.instOfNat, Fin.ofNat'] <;>
    nlinarith [goldenRatio_sq]

theorem rootsA4_ne_zero (i : Fin 4) : rootsA4 i ≠ 0 := by
  intro hz
  have h := rootsA4_gram i i
  rw [hz, inner_zero_left] at h
  fin_cases i <;> norm_num at h

theorem rootsB4_ne_zero (i : Fin 4) : rootsB4 i ≠ 0 := by
  intro hz
  have h := rootsB4_gram i i
  rw [hz, inner_zero_left] at h
  fin_cases i <;> norm_num at h

theorem rootsD4_ne_zero (i : Fin 4) : rootsD4 i ≠ 0 := by
  intro hz
  have h := rootsD4_gram i i
  rw [hz, inner_zero_left] at h
  fin_cases i <;> norm_num at h

theorem rootsF4_ne_zero (i : Fin 4) : rootsF4 i ≠ 0 := by
  intro hz
  have h := rootsF4_gram i i
  rw [hz, inner_zero_left] at h
  fin_cases i <;> norm_num at h

theorem rootsH4_norm (i : Fin 4) : ‖rootsH4 i‖ = 1 := by
  have h := rootsH4_gram i i
  rw [real_inner_self_eq_norm_sq] at h
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
  fin_cases i <;> norm_num at h ⊢ <;> exact h

theorem rootsH4_ne_zero (i : Fin 4) : rootsH4 i ≠ 0 := by
  intro hz
  have h := rootsH4_norm i
  rw [hz, norm_zero] at h
  norm_num at h

noncomputable def IsA4Wythoff {E : Type*} [PseudoMetricSpace E] (P : Set E) : Prop :=
  ∃ (J : Finset (Fin 4)) (x : ModelSpace 5), J.Nonempty ∧
    (∑ i, x i) = 0 ∧ WythoffSeed rootsA4 J x ∧ Congruent P (WythoffHull rootsA4 x)

noncomputable def IsB4Wythoff {E : Type*} [PseudoMetricSpace E] (P : Set E) : Prop :=
  ∃ (J : Finset (Fin 4)) (x : ModelSpace 4), J.Nonempty ∧
    WythoffSeed rootsB4 J x ∧ Congruent P (WythoffHull rootsB4 x)

noncomputable def IsD4Wythoff {E : Type*} [PseudoMetricSpace E] (P : Set E) : Prop :=
  ∃ (J : Finset (Fin 4)) (x : ModelSpace 4), J.Nonempty ∧
    WythoffSeed rootsD4 J x ∧ Congruent P (WythoffHull rootsD4 x)

noncomputable def IsF4Wythoff {E : Type*} [PseudoMetricSpace E] (P : Set E) : Prop :=
  ∃ (J : Finset (Fin 4)) (x : ModelSpace 4), J.Nonempty ∧
    WythoffSeed rootsF4 J x ∧ Congruent P (WythoffHull rootsF4 x)

noncomputable def IsH4Wythoff {E : Type*} [PseudoMetricSpace E] (P : Set E) : Prop :=
  ∃ (J : Finset (Fin 4)) (x : ModelSpace 4), J.Nonempty ∧
    WythoffSeed rootsH4 J x ∧ Congruent P (WythoffHull rootsH4 x)

/-- Exactly the five explicit rank-four Wythoff reflection families. -/
noncomputable def IsWythoff4 {E : Type*} [PseudoMetricSpace E] (P : Set E) : Prop :=
  IsA4Wythoff P ∨ IsB4Wythoff P ∨ IsD4Wythoff P ∨ IsF4Wythoff P ∨ IsH4Wythoff P

/-- The cube seed checks the paper's B40001 node and unit normalization. -/
noncomputable def cubeCorner4 : ModelSpace 4 := fun _ => (1 / 2 : ℝ)

theorem cubeCorner4_seed : WythoffSeed rootsB4 {⟨3, by decide⟩} cubeCorner4 := by
  intro i
  fin_cases i <;>
    simp [rootsB4, coordinateVector, cubeCorner4, inner_sub_left,
      EuclideanSpace.inner_single_left]

theorem cubeCorner4_unit_move : dist cubeCorner4 (mirrorReflection (rootsB4 3) cubeCorner4) = 1 :=
  ringed_seed_distance rootsB4 {⟨3, by decide⟩} cubeCorner4 cubeCorner4_seed 3 (by simp) (rootsB4_ne_zero 3)

theorem cube_model_is_Wythoff4 : IsWythoff4 (WythoffHull rootsB4 cubeCorner4) :=
  Or.inr (Or.inl ⟨{⟨3, by decide⟩}, cubeCorner4, by simp, cubeCorner4_seed, congruent_refl _⟩)

/-- A nonzero explicit H40001 seed; its equations use the golden ratio. -/
noncomputable def h4TerminalSeed : ModelSpace 4 := goldenRatio • coordinateVector (⟨3, by decide⟩ : Fin 4)

theorem h4TerminalSeed_seed : WythoffSeed rootsH4 {⟨3, by decide⟩} h4TerminalSeed := by
  intro i
  rw [rootsH4_norm]
  fin_cases i <;>
    norm_num [rootsH4, h4TerminalSeed, coordinateVector, inner_add_left,
      inner_smul_left, inner_smul_right, inner_neg_left,
      EuclideanSpace.inner_single_left, EuclideanSpace.single_apply] <;>
    simp only [Fin.ext_iff] <;> norm_num [Fin.instOfNat, Fin.ofNat'] <;> nlinarith [goldenRatio_sq]

theorem h4TerminalSeed_unit_move :
    dist h4TerminalSeed (mirrorReflection (rootsH4 3) h4TerminalSeed) = 1 :=
  ringed_seed_distance rootsH4 {⟨3, by decide⟩} h4TerminalSeed h4TerminalSeed_seed 3
    (by simp) (rootsH4_ne_zero 3)

theorem h4_model_is_Wythoff4 : IsWythoff4 (WythoffHull rootsH4 h4TerminalSeed) :=
  Or.inr (Or.inr (Or.inr (Or.inr
    ⟨{⟨3, by decide⟩}, h4TerminalSeed, by simp, h4TerminalSeed_seed, congruent_refl _⟩)))

/-- The layer separation of the explicit antiprism coordinates.
The horizontal component of a cross-layer edge has length
`2 * unitPolygonRadius n * sin (pi / (2*n))`. -/
noncomputable def antiprismHeight (n : ℕ) : ℝ :=
  Real.sqrt (1 - (2 * unitPolygonRadius n * Real.sin (Real.pi / (2 * n))) ^ 2)

theorem antiprismHeight_pos {n : ℕ} (hn : 3 ≤ n) : 0 < antiprismHeight n := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  let t : ℝ := Real.pi / (2 * n)
  have ht : 0 < t := div_pos Real.pi_pos (by positivity)
  have ht3 : t < Real.pi / 3 := by
    dsimp [t]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
    nlinarith [Real.pi_pos]
  have hc : 1 / 2 < Real.cos t := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi ht.le
      (show Real.pi / 3 ≤ Real.pi by linarith [Real.pi_pos]) ht3
    simpa only [Real.cos_pi_div_three] using h
  have hs : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_pos])
  have he : Real.pi / n = 2 * t := by dsimp [t]; ring
  have hprod : (2 * unitPolygonRadius n * Real.sin t) * (2 * Real.cos t) = 1 := by
    unfold unitPolygonRadius
    rw [he, Real.sin_two_mul]
    field_simp
    nlinarith
  have hp : 0 ≤ 2 * unitPolygonRadius n * Real.sin t := by
    unfold unitPolygonRadius
    rw [he, Real.sin_two_mul]
    positivity
  have hlt : 2 * unitPolygonRadius n * Real.sin t < 1 := by nlinarith
  apply Real.sqrt_pos.2
  change 0 < 1 - (2 * unitPolygonRadius n * Real.sin t) ^ 2
  nlinarith

/-- Actual three-dimensional coordinates: two regular polygons, offset
by half a polygon step and separated by `antiprismHeight n`. -/
noncomputable def antiprismPoint (n : ℕ) (b : Bool) (i : Fin n) : Space 3 :=
  let θ := 2 * Real.pi * (i : ℕ) / n + if b then Real.pi / n else 0
  !₂[unitPolygonRadius n * Real.cos θ,
     unitPolygonRadius n * Real.sin θ,
     if b then -(antiprismHeight n / 2) else antiprismHeight n / 2]

/-- A coordinate hull, without asserting its face lattice or uniformity. -/
noncomputable def antiprismModel (n : ℕ) : Set (Space 3) :=
  convexHull ℝ (Set.range (fun p : Bool × Fin n => antiprismPoint n p.1 p.2))

theorem antiprismModel_finitePolytope {n : ℕ} (hn : 0 < n) :
    FinitePolytope (antiprismModel n) := by
  classical
  let S := Set.range (fun p : Bool × Fin n => antiprismPoint n p.1 p.2)
  have hS : S.Finite := Set.finite_range _
  have hne : S.Nonempty := ⟨_, ⟨(false, ⟨0, hn⟩), rfl⟩⟩
  exact ⟨hS.toFinset, hS.toFinset_nonempty.mpr hne, by
    simp only [Set.Finite.coe_toFinset]; rfl⟩

/-- Orthogonal product with an actual unit interval. -/
noncomputable def polyhedralPrismModel (Q : Set (Space 3)) :
    Set (EuclideanSpace ℝ (Fin 3 ⊕ Fin 1)) := product Q unitInterval

noncomputable def antiprismPrismModel (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin 3 ⊕ Fin 1)) :=
  polyhedralPrismModel (antiprismModel n)

noncomputable def duoprismModel (p q : ℕ) :
    Set (EuclideanSpace ℝ (Fin 2 ⊕ Fin 2)) := product (unitPolygon p) (unitPolygon q)

noncomputable def IsAntiprismPrism {E : Type*} [PseudoMetricSpace E] (P : Set E) : Prop :=
  ∃ n : ℕ, 3 ≤ n ∧ Congruent P (antiprismPrismModel n)

noncomputable def IsDuoprism {E : Type*} [PseudoMetricSpace E] (P : Set E) : Prop :=
  ∃ p q : ℕ, 3 ≤ p ∧ p ≤ q ∧ Congruent P (duoprismModel p q)

end Uniform5.Composition
