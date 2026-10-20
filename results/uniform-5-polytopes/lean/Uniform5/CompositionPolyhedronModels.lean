import Uniform5.CompositionLowerModels

/-!
# Concrete three-dimensional classification models

Rank-three node order follows the coordinate library. The snub root
boxes and rotation words encode the exact algebraic model certificates.
Their equations are the physical-coordinate form of the coefficient
quadratic forms described in the manuscript.
Snub families quantify over the precisely constrained algebraic seed;
no existence, uniqueness, uniformity, or completeness theorem is assumed
or asserted by these definitions.
-/

noncomputable section
namespace Uniform5.Composition
open scoped RealInnerProductSpace

noncomputable def rootsA3 (i : Fin 3) : ModelSpace 4 :=
  coordinateVector i.castSucc - coordinateVector i.succ

noncomputable def rootsB3 (i : Fin 3) : ModelSpace 3 :=
  if h : i.val < 2 then
    coordinateVector i - coordinateVector ⟨i.val + 1, by omega⟩
  else coordinateVector i

noncomputable def rootsH3 : Fin 3 → ModelSpace 3 :=
  ![coordinateVector 0,
    (-goldenRatio / 2) • coordinateVector 0 + (1 / 2 : ℝ) • coordinateVector 1 +
      ((goldenRatio - 1) / 2) • coordinateVector (⟨2, by decide⟩ : Fin 3),
    -coordinateVector 1]

theorem rootsA3_gram (i j : Fin 3) :
    ⟪rootsA3 i, rootsA3 j⟫ = !![(2 : ℝ), -1, 0; -1, 2, -1; 0, -1, 2] i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [rootsA3, coordinateVector, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_succ, EuclideanSpace.single_apply, Fin.isValue,
      Fin.mk.injEq, Fin.succ]

theorem rootsB3_gram (i j : Fin 3) :
    ⟪rootsB3 i, rootsB3 j⟫ = !![(2 : ℝ), -1, 0; -1, 2, -1; 0, -1, 1] i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [rootsB3, coordinateVector, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_succ, EuclideanSpace.single_apply, Fin.isValue,
      Fin.mk.injEq, Fin.succ]

theorem rootsH3_gram (i j : Fin 3) :
    ⟪rootsH3 i, rootsH3 j⟫ =
      !![(1 : ℝ), -goldenRatio / 2, 0; -goldenRatio / 2, 1, -1 / 2; 0, -1 / 2, 1] i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [rootsH3, coordinateVector, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_succ, EuclideanSpace.single_apply, Fin.isValue,
      Fin.mk.injEq, Fin.succ]
  all_goals nlinarith [goldenRatio_sq]

theorem rootsA3_ne_zero (i : Fin 3) : rootsA3 i ≠ 0 := by
  intro hz
  have h := rootsA3_gram i i
  rw [hz, inner_zero_left] at h
  fin_cases i <;> norm_num at h

theorem rootsB3_ne_zero (i : Fin 3) : rootsB3 i ≠ 0 := by
  intro hz
  have h := rootsB3_gram i i
  rw [hz, inner_zero_left] at h
  fin_cases i <;> norm_num at h

theorem rootsH3_norm (i : Fin 3) : ‖rootsH3 i‖ = 1 := by
  have h := rootsH3_gram i i
  rw [real_inner_self_eq_norm_sq] at h
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
  fin_cases i <;> norm_num at h ⊢ <;> exact h

theorem rootsH3_ne_zero (i : Fin 3) : rootsH3 i ≠ 0 := by
  intro hz
  have h := rootsH3_norm i
  rw [hz, norm_zero] at h
  norm_num at h

noncomputable def IsA3Wythoff {E : Type*} [PseudoMetricSpace E] (P : Set E) : Prop :=
  ∃ (J : Finset (Fin 3)) (x : ModelSpace 4), J.Nonempty ∧
    (∑ i, x i) = 0 ∧ WythoffSeed rootsA3 J x ∧ Congruent P (WythoffHull rootsA3 x)

noncomputable def IsB3Wythoff {E : Type*} [PseudoMetricSpace E] (P : Set E) : Prop :=
  ∃ (J : Finset (Fin 3)) (x : ModelSpace 3), J.Nonempty ∧
    WythoffSeed rootsB3 J x ∧ Congruent P (WythoffHull rootsB3 x)

noncomputable def IsH3Wythoff {E : Type*} [PseudoMetricSpace E] (P : Set E) : Prop :=
  ∃ (J : Finset (Fin 3)) (x : ModelSpace 3), J.Nonempty ∧
    WythoffSeed rootsH3 J x ∧ Congruent P (WythoffHull rootsH3 x)

noncomputable def IsWythoff3 {E : Type*} [PseudoMetricSpace E] (P : Set E) : Prop :=
  IsA3Wythoff P ∨ IsB3Wythoff P ∨ IsH3Wythoff P

noncomputable def cubeCorner3 : ModelSpace 3 := fun _ => (1 / 2 : ℝ)

theorem cubeCorner3_seed : WythoffSeed rootsB3 {⟨2, by decide⟩} cubeCorner3 := by
  intro i
  fin_cases i <;>
    simp [rootsB3, coordinateVector, cubeCorner3, inner_sub_left,
      EuclideanSpace.inner_single_left]

theorem cubeCorner3_unit_move : dist cubeCorner3 (mirrorReflection (rootsB3 2) cubeCorner3) = 1 :=
  ringed_seed_distance rootsB3 {⟨2, by decide⟩} cubeCorner3 cubeCorner3_seed 2 (by simp) (rootsB3_ne_zero 2)

noncomputable def h3TerminalSeed : ModelSpace 3 :=
  (-1 / 2 : ℝ) • coordinateVector 1 + (goldenRatio / 2) • coordinateVector (⟨2, by decide⟩ : Fin 3)

theorem h3TerminalSeed_seed : WythoffSeed rootsH3 {⟨2, by decide⟩} h3TerminalSeed := by
  intro i
  rw [rootsH3_norm]
  fin_cases i <;>
    norm_num [rootsH3, h3TerminalSeed, coordinateVector, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, inner_neg_left,
      EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  all_goals nlinarith [goldenRatio_sq]

theorem h3TerminalSeed_unit_move :
    dist h3TerminalSeed (mirrorReflection (rootsH3 2) h3TerminalSeed) = 1 :=
  ringed_seed_distance rootsH3 {⟨2, by decide⟩} h3TerminalSeed h3TerminalSeed_seed 2
    (by simp) (rootsH3_ne_zero 2)

noncomputable def polygonPrismModel (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin 2 ⊕ Fin 1)) := product (unitPolygon n) unitInterval

noncomputable def IsPolygonPrism {E : Type*} [PseudoMetricSpace E] (P : Set E) : Prop :=
  ∃ n : ℕ, 3 ≤ n ∧ Congruent P (polygonPrismModel n)

noncomputable def IsAntiprism {E : Type*} [PseudoMetricSpace E] (P : Set E) : Prop :=
  ∃ n : ℕ, 3 ≤ n ∧ Congruent P (antiprismModel n)

/-- Unit simple roots are required because the certificate's coefficients
refer to its unit-root Gram basis. -/
noncomputable def snubCubeRoots (i : Fin 3) : Space 3 := ‖rootsB3 i‖⁻¹ • rootsB3 i

noncomputable def snubDodecaRoots : Fin 3 → Space 3 := rootsH3

theorem snubCubeRoots_norm (i : Fin 3) : ‖snubCubeRoots i‖ = 1 := by
  rw [snubCubeRoots, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (rootsB3_ne_zero i))]

theorem rootsB3_norm (i : Fin 3) : ‖rootsB3 i‖ = ![Real.sqrt 2, Real.sqrt 2, (1 : ℝ)] i := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by fin_cases i <;> norm_num)).mp
  rw [← real_inner_self_eq_norm_sq, rootsB3_gram]
  fin_cases i <;> norm_num [Real.sq_sqrt]

/-- This is the exact unit-root Gram matrix used by the snub certificate. -/
theorem snubCubeRoots_gram (i j : Fin 3) :
    ⟪snubCubeRoots i, snubCubeRoots j⟫ =
      !![(1 : ℝ), -1 / 2, 0; -1 / 2, 1, -Real.sqrt 2 / 2;
        0, -Real.sqrt 2 / 2, 1] i j := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  simp only [snubCubeRoots, real_inner_smul_left, inner_smul_right, rootsB3_norm, rootsB3_gram]
  fin_cases i <;> fin_cases j <;> norm_num <;>
    field_simp

noncomputable def snubPhysicalSeed (roots : Fin 3 → Space 3) (c : Space 3) : Space 3 :=
  ∑ i, c i • roots i

/-- Generator 0 is R0 R1; generator 1 is R1 R2. Words act right to left. -/
noncomputable def snubRotationWord (roots : Fin 3 → Space 3)
    (w : List (Fin 2)) (p : Space 3) : Space 3 :=
  reflectionWord roots (w.flatMap (fun i => if i = 0 then [0, 1] else [1, 2])) p

noncomputable def snubEdgeScale (roots : Fin 3 → Space 3) (c : Space 3) : ℝ :=
  dist (snubPhysicalSeed roots c) (snubRotationWord roots [0] (snubPhysicalSeed roots c))

/-- Exact algebraic seed constraints, including the certificate's fixed
rational box and the positive normalization denominator. -/
noncomputable def SnubSeed (roots : Fin 3 → Space 3) (lo hi : Fin 3 → ℚ)
    (c : Space 3) : Prop :=
  (∀ i, (lo i : ℝ) ≤ c i ∧ c i ≤ (hi i : ℝ)) ∧
  ‖snubPhysicalSeed roots c‖ ^ 2 = 1 ∧
  dist (snubPhysicalSeed roots c) (snubRotationWord roots [0] (snubPhysicalSeed roots c)) ^ 2 =
    dist (snubPhysicalSeed roots c) (snubRotationWord roots [1] (snubPhysicalSeed roots c)) ^ 2 ∧
  dist (snubPhysicalSeed roots c) (snubRotationWord roots [0] (snubPhysicalSeed roots c)) ^ 2 =
    dist (snubPhysicalSeed roots c) (snubRotationWord roots [0, 1] (snubPhysicalSeed roots c)) ^ 2 ∧
  0 < snubEdgeScale roots c

noncomputable def snubIndexedPoint (roots : Fin 3 → Space 3) (c : Space 3)
    (w : List (Fin 2)) : Space 3 :=
  (snubEdgeScale roots c)⁻¹ • snubRotationWord roots w (snubPhysicalSeed roots c)

noncomputable def snubFinitePoints {n : ℕ} (roots : Fin 3 → Space 3) (c : Space 3)
    (words : Fin n → List (Fin 2)) : Finset (Space 3) :=
  Finset.univ.image (fun i => snubIndexedPoint roots c (words i))

noncomputable def snubFiniteHull {n : ℕ} (roots : Fin 3 → Space 3) (c : Space 3)
    (words : Fin n → List (Fin 2)) : Set (Space 3) :=
  convexHull ℝ (snubFinitePoints roots c words : Set (Space 3))

theorem snubFinitePoints_card_le {n : ℕ} (roots : Fin 3 → Space 3) (c : Space 3)
    (words : Fin n → List (Fin 2)) : (snubFinitePoints roots c words).card ≤ n := by
  exact (Finset.card_image_le).trans_eq (by simp)

theorem snubFiniteHull_finitePolytope {n : ℕ} (hn : 0 < n)
    (roots : Fin 3 → Space 3) (c : Space 3) (words : Fin n → List (Fin 2)) :
    FinitePolytope (snubFiniteHull roots c words) := by
  refine ⟨snubFinitePoints roots c words, ?_, rfl⟩
  exact ⟨_, Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩

theorem snubIndexedPoint_norm (roots : Fin 3 → Space 3) (c : Space 3)
    (w : List (Fin 2)) :
    ‖snubIndexedPoint roots c w‖ = ‖snubIndexedPoint roots c []‖ := by
  simp only [snubIndexedPoint, norm_smul, snubRotationWord, reflectionWord_norm]

theorem SnubSeed.first_unit_chord {roots : Fin 3 → Space 3} {lo hi : Fin 3 → ℚ}
    {c : Space 3} (hc : SnubSeed roots lo hi c) :
    dist (snubIndexedPoint roots c []) (snubIndexedPoint roots c [0]) = 1 := by
  have hp : 0 < snubEdgeScale roots c := hc.2.2.2.2
  change dist ((snubEdgeScale roots c)⁻¹ • snubPhysicalSeed roots c)
    ((snubEdgeScale roots c)⁻¹ • snubRotationWord roots [0] (snubPhysicalSeed roots c)) = 1
  rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hp, ← dist_eq_norm]
  exact inv_mul_cancel₀ hp.ne'

noncomputable def snubCubeWords : Fin 24 → List (Fin 2) :=
  ![[],
    [0],
    [1],
    [0, 0],
    [1, 0],
    [0, 1],
    [1, 1],
    [1, 0, 0],
    [0, 1, 0],
    [1, 1, 0],
    [0, 0, 1],
    [0, 1, 1],
    [0, 1, 0, 0],
    [1, 1, 0, 0],
    [0, 0, 1, 0],
    [0, 1, 1, 0],
    [1, 0, 0, 1],
    [0, 0, 1, 1],
    [0, 0, 1, 0, 0],
    [0, 1, 1, 0, 0],
    [0, 0, 1, 1, 0],
    [1, 1, 0, 0, 1],
    [1, 0, 0, 1, 1],
    [1, 0, 0, 1, 1, 0]]

noncomputable def snubCubeLower : Fin 3 → ℚ :=
  ![878773643867953786452859399614471130035649824049 / 730750818665451459101842416358141509827966271488,
    1356553218682339905163570511975437229234135626399 / 730750818665451459101842416358141509827966271488,
    1142908516083937836411527736082268572123007243307 / 730750818665451459101842416358141509827966271488]

noncomputable def snubCubeUpper : Fin 3 → ℚ :=
  ![878773643867953786452860861116108460938568027735 / 730750818665451459101842416358141509827966271488,
    1356553218682339905163571973477074560137053830085 / 730750818665451459101842416358141509827966271488,
    1142908516083937836411529197583905903025925446993 / 730750818665451459101842416358141509827966271488]

noncomputable def snubDodecaWords : Fin 60 → List (Fin 2) :=
  ![[],
    [0],
    [1],
    [0, 0],
    [1, 0],
    [0, 1],
    [1, 1],
    [0, 0, 0],
    [1, 0, 0],
    [1, 1, 0],
    [0, 0, 1],
    [1, 0, 1],
    [0, 1, 1],
    [1, 0, 0, 0],
    [1, 1, 0, 0],
    [0, 1, 1, 0],
    [0, 0, 0, 1],
    [1, 0, 0, 1],
    [1, 1, 0, 1],
    [0, 0, 1, 1],
    [1, 0, 1, 1],
    [1, 1, 0, 0, 0],
    [0, 1, 1, 0, 0],
    [0, 0, 1, 1, 0],
    [1, 0, 1, 1, 0],
    [1, 0, 0, 0, 1],
    [1, 1, 0, 0, 1],
    [1, 0, 0, 1, 1],
    [1, 1, 0, 1, 1],
    [0, 1, 1, 0, 0, 0],
    [0, 0, 1, 1, 0, 0],
    [1, 0, 1, 1, 0, 0],
    [1, 0, 0, 1, 1, 0],
    [1, 1, 0, 1, 1, 0],
    [1, 1, 0, 0, 0, 1],
    [0, 1, 1, 0, 0, 1],
    [1, 1, 0, 0, 1, 1],
    [0, 0, 1, 1, 0, 0, 0],
    [1, 0, 1, 1, 0, 0, 0],
    [1, 0, 0, 1, 1, 0, 0],
    [1, 1, 0, 1, 1, 0, 0],
    [1, 1, 0, 0, 1, 1, 0],
    [0, 1, 1, 0, 0, 0, 1],
    [0, 0, 1, 1, 0, 0, 1],
    [0, 1, 1, 0, 0, 1, 1],
    [1, 0, 0, 1, 1, 0, 0, 0],
    [1, 1, 0, 1, 1, 0, 0, 0],
    [1, 1, 0, 0, 1, 1, 0, 0],
    [0, 1, 1, 0, 0, 1, 1, 0],
    [0, 0, 1, 1, 0, 0, 0, 1],
    [1, 0, 1, 1, 0, 0, 0, 1],
    [1, 0, 0, 1, 1, 0, 0, 1],
    [0, 0, 1, 1, 0, 0, 1, 1],
    [0, 1, 1, 0, 0, 1, 1, 0, 0],
    [0, 0, 1, 1, 0, 0, 1, 1, 0],
    [1, 0, 0, 1, 1, 0, 0, 0, 1],
    [1, 1, 0, 1, 1, 0, 0, 0, 1],
    [1, 1, 0, 0, 1, 1, 0, 0, 1],
    [1, 0, 0, 1, 1, 0, 0, 1, 1],
    [1, 0, 0, 1, 1, 0, 0, 1, 1, 0]]

noncomputable def snubDodecaLower : Fin 3 → ℚ :=
  ![986567556175236384102055818840935033608579609443 / 365375409332725729550921208179070754913983135744,
    575069769489039590624913033886112940301606083865 / 182687704666362864775460604089535377456991567872,
    1277190510763957147939204089733113776164650455797 / 730750818665451459101842416358141509827966271488]

noncomputable def snubDodecaUpper : Fin 3 → ℚ :=
  ![986567556175236384102056549591753699060038711287 / 365375409332725729550921208179070754913983135744,
    575069769489039590624913399261522273027335634787 / 182687704666362864775460604089535377456991567872,
    1277190510763957147939205551234751107067568659483 / 730750818665451459101842416358141509827966271488]

noncomputable def snubCubeModel (c : Space 3) : Set (Space 3) :=
  snubFiniteHull snubCubeRoots c snubCubeWords

noncomputable def snubDodecaModel (c : Space 3) : Set (Space 3) :=
  snubFiniteHull snubDodecaRoots c snubDodecaWords

noncomputable def IsSnubCube {E : Type*} [PseudoMetricSpace E] (P : Set E) : Prop :=
  ∃ c : Space 3, SnubSeed snubCubeRoots snubCubeLower snubCubeUpper c ∧
    Congruent P (snubCubeModel c)

noncomputable def IsSnubDodeca {E : Type*} [PseudoMetricSpace E] (P : Set E) : Prop :=
  ∃ c : Space 3, SnubSeed snubDodecaRoots snubDodecaLower snubDodecaUpper c ∧
    Congruent P (snubDodecaModel c)

/-- Concrete Platonic/Archimedean constructions, including the two snubs. -/
noncomputable def IsFinitePolyhedronType {E : Type*} [PseudoMetricSpace E] (P : Set E) : Prop :=
  IsWythoff3 P ∨ IsSnubCube P ∨ IsSnubDodeca P

/-- Explicit full convex uniform-polyhedron model catalogue. This
predicate states membership in the constructions, not their classification. -/
noncomputable def IsPolyhedronModel {E : Type*} [PseudoMetricSpace E] (P : Set E) : Prop :=
  IsFinitePolyhedronType P ∨ IsPolygonPrism P ∨ IsAntiprism P

theorem snubCubeModel_finitePolytope (c : Space 3) : FinitePolytope (snubCubeModel c) :=
  snubFiniteHull_finitePolytope (by norm_num) _ _ _

theorem snubDodecaModel_finitePolytope (c : Space 3) : FinitePolytope (snubDodecaModel c) :=
  snubFiniteHull_finitePolytope (by norm_num) _ _ _

theorem snubCubeWords_initial : snubCubeWords 0 = [] ∧ snubCubeWords 1 = [0] := by decide

theorem snubDodecaWords_initial : snubDodecaWords 0 = [] ∧ snubDodecaWords 1 = [0] := by decide

theorem snubCube_root_box_nonempty : ∀ i, snubCubeLower i < snubCubeUpper i := by
  intro i
  fin_cases i <;> norm_num [snubCubeLower, snubCubeUpper]

theorem snubDodeca_root_box_nonempty : ∀ i, snubDodecaLower i < snubDodecaUpper i := by
  intro i
  fin_cases i <;> norm_num [snubDodecaLower, snubDodecaUpper]

end Uniform5.Composition
