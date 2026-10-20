import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull

/-!
# Concrete reflection models for the rank-five Wythoff families

The roots use the paper's node order. Type A is represented in its standard
sum-zero hyperplane in six-dimensional Euclidean space. Congruence uses the
whole convex hull, including when the ambient dimensions differ.
-/
noncomputable section
namespace Uniform5.Composition

abbrev ModelSpace (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def coordinateVector {n : ℕ} (i : Fin n) : ModelSpace n :=
  EuclideanSpace.single i 1

/-- Reflection in the mirror perpendicular to a root. -/
noncomputable def mirrorReflection {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (a : E) : E ≃ₗᵢ[ℝ] E :=
  (ℝ ∙ a)ᗮ.reflection

theorem mirrorReflection_involutive {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (a : E) :
    Function.Involutive (mirrorReflection a) :=
  Submodule.reflection_involutive _

theorem mirrorReflection_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (a x : E) :
    ‖mirrorReflection a x‖ = ‖x‖ :=
  (mirrorReflection a).norm_map x

/-- The explicit reflection formula. All concrete model roots are nonzero. -/
theorem mirrorReflection_formula {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (a x : E) :
    mirrorReflection a x = x - (2 * (@inner ℝ E _ a x / ‖a‖ ^ 2)) • a := by
  rw [mirrorReflection, Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply]
  simp only [neg_sub, two_smul, add_smul, two_mul, RCLike.ofReal_real_eq_id, id_eq]

/-- A5: adjacent differences e₀-e₁, ..., e₄-e₅ in R6. -/
noncomputable def rootsA5 (i : Fin 5) : ModelSpace 6 :=
  coordinateVector i.castSucc - coordinateVector i.succ

/-- B5: linear diagram 3,3,3,4, with its short root at node 4. -/
noncomputable def rootsB5 (i : Fin 5) : ModelSpace 5 :=
  if h : i.val < 4 then
    coordinateVector i - coordinateVector ⟨i.val + 1, by omega⟩
  else coordinateVector i

/-- D5: chain 0--1--2, with nodes 3 and 4 attached to node 2. -/
noncomputable def rootsD5 (i : Fin 5) : ModelSpace 5 :=
  if h : i.val < 4 then
    coordinateVector i - coordinateVector ⟨i.val + 1, by omega⟩
  else coordinateVector (⟨3, by decide⟩ : Fin 5) + coordinateVector (⟨4, by decide⟩ : Fin 5)

theorem rootsA5_ne_zero (i : Fin 5) : rootsA5 i ≠ 0 := by
  intro h
  have hc := congrArg (fun x : ModelSpace 6 => x i.castSucc) h
  fin_cases i <;> norm_num [rootsA5, coordinateVector,
    EuclideanSpace.single_apply, Fin.ext_iff] at hc

theorem rootsB5_ne_zero (i : Fin 5) : rootsB5 i ≠ 0 := by
  intro h
  have hc := congrArg (fun x : ModelSpace 5 => x i) h
  fin_cases i <;> norm_num [rootsB5, coordinateVector,
    EuclideanSpace.single_apply, Fin.ext_iff] at hc

theorem rootsD5_ne_zero (i : Fin 5) : rootsD5 i ≠ 0 := by
  intro h
  have hc := congrArg (fun x : ModelSpace 5 => x i) h
  fin_cases i <;> norm_num [rootsD5, coordinateVector,
    EuclideanSpace.single_apply, Fin.ext_iff] at hc

/-- Finite words in involutive generators give the generated group orbit. -/
noncomputable def reflectionWord {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {k : ℕ} (roots : Fin k → E) : List (Fin k) → E → E
  | [], x => x
  | i :: w, x => mirrorReflection (roots i) (reflectionWord roots w x)

noncomputable def reflectionOrbit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {k : ℕ} (roots : Fin k → E) (x : E) : Set E :=
  {y | ∃ w, reflectionWord roots w x = y}

/-- Signed distance 1/2 at ringed mirrors, zero at unringed mirrors. -/
noncomputable def WythoffSeed {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (roots : Fin k → E) (J : Finset (Fin k)) (x : E) : Prop :=
  ∀ i, @inner ℝ E _ (roots i) x = if i ∈ J then ‖roots i‖ / 2 else 0

/-- With nonzero roots, the seed equations are precisely the signed
mirror-distance conditions stated in the paper. -/
theorem wythoffSeed_iff_signed_distance {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {k : ℕ} (roots : Fin k → E)
    (hne : ∀ i, roots i ≠ 0) (J : Finset (Fin k)) (x : E) :
    WythoffSeed roots J x ↔
      ∀ i, @inner ℝ E _ (roots i) x / ‖roots i‖ =
        if i ∈ J then (1 / 2 : ℝ) else 0 := by
  unfold WythoffSeed
  apply forall_congr'
  intro i
  have hn : ‖roots i‖ ≠ 0 := norm_ne_zero_iff.mpr (hne i)
  rw [div_eq_iff hn]
  by_cases hi : i ∈ J <;> simp [hi, div_eq_mul_inv, mul_comm]

noncomputable def WythoffHull {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {k : ℕ} (roots : Fin k → E) (x : E) : Set E :=
  convexHull ℝ (reflectionOrbit roots x)

/-- Type A uses its canonical zero-sum representative. -/
noncomputable def IsA5Wythoff {E : Type*} [PseudoMetricSpace E] (S : Set E) : Prop :=
  ∃ (J : Finset (Fin 5)) (x : ModelSpace 6), J.Nonempty ∧
    (∑ i, x i) = 0 ∧ WythoffSeed rootsA5 J x ∧
    Nonempty (S ≃ᵢ WythoffHull rootsA5 x)

noncomputable def IsB5Wythoff {E : Type*} [PseudoMetricSpace E] (S : Set E) : Prop :=
  ∃ (J : Finset (Fin 5)) (x : ModelSpace 5), J.Nonempty ∧
    WythoffSeed rootsB5 J x ∧ Nonempty (S ≃ᵢ WythoffHull rootsB5 x)

noncomputable def IsD5Wythoff {E : Type*} [PseudoMetricSpace E] (S : Set E) : Prop :=
  ∃ (J : Finset (Fin 5)) (x : ModelSpace 5), J.Nonempty ∧
    WythoffSeed rootsD5 J x ∧ Nonempty (S ≃ᵢ WythoffHull rootsD5 x)

/-- Exactly the concrete rank-five Wythoff alternatives (K1). -/
noncomputable def IsWythoff5 {E : Type*} [PseudoMetricSpace E] (S : Set E) : Prop :=
  IsA5Wythoff S ∨ IsB5Wythoff S ∨ IsD5Wythoff S

theorem seed_mem_orbit {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {k : ℕ}
    (roots : Fin k → E) (x : E) : x ∈ reflectionOrbit roots x :=
  ⟨[], rfl⟩

theorem seed_mem_hull {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {k : ℕ}
    (roots : Fin k → E) (x : E) : x ∈ WythoffHull roots x :=
  subset_convexHull ℝ _ (seed_mem_orbit roots x)

theorem reflectionWord_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {k : ℕ}
    (roots : Fin k → E) (w : List (Fin k)) (x : E) :
    ‖reflectionWord roots w x‖ = ‖x‖ := by
  induction w with
  | nil => rfl
  | cons i w ih => exact (mirrorReflection_norm _ _).trans ih

/-- A mirror negates its own normal, a check against accidentally using
an identity or a projection in the orbit construction. -/
theorem mirrorReflection_root {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (a : E) :
    mirrorReflection a a = -a :=
  Submodule.reflection_orthogonalComplement_singleton_eq_neg a

/-- A ringed mirror moves the seed exactly one unit. This checks the
normalization used in the definition, without assuming hull uniformity. -/
theorem ringed_seed_distance {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {k : ℕ}
    (roots : Fin k → E) (J : Finset (Fin k)) (x : E)
    (hseed : WythoffSeed roots J x) (j : Fin k) (hj : j ∈ J)
    (hne : roots j ≠ 0) : dist x (mirrorReflection (roots j) x) = 1 := by
  have hn : 0 < ‖roots j‖ := norm_pos_iff.mpr hne
  have hi : @inner ℝ E _ (roots j) x = ‖roots j‖ / 2 := by
    simpa [hj] using hseed j
  have hc : 2 * (@inner ℝ E _ (roots j) x / ‖roots j‖ ^ 2) =
      1 / ‖roots j‖ := by
    rw [hi]
    field_simp
    ring
  rw [dist_eq_norm, mirrorReflection_formula, hc, sub_sub_cancel, norm_smul]
  rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hn)]
  exact one_div_mul_cancel (ne_of_gt hn)

/-- Every nonempty ring pattern has two hull points separated by one unit;
in particular these model definitions cannot describe a singleton. -/
theorem wythoffHull_unit_pair {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {k : ℕ}
    (roots : Fin k → E) (hne : ∀ i, roots i ≠ 0)
    (J : Finset (Fin k)) (hJ : J.Nonempty) (x : E)
    (hseed : WythoffSeed roots J x) :
    ∃ u ∈ WythoffHull roots x, ∃ v ∈ WythoffHull roots x, dist u v = 1 := by
  obtain ⟨j, hj⟩ := hJ
  refine ⟨x, seed_mem_hull roots x, mirrorReflection (roots j) x, ?_,
    ringed_seed_distance roots J x hseed j hj (hne j)⟩
  apply subset_convexHull ℝ _
  exact ⟨[j], rfl⟩

private theorem unit_pair_of_isometryEquiv {E F : Type*}
    [PseudoMetricSpace E] [PseudoMetricSpace F] {S : Set E} {T : Set F}
    (e : S ≃ᵢ T) (h : ∃ u ∈ T, ∃ v ∈ T, dist u v = 1) :
    ∃ u ∈ S, ∃ v ∈ S, dist u v = 1 := by
  obtain ⟨u, hu, v, hv, huv⟩ := h
  refine ⟨e.symm ⟨u, hu⟩, (e.symm ⟨u, hu⟩).property,
    e.symm ⟨v, hv⟩, (e.symm ⟨v, hv⟩).property, ?_⟩
  exact (e.symm.dist_eq _ _).trans huv

/-- A concrete constraint on every K1 member, also after congruence. -/
theorem isWythoff5_unit_pair {E : Type*} [PseudoMetricSpace E]
    {S : Set E} (h : IsWythoff5 S) :
    ∃ u ∈ S, ∃ v ∈ S, dist u v = 1 := by
  rcases h with ha | hb | hd
  · obtain ⟨J, x, hJ, _, hseed, ⟨e⟩⟩ := ha
    exact unit_pair_of_isometryEquiv e
      (wythoffHull_unit_pair rootsA5 rootsA5_ne_zero J hJ x hseed)
  · obtain ⟨J, x, hJ, hseed, ⟨e⟩⟩ := hb
    exact unit_pair_of_isometryEquiv e
      (wythoffHull_unit_pair rootsB5 rootsB5_ne_zero J hJ x hseed)
  · obtain ⟨J, x, hJ, hseed, ⟨e⟩⟩ := hd
    exact unit_pair_of_isometryEquiv e
      (wythoffHull_unit_pair rootsD5 rootsD5_ne_zero J hJ x hseed)

/-- Rejection sanity check: no singleton can be mislabeled a K1 model. -/
theorem singleton_not_isWythoff5 {E : Type*} [PseudoMetricSpace E] (a : E) :
    ¬ IsWythoff5 ({a} : Set E) := by
  intro h
  obtain ⟨u, hu, v, hv, huv⟩ := isWythoff5_unit_pair h
  have hu' : u = a := hu
  have hv' : v = a := hv
  simp [hu', hv'] at huv

/-- The standard positive vertex of the unit five-cube. -/
noncomputable def cubeCorner : ModelSpace 5 := fun _ => (1 / 2 : ℝ)

/-- The B5 ring pattern 00001 has the expected unit-cube seed. -/
theorem cubeCorner_seed : WythoffSeed rootsB5 {4} cubeCorner := by
  intro i
  fin_cases i <;>
    simp [rootsB5, coordinateVector, cubeCorner, inner_sub_left,
      EuclideanSpace.inner_single_left]

/-- The last B5 generator flips precisely the last coordinate. -/
theorem cubeCorner_last_reflection :
    mirrorReflection (rootsB5 4) cubeCorner =
      (fun j => if j = (4 : Fin 5) then (-1 / 2 : ℝ) else 1 / 2) := by
  have hroot : rootsB5 4 = coordinateVector 4 := by
    rw [rootsB5, dif_neg (by decide)]
  rw [hroot, mirrorReflection_formula]
  ext j
  by_cases hj : j = 4 <;>
    norm_num [coordinateVector, cubeCorner, EuclideanSpace.inner_single_left,
      EuclideanSpace.single_apply, hj]

/-- The flipped cube corner is really a generated orbit point. -/
theorem cubeCorner_flipped_mem_orbit :
    (fun j => if j = (4 : Fin 5) then (-1 / 2 : ℝ) else 1 / 2) ∈
      reflectionOrbit rootsB5 cubeCorner :=
  ⟨[4], cubeCorner_last_reflection⟩

/-- A concrete nonempty instance of K1; its seed has been checked above. -/
theorem cube_model_is_K1 : IsWythoff5 (WythoffHull rootsB5 cubeCorner) := by
  right; left
  exact ⟨{4}, cubeCorner, by simp, cubeCorner_seed, ⟨IsometryEquiv.refl _⟩⟩

end Uniform5.Composition
