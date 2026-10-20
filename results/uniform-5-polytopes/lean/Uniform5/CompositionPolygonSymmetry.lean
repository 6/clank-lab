import Uniform5.CompositionEmbedding

/-!
# Actual rotational symmetries of the concrete regular polygons

The coordinate rotations preserve the explicit circular vertex set. Their
convex-hull action proves vertex transitivity, which then transports into
any finite-dimensional Euclidean ambient space by isometric embedding.
-/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace

noncomputable abbrev planeRotationLinear (θ : ℝ) : Plane →ₗ[ℝ] Plane :=
  Uniform5.polygonRotationLinear θ

theorem plane_norm_sq (x : Plane) : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two]

/-- The usual real two-dimensional rotation as an actual linear isometry. -/
noncomputable abbrev planeRotationIsometry (θ : ℝ) : Plane →ₗᵢ[ℝ] Plane :=
  Uniform5.polygonRotation θ

noncomputable def planeRotation (θ : ℝ) : Plane ≃ᵃⁱ[ℝ] Plane :=
  (LinearIsometryEquiv.ofSurjective (planeRotationIsometry θ)
    ((LinearMap.injective_iff_surjective (f := (planeRotationIsometry θ).toLinearMap)).mp
      (planeRotationIsometry θ).injective)).toAffineIsometryEquiv

theorem planeRotation_apply (θ : ℝ) (x : Plane) :
    planeRotation θ x = !₂[Real.cos θ * x 0 - Real.sin θ * x 1,
      Real.sin θ * x 0 + Real.cos θ * x 1] := rfl

theorem planeRotation_polygonPoint (θ : ℝ) (n : ℕ) (r : ℝ) (i : Fin n) :
    planeRotation θ (polygonPoint n r i) =
      !₂[r * Real.cos (θ + 2 * Real.pi * (i : ℕ) / n),
        r * Real.sin (θ + 2 * Real.pi * (i : ℕ) / n)] := by
  rw [planeRotation_apply]
  ext j
  fin_cases j <;> simp [polygonPoint, Real.cos_add, Real.sin_add] <;> ring

/-- Addition of polygon indices adds their angles modulo a full turn. -/
theorem polygon_angles_add {n : ℕ} [NeZero n] (i j : Fin n) :
    Real.cos (2 * Real.pi * ((i + j : Fin n) : ℕ) / n) =
      Real.cos (2 * Real.pi * (i : ℕ) / n + 2 * Real.pi * (j : ℕ) / n) ∧
    Real.sin (2 * Real.pi * ((i + j : Fin n) : ℕ) / n) =
      Real.sin (2 * Real.pi * (i : ℕ) / n + 2 * Real.pi * (j : ℕ) / n) := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hnat : ((i + j : Fin n) : ℕ) + n * ((i.val + j.val) / n) = i.val + j.val := by
    exact Nat.mod_add_div _ _
  have hreal : (((i + j : Fin n) : ℕ) : ℝ) + n * (((i.val + j.val) / n : ℕ) : ℝ) =
      (i.val : ℝ) + j.val := by exact_mod_cast hnat
  have hangle : 2 * Real.pi * (i : ℕ) / n + 2 * Real.pi * (j : ℕ) / n =
      2 * Real.pi * ((i + j : Fin n) : ℕ) / n +
        ((i.val + j.val) / n : ℕ) * (2 * Real.pi) := by
    field_simp
    linear_combination -2 * Real.pi * hreal
  rw [hangle, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]
  exact ⟨rfl, rfl⟩

theorem polygon_rotation_index {n : ℕ} [NeZero n] (r : ℝ) (i j : Fin n) :
    planeRotation (2 * Real.pi * (i : ℕ) / n) (polygonPoint n r j) =
      polygonPoint n r (i + j) := by
  rw [planeRotation_polygonPoint]
  have hh := polygon_angles_add i j
  simp only [polygonPoint, Uniform5.regularPolygonVertex, hh.1, hh.2]

theorem polygon_rotation_image {n : ℕ} [NeZero n] (r : ℝ) (i : Fin n) :
    planeRotation (2 * Real.pi * (i : ℕ) / n) '' polygon n r = polygon n r := by
  let g := planeRotation (2 * Real.pi * (i : ℕ) / n)
  have hrange : g '' Set.range (polygonPoint n r) = Set.range (polygonPoint n r) := by
    ext x
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨i + j, (polygon_rotation_index r i j).symm⟩
    · rintro ⟨j, rfl⟩
      refine ⟨polygonPoint n r (-i + j), ⟨-i + j, rfl⟩, ?_⟩
      change planeRotation _ _ = _
      rw [polygon_rotation_index]
      simp
  change g '' convexHull ℝ (Set.range (polygonPoint n r)) = _
  have hHull : g '' convexHull ℝ (Set.range (polygonPoint n r)) =
      convexHull ℝ (g '' Set.range (polygonPoint n r)) :=
    g.toAffineMap.image_convexHull _
  rw [hHull, hrange]
  rfl

/-- Every concrete regular polygon is vertex transitive under ambient
Euclidean symmetries. Its actual vertices are a subset of its generators. -/
theorem polygon_vertexTransitive {n : ℕ} (r : ℝ) (hn : 0 < n) :
    VertexTransitive (polygon n r) := by
  letI : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  intro v hv w hw
  obtain ⟨i, rfl⟩ := extremePoints_convexHull_subset hv
  obtain ⟨j, rfl⟩ := extremePoints_convexHull_subset hw
  let g := planeRotation (2 * Real.pi * (i : ℕ) / n)
  let h := planeRotation (2 * Real.pi * (j : ℕ) / n)
  have hgP : g '' polygon n r = polygon n r := polygon_rotation_image r i
  have hhP : h '' polygon n r = polygon n r := polygon_rotation_image r j
  have hg0 : g (polygonPoint n r 0) = polygonPoint n r i := by
    simpa using polygon_rotation_index r i 0
  have hh0 : h (polygonPoint n r 0) = polygonPoint n r j := by
    simpa using polygon_rotation_index r j 0
  refine ⟨g.symm.trans h, ?_, ?_⟩
  · change (fun x => h (g.symm x)) '' polygon n r = _
    have hginv : g.symm '' polygon n r = polygon n r := by
      calc
        _ = g.symm '' (g '' polygon n r) := congrArg (fun S => g.symm '' S) hgP.symm
        _ = _ := affineIsometry_symm_image_image g _
    rw [← Set.image_image, hginv, hhP]
  · change h (g.symm (polygonPoint n r i)) = _
    rw [← hg0, g.symm_apply_apply, hh0]

/-- The regular-polygon base case of recursive uniformity supplies genuine
ambient vertex transitivity, including polygons embedded in higher dimensions. -/
theorem uniform2_vertexTransitive {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Set E} (hP : Uniform 2 P) : VertexTransitive P := by
  rw [Uniform] at hP
  obtain ⟨n, hn, r, _, f, rfl⟩ := hP
  exact embedding_vertexTransitive_image f (polygon_vertexTransitive r (by omega))

end Uniform5.Composition
