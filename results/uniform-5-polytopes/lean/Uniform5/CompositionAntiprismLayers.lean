import Uniform5.CompositionAntiprismCrossNeighbors

/-! Both antiprism layers are actual regular-polygon faces. -/
noncomputable section
namespace Uniform5.Composition
open Set

noncomputable def antiprismLayerSlice (n : ℕ) (b : Bool) : Plane →ᵃⁱ[ℝ] Space 3 :=
  (horizontalPolygonSlice (if b then -(antiprismHeight n / 2) else antiprismHeight n / 2)).comp
    (planeRotation (if b then Real.pi / n else 0)).toAffineIsometry

@[simp] theorem antiprismLayerSlice_point (n : ℕ) (b : Bool) (i : Fin n) :
    antiprismLayerSlice n b (polygonPoint n (unitPolygonRadius n) i) = antiprismPoint n b i := by
  change horizontalPolygonSlice _ (planeRotation _ (polygonPoint n _ i)) = _
  rw [planeRotation_polygonPoint]
  change !₂[unitPolygonRadius n * Real.cos ((if b then Real.pi / n else 0) + 2 * Real.pi * (i : ℕ) / n),
    unitPolygonRadius n * Real.sin ((if b then Real.pi / n else 0) + 2 * Real.pi * (i : ℕ) / n),
    if b then -(antiprismHeight n / 2) else antiprismHeight n / 2] = _
  ext j
  fin_cases j <;> simp [antiprismPoint, add_comm]

noncomputable def antiprismLayer (n : ℕ) (b : Bool) : Set (Space 3) :=
  convexHull ℝ (Set.range (antiprismPoint n b))

theorem antiprismLayer_eq_image (n : ℕ) (b : Bool) :
    antiprismLayer n b = antiprismLayerSlice n b '' unitPolygon n := by
  change convexHull ℝ (Set.range (antiprismPoint n b)) =
    (antiprismLayerSlice n b).toAffineMap '' convexHull ℝ (Set.range (polygonPoint n (unitPolygonRadius n)))
  rw [(antiprismLayerSlice n b).toAffineMap.image_convexHull]
  congr 1
  ext x
  simp only [mem_image, mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, antiprismLayerSlice_point n b i⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (antiprismLayerSlice_point n b i).symm⟩

/-- A signed vertical functional exposes exactly either specified layer. -/
theorem antiprism_layer_face {n : ℕ} (hn : 3 ≤ n) (b : Bool) :
    IsConvexFace (antiprismModel n) (antiprismLayer n b) := by
  let V := Set.range (fun p : Bool × Fin n => antiprismPoint n p.1 p.2)
  let L : Space 3 →L[ℝ] ℝ := if b then -(EuclideanSpace.proj 2) else EuclideanSpace.proj 2
  let h := antiprismHeight n / 2
  let T := {x ∈ antiprismModel n | L x = h}
  have hp : 0 < h := half_pos (antiprismHeight_pos hn)
  have he (c : Bool) (i : Fin n) : L (antiprismPoint n c i) = if c = b then h else -h := by
    cases b <;> cases c <;> simp [L, antiprismPoint, h]
  have hb : ∀ x ∈ antiprismModel n, L x ≤ h := by
    apply convexHull_min _ ((convex_Iic h).linear_preimage L.toLinearMap)
    rintro _ ⟨⟨c, i⟩, rfl⟩
    change L (antiprismPoint n c i) ≤ h
    rw [he]
    split_ifs <;> linarith
  let i : Fin n := ⟨0, by omega⟩
  have hv : antiprismPoint n b i ∈ antiprismModel n :=
    subset_convexHull ℝ V ⟨(b, i), rfl⟩
  have hex : IsExposed ℝ (antiprismModel n) T := by
    have hh := support_level_isExposed L (antiprismPoint n b i) hv
      (by simpa only [he, if_pos rfl] using hb)
    simpa only [he, if_pos rfl] using hh
  have hf : IsConvexFace (antiprismModel n) T :=
    ⟨hex.convex (convex_convexHull ℝ _), hex.isExtreme⟩
  have hinter : V ∩ T = Set.range (antiprismPoint n b) := by
    ext x
    constructor
    · rintro ⟨⟨⟨c, k⟩, rfl⟩, _, hk⟩
      change L (antiprismPoint n c k) = h at hk
      rw [he] at hk
      have hc : c = b := by by_contra hc; rw [if_neg hc] at hk; linarith
      subst c
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨⟨(b, k), rfl⟩, subset_convexHull ℝ V ⟨(b, k), rfl⟩, by simp [he]⟩
  have hT : T = antiprismLayer n b := by
    rw [face_convexHull_eq hf, hinter]
    rfl
  rwa [hT] at hf

/-- Both layers retain their exact n-gon counts and geometry. -/
theorem antiprism_layer_polygonFace {n : ℕ} (hn : 3 ≤ n) (b : Bool) :
    PolygonFace (antiprismModel n) (antiprismLayer n b) n := by
  refine ⟨antiprism_layer_face hn b, ?_⟩
  rw [antiprismLayer_eq_image]
  exact (embedding_polygonFace_image (antiprismLayerSlice n b) (unitPolygon_self_polygonFace hn)).2

/-- The layer embedding transports all distances without coordinate
assumptions on the ambient polytope. -/
theorem antiprism_same_layer_dist (n : ℕ) (b : Bool) (i j : Fin n) :
    dist (antiprismPoint n b i) (antiprismPoint n b j) =
      dist (polygonPoint n (unitPolygonRadius n) i) (polygonPoint n (unitPolygonRadius n) j) := by
  rw [← antiprismLayerSlice_point n b i, ← antiprismLayerSlice_point n b j]
  exact (antiprismLayerSlice n b).dist_map _ _

end Uniform5.Composition
