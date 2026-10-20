import Uniform5.CompositionWordAngle
import Uniform5.CompositionTransverseFacets

/-! Actual polygon cycles with coherent intrinsic radii and facet word angles. -/
noncomputable section
namespace Uniform5.Composition
open Set InnerProductGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A nonnegative radius about the actual vertex centroid. -/
def HasIntrinsicRadius (P : Set E) (r : ℝ) : Prop :=
  ∃ hP : FinitePolytope P, 0 ≤ r ∧
    ∀ x ∈ P.extremePoints ℝ, ‖x - vertexCentroid (vertices P hP)‖ ^ 2 = r ^ 2

theorem HasIntrinsicRadius.unique {P : Set E} {r s : ℝ}
    (hr : HasIntrinsicRadius P r) (hs : HasIntrinsicRadius P s) : r = s := by
  obtain ⟨hP, hr, hsr⟩ := hr
  obtain ⟨_, hs, hss⟩ := hs
  obtain ⟨x, hx⟩ := finitePolytope_extremePoints_nonempty hP
  exact (sq_eq_sq₀ hr hs).mp ((hsr x hx).symm.trans (hss x hx))

/-- The intrinsic circumradius, when it exists; zero otherwise. Its choice
is unique whenever it will be used for a uniform polytope. -/
noncomputable def intrinsicRadius (P : Set E) : ℝ := by
  classical
  exact if h : ∃ r, HasIntrinsicRadius P r then h.choose else 0

theorem HasIntrinsicRadius.eq_intrinsicRadius {P : Set E} {r : ℝ}
    (hr : HasIntrinsicRadius P r) : r = intrinsicRadius P := by
  have he : ∃ s, HasIntrinsicRadius P s := ⟨r, hr⟩
  rw [intrinsicRadius, dif_pos he]
  exact hr.unique he.choose_spec

theorem uniform_hasIntrinsicRadius {n : ℕ} {P : Set E} (hP : Uniform (n + 3) P) :
    HasIntrinsicRadius P (intrinsicRadius P) := by
  obtain ⟨r, hr, hs⟩ := finitePolytope_transitive_cospherical
    (uniform_finitePolytope hP) (uniform_vertexTransitive hP)
  have hh : HasIntrinsicRadius P r := ⟨_, hr, hs⟩
  rwa [← hh.eq_intrinsicRadius]

theorem uniform_intrinsicRadius_pos {n : ℕ} {P : Set E} (hP : Uniform (n + 3) P) :
    0 < intrinsicRadius P := by
  obtain ⟨_, hr, hs⟩ := uniform_hasIntrinsicRadius hP
  exact uniform_sphere_radius_pos hP hr hs

/-- The literal geometric word-angle expression, before library labels or
ball enclosures are attached. -/
noncomputable def facetWordAngle (k : ℕ) (R rA rB : ℝ) : ℝ :=
  Real.arccos (Real.sqrt ((rA ^ 2 - (unitPolygonRadius k) ^ 2) /
    (R ^ 2 - (unitPolygonRadius k) ^ 2))) +
  Real.arccos (Real.sqrt ((rB ^ 2 - (unitPolygonRadius k) ^ 2) /
    (R ^ 2 - (unitPolygonRadius k) ^ 2)))

variable [FiniteDimensional ℝ E]

theorem unitUniform4_canonical_word_angle {P G A B : Set E} {k : ℕ}
    (hP : UnitUniform 4 P) (hG : PolygonFace P G k)
    (hA : Facet P A) (hB : Facet P B) (hGA : G ⊆ A) (hGB : G ⊆ B) (hAB : A ≠ B) :
    let hPP := uniform_finitePolytope hP.1
    let f := vertexCentroid (vertices G (finitePolytope_face hPP hG.1 (polygonFace_nonempty hG)))
    let a := vertexCentroid (vertices A (finitePolytope_facet hPP hA))
    let b := vertexCentroid (vertices B (finitePolytope_facet hPP hB))
    angle (a - f) (b - f) =
      facetWordAngle k (intrinsicRadius P) (intrinsicRadius A) (intrinsicRadius B) := by
  obtain ⟨R, rA, rB, hR, hrA, hrB, hsR, hsA, hsB, heq⟩ :=
    unitUniform4_word_angle hP hG hA hB hGA hGB hAB
  have hRP : HasIntrinsicRadius P R := ⟨_, hR.le, hsR⟩
  have hRA : HasIntrinsicRadius A rA := ⟨_, hrA.le, hsA⟩
  have hRB : HasIntrinsicRadius B rB := ⟨_, hrB.le, hsB⟩
  simpa only [facetWordAngle, hRP.eq_intrinsicRadius, hRA.eq_intrinsicRadius,
    hRB.eq_intrinsicRadius] using heq

/-- The height parameter of each actual incident three-cell is determined
by its intrinsic radius and the actual unit polygon radius. -/
theorem uniform_polygon_cell_offset {n k : ℕ} {P G C : Set E}
    (hP : UnitUniform (n + 3) P) (hG : PolygonFace P G k)
    (hC : IsConvexFace P C) (hGC : G ⊆ C) (hdC : affineDimension C = 3) :
    let hPP := uniform_finitePolytope hP.1
    let hGne := polygonFace_nonempty hG
    let f := vertexCentroid (vertices G (finitePolytope_face hPP hG.1 hGne))
    let a := vertexCentroid (vertices C (finitePolytope_face hPP hC (hGne.mono hGC)))
    ‖a - f‖ = Real.sqrt ((intrinsicRadius C) ^ 2 - (unitPolygonRadius k) ^ 2) := by
  dsimp only
  let hPP := uniform_finitePolytope hP.1
  have hGne := polygonFace_nonempty hG
  let hGP := finitePolytope_face hPP hG.1 hGne
  let hCP := finitePolytope_face hPP hC (hGne.mono hGC)
  let a := vertexCentroid (vertices C hCP)
  have hUC : Uniform 3 C := by
    have hh := uniform_face hP.1 hC (hGne.mono hGC) (by omega)
    rwa [hdC] at hh
  obtain ⟨_, _, hsC⟩ := uniform_hasIntrinsicRadius hUC
  have hsGC : ∀ x ∈ G.extremePoints ℝ, ‖x - a‖ ^ 2 = (intrinsicRadius C) ^ 2 :=
    fun x hx => hsC x ((face_restrict hG.1 hC.2.1 hGC).2.extremePoints_subset_extremePoints hx)
  obtain ⟨ρ, hρ, hsρ, _, _, _⟩ :=
    transitive_centroid_projection hGP (uniform_face_vertexTransitive hP.1 hG.1 hGne)
      a (intrinsicRadius C) hsGC
  have heq : ρ = unitPolygonRadius k := by
    apply polygonFace_intrinsic_radius hP hG
      (subset_affineSpan ℝ G (intrinsicInterior_subset (vertexCentroid_mem_intrinsicInterior hGP)))
    intro x hx
    rw [dist_eq_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) hρ).mp (hsρ x hx)
  rw [heq] at hsρ
  exact centroid_offset_of_spheres hGP (uniform_face_vertexTransitive hP.1 hG.1 hGne)
    a (intrinsicRadius C) (unitPolygonRadius k) hsGC hsρ

/-- Every actual polygon has a complete cycle of actual facet words. Its
coherent cell/facet radii satisfy the literal reciprocal-radius equation.
This is the geometric input to library matching, before any computed claim. -/
theorem unitUniform5_actual_word_cycle {P G : Set (Space 5)}
    (hP : UnitUniform 5 P) {k : ℕ} (hG : PolygonFace P G k) :
    ∃ n : ℕ, 3 ≤ n ∧ ∃ C : ℕ → Set (Space 5),
      (∀ i, IsConvexFace P (C i)) ∧ (∀ i, G ⊆ C i) ∧
      (∀ i, affineDimension (C i) = 3) ∧ C n = C 0 ∧ Set.InjOn C (Iio n) ∧
      (∀ F, IsConvexFace P F → G ⊆ F → affineDimension F = 3 → ∃ i < n, C i = F) ∧
      ∃ A : Fin n → Set (Space 5),
        (∀ i, Facet P (A i) ∧ G ⊆ A i ∧ C i ⊆ A i ∧ C (i.val + 1) ⊆ A i) ∧
        Function.Injective A ∧
        (∀ F, (Facet P F ∧ G ⊆ F) ↔ ∃ i, A i = F) ∧
        (∀ i : Fin n, ∀ F, (Facet P F ∧ C i ⊆ F) ↔
          F = A ((finRotate n).symm i) ∨ F = A i) ∧
        (∀ i : Fin n, ∃! F, Facet P F ∧ C i ⊆ F ∧ C (i.val + 1) ⊆ F) ∧
        0 < intrinsicRadius P ∧ (∀ i, 0 < intrinsicRadius (C i)) ∧
        (∀ i, 0 < intrinsicRadius (A i)) ∧
        cycleClosureFunction n (unitPolygonRadius k)
          (fun i => Real.sqrt ((intrinsicRadius (C i)) ^ 2 - (unitPolygonRadius k) ^ 2))
          (fun i => if hi : i < n then facetWordAngle k (intrinsicRadius (A ⟨i, hi⟩))
            (intrinsicRadius (C i)) (intrinsicRadius (C (i + 1))) else 0)
          (1 / intrinsicRadius P) = 0 := by
  classical
  obtain ⟨n, hn, C, hC, hGC, hdC, hcycle, hinj, hcov, hadj, hclose⟩ :=
    unitUniform5_polygon_closure hP hG
  obtain ⟨A, hA, hAinj, hAcov, hAtwo, hAunique⟩ :=
    ordered_cell_cycle_facet_cycle (uniform_finitePolytope hP.1) (uniform_dimension hP.1)
      hG.1 (polygonFace_nonempty hG) hG.2.1 hn C hC hGC hdC hcycle hinj hcov hadj
  have hUC (i : ℕ) : UnitUniform 3 (C i) := by
    have hh := unitUniform_face hP (hC i) ((polygonFace_nonempty hG).mono (hGC i))
      (by rw [hdC]; omega)
    rwa [hdC] at hh
  have hUA (i : Fin n) : UnitUniform 4 (A i) :=
    ⟨uniform_facets hP.1 (hA i).1,
      unitEdges_face (uniform_finitePolytope hP.1) (hA i).1.1 hP.2⟩
  refine ⟨n, hn, C, hC, hGC, hdC, hcycle, hinj, hcov, A, hA, hAinj, hAcov,
    hAtwo, hAunique, uniform_intrinsicRadius_pos hP.1,
    fun i => uniform_intrinsicRadius_pos (hUC i).1,
    fun i => uniform_intrinsicRadius_pos (hUA i).1, ?_⟩
  dsimp only at hclose
  obtain ⟨R, hR, hsR, hzero⟩ := hclose
  have hRP : HasIntrinsicRadius P R := ⟨_, hR.le, hsR⟩
  rw [hRP.eq_intrinsicRadius] at hzero
  let hPP := uniform_finitePolytope hP.1
  let hGne := polygonFace_nonempty hG
  let f := vertexCentroid (vertices G (finitePolytope_face hPP hG.1 hGne))
  let a := fun i => vertexCentroid (vertices (C i) (finitePolytope_face hPP (hC i) (hGne.mono (hGC i))))
  have hd : (fun i => ‖a i - f‖) =
      (fun i => Real.sqrt ((intrinsicRadius (C i)) ^ 2 - (unitPolygonRadius k) ^ 2)) := by
    funext i
    exact uniform_polygon_cell_offset hP hG (hC i) (hGC i) (hdC i)
  have hang (i : ℕ) (hi : i < n) : angle (a i - f) (a (i + 1) - f) =
      facetWordAngle k (intrinsicRadius (A ⟨i, hi⟩))
        (intrinsicRadius (C i)) (intrinsicRadius (C (i + 1))) := by
    let j : Fin n := ⟨i, hi⟩
    have hGj : PolygonFace (A j) G k :=
      ⟨face_restrict hG.1 (hA j).1.1.2.1 (hA j).2.1, hG.2⟩
    have hCA : Facet (A j) (C i) :=
      ⟨face_restrict (hC i) (hA j).1.1.2.1 (hA j).2.2.1,
        hGne.mono (hGC i), by rw [hdC, uniform_dimension (hUA j).1]⟩
    have hCB : Facet (A j) (C (i + 1)) :=
      ⟨face_restrict (hC (i + 1)) (hA j).1.1.2.1 (hA j).2.2.2,
        hGne.mono (hGC (i + 1)), by rw [hdC, uniform_dimension (hUA j).1]⟩
    exact unitUniform4_canonical_word_angle (hUA j) hGj hCA hCB (hGC i) (hGC (i + 1))
      (cell_cycle_consecutive_ne hn C hcycle hinj hi)
  change cycleClosureFunction n (unitPolygonRadius k) (fun i => ‖a i - f‖)
    (fun i => angle (a i - f) (a (i + 1) - f)) (1 / intrinsicRadius P) = 0 at hzero
  rw [hd] at hzero
  rw [← hzero]
  unfold cycleClosureFunction
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [dif_pos (Finset.mem_range.mp hi), hang i (Finset.mem_range.mp hi)]

end Uniform5.Composition
