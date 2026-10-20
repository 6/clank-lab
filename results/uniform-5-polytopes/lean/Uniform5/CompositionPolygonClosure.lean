import Uniform5.CompositionActualClosure
import Uniform5.CompositionSubspaceAngles
import Uniform5.CompositionTransverseCells

/-! The closure equation for an actual polygon of an actual uniform
five-polytope. The fan and its metric identities are constructed. -/
noncomputable section
namespace Uniform5.Composition
open Set InnerProductGeometry

/-- An actual two-dimensional polygon face is nonempty. -/
theorem polygonFace_nonempty {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {P G : Set E} {k : ℕ} (hG : PolygonFace P G k) : G.Nonempty := by
  by_contra hn
  have he : G = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
  have hd := hG.2.1
  change affineDimension G = 2 at hd
  rw [he] at hd
  unfold affineDimension Uniform5.affineDimension at hd
  rw [AffineSubspace.span_empty, AffineSubspace.direction_bot, finrank_bot] at hd
  norm_num at hd

/-- Strict gaps below pi and one full turn require at least three rays. -/
theorem sphericalFanData_three_le {n : ℕ} {θ : ℕ → ℝ} (fan : SphericalFanData n θ) :
    3 ≤ n := by
  by_contra hn
  have hn' : n ≤ 2 := by omega
  interval_cases n
  · have h := fan.winding
    nlinarith [Real.pi_pos]
  · have h := fan.winding
    have hg := fan.gap_lt_pi 0 (by decide)
    norm_num at hg
    linarith [Real.pi_pos]
  · have h := fan.winding
    have hg0 := fan.gap_lt_pi 0 (by decide)
    have hg1 := fan.gap_lt_pi 1 (by decide)
    norm_num at hg0 hg1
    linarith

/-- Every polygon has an actual cyclic enumeration of all incident
three-cells, consecutive actual facet incidence, and a zero of its literal
closure function at the reciprocal of the actual positive circumradius. -/
theorem unitUniform5_polygon_closure {P G : Set (Space 5)}
    (hP : UnitUniform 5 P) {k : ℕ} (hG : PolygonFace P G k) :
    ∃ n : ℕ, 3 ≤ n ∧ ∃ C : ℕ → Set (Space 5),
    ∃ hC : ∀ i, IsConvexFace P (C i), ∃ hGC : ∀ i, G ⊆ C i,
      (∀ i, affineDimension (C i) = 3) ∧ C n = C 0 ∧
      Set.InjOn C (Iio n) ∧
      (∀ F, IsConvexFace P F → G ⊆ F → affineDimension F = 3 → ∃ i < n, C i = F) ∧
      (∀ i < n, ∃ F, Facet P F ∧ G ⊆ F ∧ C i ⊆ F ∧ C (i + 1) ⊆ F) ∧
      let hPP := uniform_finitePolytope hP.1
      let hGne := polygonFace_nonempty hG
      let o := vertexCentroid (vertices P hPP)
      let f := vertexCentroid (vertices G (finitePolytope_face hPP hG.1 hGne))
      let a := fun i => vertexCentroid (vertices (C i)
        (finitePolytope_face hPP (hC i) (hGne.mono (hGC i))))
      ∃ R : ℝ, 0 < R ∧ (∀ x ∈ P.extremePoints ℝ, ‖x - o‖ ^ 2 = R ^ 2) ∧
        cycleClosureFunction n (unitPolygonRadius k) (fun i => ‖a i - f‖)
          (fun i => angle (a i - f) (a (i + 1) - f)) (1 / R) = 0 := by
  let hPP := uniform_finitePolytope hP.1
  have hGne := polygonFace_nonempty hG
  let hGP := finitePolytope_face hPP hG.1 hGne
  let f := vertexCentroid (vertices G hGP)
  have hf : f ∈ G := intrinsicInterior_subset (vertexCentroid_mem_intrinsicInterior hGP)
  obtain ⟨n, hn, C, hC, hGC, hdim, hcyc, hinj, hcov, hfac, ⟨fan⟩⟩ :=
    unitUniform5_projected_cell_centroid_fan hP hG hf
  have hproper (i : ℕ) : G ≠ C i := by
    intro heq
    have hd := hdim i
    rw [← heq, hG.2.1] at hd
    norm_num at hd
  have hCproper (i : ℕ) : C i ≠ P := by
    intro heq
    have hd := hdim i
    rw [heq, uniform_dimension hP.1] at hd
    norm_num at hd
  refine ⟨n, sphericalFanData_three_le fan, C, hC, hGC, hdim, hcyc, hinj, hcov, hfac, ?_⟩
  apply actual_center_cycle_closure hP hG hGne hn C hC hGC hproper hCproper hcyc
  let o := vertexCentroid (vertices P hPP)
  let a := fun i => vertexCentroid (vertices (C i)
    (finitePolytope_face hPP (hC i) (hGne.mono (hGC i))))
  have horth (i : ℕ) := uniform_nested_face_rays_mem_orthogonal
    hP.1 (hC i) hG.1 hGne (hGC i)
  have hangle (i : ℕ) := transverse_normalized_tangent_angle G f o (a i) (a (i + 1))
    (horth i).1 (horth i).2 (horth (i + 1)).2
  convert fan using 1
  funext i
  exact (hangle i).symm

end Uniform5.Composition
