import Uniform5.CompositionCycleWords
import Uniform5.CompositionRadiusTransport

/-! The geometric domain of the closure formula, before interval evaluation. -/
noncomputable section
namespace Uniform5.Composition
open Set InnerProductGeometry

noncomputable def closureArgument (ρ a b α s : ℝ) : ℝ :=
  (Real.cos α - cyclePolarCosine ρ a s * cyclePolarCosine ρ b s) /
    (Real.sqrt (1 - cyclePolarCosine ρ a s ^ 2) *
      Real.sqrt (1 - cyclePolarCosine ρ b s ^ 2))

/-- Total real functions in Lean are restricted to the paper's geometric
triangle domain. Its polar denominators are positive and its inverse-cosine
arguments are in their intended range. -/
def ClosureDomain (n : ℕ) (ρ : ℝ) (d α : ℕ → ℝ) (s : ℝ) : Prop :=
  0 < 1 - ρ ^ 2 * s ^ 2 ∧
    (∀ i ≤ n, 0 < Real.sqrt (1 - cyclePolarCosine ρ (d i) s ^ 2)) ∧
    ∀ i < n, closureArgument ρ (d i) (d (i + 1)) (α i) s ∈ Icc (-1) 1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual unit rays with nonzero tangents force the geometric domain.
No once-around or closure-equation assumption is needed for this fact. -/
theorem closureDomain_of_unit_rays {n : ℕ} {w : E} {u : ℕ → E}
    {ρ R h : ℝ} {d α : ℕ → ℝ}
    (hw : ‖w‖ = 1) (hu : ∀ i ≤ n, ‖u i‖ = 1)
    (ht : ∀ i ≤ n, sphericalTangent w (u i) ≠ 0)
    (hR : 0 < R) (hh : 0 < h) (hsq : h ^ 2 = R ^ 2 - ρ ^ 2)
    (hpolar : ∀ i ≤ n, Real.cos (angle (u i) w) = d i / h)
    (hangle : ∀ i < n, α i = angle (u i) (u (i + 1))) :
    ClosureDomain n ρ d α (1 / R) := by
  have hcos (i : ℕ) (hi : i ≤ n) :
      cyclePolarCosine ρ (d i) (1 / R) = Real.cos (angle (u i) w) := by
    rw [cyclePolarCosine_at_radius hR hh hsq, hpolar i hi]
  have hsin (i : ℕ) (hi : i ≤ n) :
      Real.sqrt (1 - cyclePolarCosine ρ (d i) (1 / R) ^ 2) =
        Real.sin (angle (u i) w) := by
    rw [hcos i hi]
    exact (Real.sin_eq_sqrt_one_sub_cos_sq (angle_nonneg _ _) (angle_le_pi _ _)).symm
  refine ⟨?_, ?_, ?_⟩
  · have heq : 1 - ρ ^ 2 * (1 / R) ^ 2 = h ^ 2 / R ^ 2 := by
      rw [hsq]
      field_simp
    rw [heq]
    exact div_pos (sq_pos_of_pos hh) (sq_pos_of_pos hR)
  · intro i hi
    rw [hsin i hi, ← sphericalTangent_norm hw (hu i hi)]
    exact norm_pos_iff.mpr (ht i hi)
  · intro i hi
    unfold closureArgument
    rw [hsin i (by omega), hsin (i + 1) (by omega), hcos i (by omega),
      hcos (i + 1) (by omega), hangle i hi,
      ← spherical_cosine_law hw (hu i (by omega)) (hu (i + 1) (by omega))]
    exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

variable [FiniteDimensional ℝ E]

/-- Every actual sequence of proper incident face rays lies in the
geometric closure domain at the parent's actual reciprocal radius. -/
theorem actual_center_cycle_domain {m k n : ℕ} {P G : Set E}
    (hP : UnitUniform (m + 3) P) (hG : PolygonFace P G k)
    (C : ℕ → Set E) (hC : ∀ i, IsConvexFace P (C i))
    (hGC : ∀ i, G ⊆ C i) (hproper : ∀ i, G ≠ C i)
    (hCproper : ∀ i, C i ≠ P) :
    let hPP := uniform_finitePolytope hP.1
    let hGne := polygonFace_nonempty hG
    let f := vertexCentroid (vertices G (finitePolytope_face hPP hG.1 hGne))
    let a := fun i => vertexCentroid (vertices (C i)
      (finitePolytope_face hPP (hC i) (hGne.mono (hGC i))))
    ClosureDomain n (unitPolygonRadius k) (fun i => ‖a i - f‖)
      (fun i => angle (a i - f) (a (i + 1) - f)) (1 / intrinsicRadius P) := by
  dsimp only
  let hPP := uniform_finitePolytope hP.1
  let hGne := polygonFace_nonempty hG
  let hGP := finitePolytope_face hPP hG.1 hGne
  let hCP := fun i => finitePolytope_face hPP (hC i) (hGne.mono (hGC i))
  let o := vertexCentroid (vertices P hPP)
  let f := vertexCentroid (vertices G hGP)
  let a := fun i => vertexCentroid (vertices (C i) (hCP i))
  let w := ‖o - f‖⁻¹ • (o - f)
  let u := fun i => ‖a i - f‖⁻¹ • (a i - f)
  have hm (i : ℕ) := uniform_nested_face_polar_cosine hP.1 (hC i) hG.1 hGne
    (hGC i) (hproper i)
  have hap (i : ℕ) : 0 < ‖a i - f‖ := (hm i).2.1
  have hop : 0 < ‖o - f‖ := (hm 0).2.2.1
  obtain ⟨_, hR, hsR⟩ := uniform_hasIntrinsicRadius hP.1
  have hRp := uniform_intrinsicRadius_pos hP.1
  obtain ⟨ρ, hρ, hsρ, _, _, hoff⟩ :=
    uniform_face_center_projection hP.1 hG.1 hGne o (intrinsicRadius P) hsR
  have hρeq : ρ = unitPolygonRadius k := by
    apply polygonFace_intrinsic_radius hP hG
      (subset_affineSpan ℝ G (intrinsicInterior_subset (vertexCentroid_mem_intrinsicInterior hGP)))
    intro x hx
    rw [dist_eq_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) hρ).mp (hsρ x hx)
  have hnorm : ‖o - f‖ = Real.sqrt ((intrinsicRadius P) ^ 2 - (unitPolygonRadius k) ^ 2) := by
    simpa only [dist_eq_norm, hρeq] using hoff
  have hsq : ‖o - f‖ ^ 2 = (intrinsicRadius P) ^ 2 - (unitPolygonRadius k) ^ 2 := by
    rw [hnorm]
    exact Real.sq_sqrt (Real.sqrt_pos.mp (hnorm ▸ hop)).le
  have huw (i : ℕ) : ‖u i‖ = 1 := normalized_center_unit rfl (hap i)
  have hww : ‖w‖ = 1 := normalized_center_unit rfl hop
  have ht (i : ℕ) : sphericalTangent w (u i) ≠ 0 :=
    uniform_nested_face_tangent_ne_zero hP.1 (hC i) (hCproper i) hG.1 hGne
      (hGC i) (hproper i)
  have hp (i : ℕ) : Real.cos (angle (u i) w) = ‖a i - f‖ / ‖o - f‖ := by
    dsimp only [u, w]
    rw [angle_smul_left_of_pos _ _ (inv_pos.mpr (hap i)),
      angle_smul_right_of_pos _ _ (inv_pos.mpr hop)]
    exact (hm i).2.2.2
  have hangle (i : ℕ) : angle (a i - f) (a (i + 1) - f) = angle (u i) (u (i + 1)) := by
    dsimp only [u]
    rw [angle_smul_left_of_pos _ _ (inv_pos.mpr (hap i)),
      angle_smul_right_of_pos _ _ (inv_pos.mpr (hap (i + 1)))]
  exact closureDomain_of_unit_rays hww (fun i _ => huw i) (fun i _ => ht i)
    hRp hop hsq (fun i _ => hp i) (fun i _ => hangle i)

end Uniform5.Composition
