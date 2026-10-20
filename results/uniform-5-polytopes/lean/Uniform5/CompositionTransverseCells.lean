import Uniform5.CompositionTransverseTangent
import Uniform5.CompositionPolarMetrics

/-! Actual cell-centroid rays in the ordered transverse tangent fan. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical InnerProductGeometry
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Positive-height normalization stays in every actual apex face. -/
theorem radialPoint_mem_apex_face {P F : Set E} (hP : FinitePolytope P)
    (hF : IsConvexFace P F) (hz : (0 : E) ∈ F) (L : E →L[ℝ] ℝ)
    (hh : ∀ x ∈ (vertices P hP).erase 0, 1 ≤ L x)
    {x : E} (hx : x ∈ F) (hpos : 0 < L x) : radialPoint L x ∈ F := by
  let V := vertices P hP
  let W := V.filter (fun x => x ∈ F)
  have hFh : IsConvexFace (convexHull ℝ (V : Set E)) F := by
    simpa only [V, convexHull_vertices] using hF
  have hFW : F = convexHull ℝ (W : Set E) := by
    simpa only [W, Finset.coe_filter] using face_convexHull_eq hFh
  have hWheight : ∀ z ∈ W.erase 0, 1 ≤ L z := by
    intro z hzW
    exact hh z (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hzW).1,
      (Finset.mem_filter.mp (Finset.mem_erase.mp hzW).2).1⟩)
  by_cases hzV : (0 : E) ∈ V
  · have hzW : (0 : E) ∈ W := Finset.mem_filter.mpr ⟨hzV, hz⟩
    have hr := finiteHull_radialPoint_mem_section W hzW L hWheight (hFW ▸ hx) hpos
    exact hFW.symm ▸ hr.1
  · have hzeroext : (0 : E) ∈ P.extremePoints ℝ := by
      have hnonneg := finiteHull_height_nonnegative_zero V L
        (fun z hz => lt_of_lt_of_le zero_lt_one (hh z hz))
      refine ⟨hF.2.1 hz, ?_⟩
      intro a ha b hb hs
      obtain ⟨s, t, hspos, htpos, hst, hcomb⟩ := hs
      have ha' := hnonneg a ((convexHull_vertices hP).symm ▸ ha)
      have hb' := hnonneg b ((convexHull_vertices hP).symm ▸ hb)
      have heq := congrArg L hcomb
      simp only [map_add, map_smul, smul_eq_mul, map_zero] at heq
      exact ⟨ha'.2 (by nlinarith), hb'.2 (by nlinarith)⟩
    exact False.elim (hzV ((mem_vertices hP 0).mpr hzeroext))

noncomputable local instance (G : Set E) : DecidableEq (affineSpan ℝ G).directionᗮ := Classical.decEq _

/-- The actual centroid of every proper incident face projects to a
nonzero vector of strictly positive cutting height. -/
theorem transverse_face_centroid_height_pos {P G C : Set E} (hP : FinitePolytope P)
    (hG : IsConvexFace P G) {c : E} (hc : c ∈ G)
    (hC : IsConvexFace P C) (hGC : G ⊆ C) (hne : G ≠ C) :
    let hCP := finitePolytope_face hP hC ⟨c, hGC hc⟩
    0 < transverseCutHeight hP hG hc
      (transverseProjection G c (vertexCentroid (vertices C hCP))) := by
  dsimp only
  let hCP := finitePolytope_face hP hC ⟨c, hGC hc⟩
  let a := vertexCentroid (vertices C hCP)
  let Q := transverseProjection G c '' P
  let hQ := finitePolytope_transverse hP G c
  have ha : a ∈ C := intrinsicInterior_subset (vertexCentroid_mem_intrinsicInterior hCP)
  have hane : transverseProjection G c a ≠ 0 := by
    intro hz
    exact centroid_not_mem_proper_face_span hCP (face_restrict hG hC.2.1 hGC)
      ⟨c, hc⟩ hne ((transverseProjection_zero_iff G hc a).mp hz)
  have hh := finiteHull_height_nonnegative_zero (vertices Q hQ)
    (transverseCutHeight hP hG hc)
    (fun x hx => lt_of_lt_of_le zero_lt_one (transverseCutHeight_ge_one hP hG hc x hx))
    (transverseProjection G c a) (by
      rw [convexHull_vertices]
      exact ⟨a, hC.2.1 ha, rfl⟩)
  exact lt_of_le_of_ne hh.1 (fun heq => hane (hh.2 heq.symm))

/-- A three-cell centroid points along its unique actual link vertex,
with a derived strictly positive scale. -/
theorem transverse_cell_centroid_ray {P G C : Set E} (hP : FinitePolytope P)
    (hG : IsConvexFace P G) (hdG : affineDimension G = 2) {c : E} (hc : c ∈ G)
    (hC : IsConvexFace P C) (hGC : G ⊆ C) (hdC : affineDimension C = 3)
    {v : (affineSpan ℝ G).directionᗮ}
    (hsection : transverseProjection G c '' C ∩ transverseLink hP hG hc = {v}) :
    let hCP := finitePolytope_face hP hC ⟨c, hGC hc⟩
    let a := vertexCentroid (vertices C hCP)
    let r := transverseCutHeight hP hG hc (transverseProjection G c a)
    0 < r ∧ transverseProjection G c a = r • v := by
  dsimp only
  let hCP := finitePolytope_face hP hC ⟨c, hGC hc⟩
  let a := vertexCentroid (vertices C hCP)
  let x := transverseProjection G c a
  let L := transverseCutHeight hP hG hc
  let Q := transverseProjection G c '' P
  let hQ := finitePolytope_transverse hP G c
  have hne : G ≠ C := by intro h; have hd := congrArg affineDimension h; omega
  have hp : 0 < L x := transverse_face_centroid_height_pos hP hG hc hC hGC hne
  have ha : a ∈ C := intrinsicInterior_subset (vertexCentroid_mem_intrinsicInterior hCP)
  have hx : x ∈ transverseProjection G c '' C := ⟨a, ha, rfl⟩
  have hrF := radialPoint_mem_apex_face hQ (transverse_face_image hP hC hGC hc)
    (show (0 : (affineSpan ℝ G).directionᗮ) ∈ transverseProjection G c '' C from
      ⟨c, hGC hc, transverseProjection_center G c⟩) L
    (transverseCutHeight_ge_one hP hG hc) hx hp
  have hrS : radialPoint L x ∈ transverseLink hP hG hc := by
    have hr := finiteHull_radialPoint_mem_section (vertices Q hQ)
      ((mem_vertices hQ 0).mpr (transverse_origin_extreme hP hG hc)) L
      (transverseCutHeight_ge_one hP hG hc) (by
        rw [convexHull_vertices]
        exact ⟨a, hC.2.1 ha, rfl⟩) hp
    simpa only [convexHull_vertices] using hr
  have hr : radialPoint L x = v := by
    have hm : radialPoint L x ∈ transverseProjection G c '' C ∩ transverseLink hP hG hc := ⟨hrF, hrS⟩
    rw [hsection] at hm
    exact hm
  refine ⟨hp, ?_⟩
  change x = L x • v
  rw [← hr]
  simp only [radialPoint, smul_smul, mul_inv_cancel₀ hp.ne', one_smul]

set_option maxHeartbeats 600000 in
/-- The ordered tangent polygon lifts to actual three-cells. Its fan is
expressed in normalized projected actual centroid rays, ready for ambient
isometric transport. All cells, including indices beyond one period, are real. -/
theorem unitUniform5_projected_cell_centroid_fan {P G : Set (Space 5)}
    (hP : UnitUniform 5 P) {k : ℕ} (hG : PolygonFace P G k) {c : Space 5} (hc : c ∈ G) :
    let hPP := uniform_finitePolytope hP.1
    let y := transverseProjection G c (vertexCentroid (vertices P hPP))
    ∃ n : ℕ, 0 < n ∧ ∃ C : ℕ → Set (Space 5),
    ∃ hC : ∀ i, IsConvexFace P (C i), ∃ hGC : ∀ i, G ⊆ C i,
      (∀ i, affineDimension (C i) = 3) ∧ C n = C 0 ∧
      Set.InjOn C (Iio n) ∧
      (∀ F, IsConvexFace P F → G ⊆ F → affineDimension F = 3 → ∃ i < n, C i = F) ∧
      (∀ i < n, ∃ F, Facet P F ∧ G ⊆ F ∧ C i ⊆ F ∧ C (i + 1) ⊆ F) ∧
      Nonempty (SphericalFanData n (fun i =>
        let a := fun j => transverseProjection G c (vertexCentroid
          (vertices (C j) (finitePolytope_face hPP (hC j) ⟨c, hGC j hc⟩)))
        angle (sphericalTangent (‖y‖⁻¹ • y) (‖a i‖⁻¹ • a i))
          (sphericalTangent (‖y‖⁻¹ • y) (‖a (i + 1)‖⁻¹ • a (i + 1))))) := by
  dsimp only
  let hPP := uniform_finitePolytope hP.1
  let H := (affineSpan ℝ G).directionᗮ
  let y := transverseProjection G c (vertexCentroid (vertices P hPP))
  let L := transverseCutHeight hPP hG.1 hc
  let S := transverseLink hPP hG.1 hc
  have hS : FinitePolytope S := (unitUniform5_transverseLink hP hG hc).1
  have hheight (z : H) (hz : z ∈ S) : L z = 1 := hz.2
  have hproper : affineDimension G < affineDimension P := by
    rw [hG.2.1, uniform_dimension hP.1]
    norm_num
  have hy : L y ≠ 0 := (transverseCentroidPole_mem_intrinsicInterior hPP
    (uniform_affineSpan_eq_top hP.1) hG.1 hc hproper).1.ne'
  obtain ⟨n, u, hrange, hinj, hcycle, hne, hedge, ⟨fan⟩⟩ :=
    unitUniform5_transverse_tangent_fan hP hG hc
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    have hw := fan.winding
    have hh := congrArg fan.lift hn0
    nlinarith [Real.pi_pos]
  have hu (i : Fin n) : u i ∈ (axialProjection y '' S).extremePoints ℝ := by
    rw [← hrange]
    exact ⟨i, i.isLt, rfl⟩
  have hvex (i : Fin n) : ∃ v ∈ S.extremePoints ℝ, axialProjection y v = u i := by
    obtain ⟨v, hvS, heq⟩ := (hu i).1
    refine ⟨v, ?_, heq⟩
    apply (axialProjection_extreme_iff (finitePolytope_convex hS) L hheight hy hvS).mp
    exact heq.symm ▸ hu i
  let v : Fin n → H := fun i => (hvex i).choose
  have hv (i : Fin n) : v i ∈ S.extremePoints ℝ ∧ axialProjection y (v i) = u i :=
    (hvex i).choose_spec
  have hcex (i : Fin n) : ∃! F : Set (Space 5), IsConvexFace P F ∧ G ⊆ F ∧
      affineDimension F = 3 ∧ transverseProjection G c '' F ∩ S = {v i} :=
    transverseLink_vertex_unique_cell hPP hG.1 hG.2.1 hc (hv i).1
  let D : Fin n → Set (Space 5) := fun i => (hcex i).exists.choose
  have hD (i : Fin n) : IsConvexFace P (D i) ∧ G ⊆ D i ∧ affineDimension (D i) = 3 ∧
      transverseProjection G c '' D i ∩ S = {v i} := (hcex i).exists.choose_spec
  let idx (i : ℕ) : Fin n := ⟨i % n, Nat.mod_lt i hn⟩
  let C : ℕ → Set (Space 5) := fun i => D (idx i)
  have hC (i : ℕ) : IsConvexFace P (C i) := (hD (idx i)).1
  have hGC (i : ℕ) : G ⊆ C i := (hD (idx i)).2.1
  have hdC (i : ℕ) : affineDimension (C i) = 3 := (hD (idx i)).2.2.1
  have hCn : C n = C 0 := by simp only [C, idx, Nat.mod_self, Nat.zero_mod]
  let a (i : ℕ) : H := transverseProjection G c (vertexCentroid
    (vertices (C i) (finitePolytope_face hPP (hC i) ⟨c, hGC i hc⟩)))
  have haray (i : ℕ) : 0 < L (a i) ∧ a i = L (a i) • v (idx i) :=
    transverse_cell_centroid_ray hPP hG.1 hG.2.1 hc (hC i) (hGC i) (hdC i)
      (hD (idx i)).2.2.2
  have huwrap (i : ℕ) (hi : i ≤ n) : u (idx i) = u i := by
    by_cases hlt : i < n
    · simp only [idx, Nat.mod_eq_of_lt hlt]
    · have heq : i = n := by omega
      subst i
      simpa only [idx, Nat.mod_self] using hcycle.symm
  have htangent (i : ℕ) (hi : i ≤ n) :
      sphericalTangent (‖y‖⁻¹ • y) (‖a i‖⁻¹ • a i) =
        (‖a i‖⁻¹ * L (a i)) • (u i : H) := by
    rw [sphericalTangent_normalized_eq_axialProjection]
    have hproj : axialProjection y (a i) = L (a i) • u i := by
      conv_lhs => rw [(haray i).2]
      rw [map_smul, (hv (idx i)).2, huwrap i hi]
    rw [hproj]
    simp only [Submodule.coe_smul, smul_smul]
  have hscale (i : ℕ) : 0 < ‖a i‖⁻¹ * L (a i) := by
    have ha0 : a i ≠ 0 := by
      intro h
      have hh := (haray i).1
      rw [h, map_zero] at hh
      exact lt_irrefl _ hh
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr ha0)) (haray i).1
  have hang (i : ℕ) (hi : i < n) :
      angle (sphericalTangent (‖y‖⁻¹ • y) (‖a i‖⁻¹ • a i))
        (sphericalTangent (‖y‖⁻¹ • y) (‖a (i + 1)‖⁻¹ • a (i + 1))) =
      angle (u i) (u (i + 1)) := by
    rw [htangent i (by omega), htangent (i + 1) (by omega),
      angle_smul_left_of_pos _ _ (hscale i), angle_smul_right_of_pos _ _ (hscale (i + 1))]
    exact (ℝ ∙ y)ᗮ.subtypeₗᵢ.angle_map _ _
  have hCinj : Set.InjOn C (Iio n) := by
    intro i hi j hj hCeq
    have hs := (hD (idx i)).2.2.2
    change transverseProjection G c '' C i ∩ S = {v (idx i)} at hs
    rw [hCeq, (hD (idx j)).2.2.2] at hs
    have hvEq : v (idx i) = v (idx j) := (singleton_injective hs).symm
    have huEq := congrArg (axialProjection y) hvEq
    rw [(hv (idx i)).2, (hv (idx j)).2, huwrap i hi.le, huwrap j hj.le] at huEq
    exact hinj hi hj huEq
  have hcoverage : ∀ F, IsConvexFace P F → G ⊆ F → affineDimension F = 3 →
      ∃ i < n, C i = F := by
    intro F hF hGF hdF
    obtain ⟨z, hz, hsection⟩ := transverseLink_cell_vertex hPP hG.1 hG.2.1 hc hF hGF hdF
    have hzT : axialProjection y z ∈ (axialProjection y '' S).extremePoints ℝ :=
      (axialProjection_extreme_iff (finitePolytope_convex hS) L hheight hy hz.1).mpr hz
    rw [← hrange] at hzT
    obtain ⟨i, hi, hiu⟩ := hzT
    have hvz : v (idx i) = z :=
      axialProjection_injOn_level y L hy (hheight _ (hv (idx i)).1.1) (hheight z hz.1)
        (by rw [(hv (idx i)).2, huwrap i hi.le]; exact hiu)
    refine ⟨i, hi, ?_⟩
    obtain ⟨F₀, hF₀, huniq⟩ := hcex (idx i)
    exact (huniq _ (hD (idx i))).trans (huniq F
      ⟨hF, hGF, hdF, by simpa only [hvz] using hsection⟩).symm
  have hadjacent : ∀ i < n, ∃ F, Facet P F ∧ G ⊆ F ∧ C i ⊆ F ∧ C (i + 1) ⊆ F := by
    intro i hi
    have he : Edge S (v (idx i)) (v (idx (i + 1))) := by
      apply (axialProjection_edge_iff hS L hheight hy (hv (idx i)).1.1
        (hv (idx (i + 1))).1.1).mp
      rw [(hv (idx i)).2, (hv (idx (i + 1))).2, huwrap i (by omega),
        huwrap (i + 1) (by omega)]
      exact hedge i hi
    obtain ⟨F, ⟨hF, hGF, hFsection⟩, _⟩ := transverseLink_edge_unique_facet hPP
      (uniform_dimension hP.1) hG.1 hG.2.1 hc he
    have hsubset (j : ℕ) (hmem : v (idx j) ∈ segment ℝ (v (idx i)) (v (idx (i + 1)))) : C j ⊆ F := by
      let e := transverseLinkFaceEquiv hPP hG.1 hc
      let C' : {H : GeometricFace P // G ⊆ H.val} := ⟨⟨C j, hC j⟩, hGC j⟩
      let F' : {H : GeometricFace P // G ⊆ H.val} := ⟨⟨F, hF.1⟩, hGF⟩
      have hle : e C' ≤ e F' := by
        change (transverseLinkFaceEquiv hPP hG.1 hc C').val ⊆
          (transverseLinkFaceEquiv hPP hG.1 hc F').val
        rw [transverseLinkFaceEquiv_apply, transverseLinkFaceEquiv_apply]
        change transverseProjection G c '' C j ∩ S ⊆ transverseProjection G c '' F ∩ S
        rw [(hD (idx j)).2.2.2, hFsection]
        exact singleton_subset_iff.mpr hmem
      exact e.le_iff_le.mp hle
    exact ⟨F, hF, hGF, hsubset i (left_mem_segment ℝ _ _),
      hsubset (i + 1) (right_mem_segment ℝ _ _)⟩
  refine ⟨n, hn, C, hC, hGC, hdC, hCn, hCinj, hcoverage, hadjacent,
    ⟨{ fan with gap := ?_ }⟩⟩
  intro i hi
  exact (hang i hi).trans (fan.gap i hi)

end Uniform5.Composition
