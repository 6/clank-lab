import Uniform5.CompositionFacetNormals
import Uniform5.CompositionRelativeFaces
import Uniform5.Tangent

/-!
# Actual ridge projections and strict opposite tangent feet

Orthogonal projection to the complement of the ridge directions produces
an actual two-dimensional plane. Strict cross-support of the two facet
centres forces their tangent feet onto opposite sides; no wedge or side
condition is postulated.
-/
noncomputable section
namespace Uniform5.Composition
open Set Classical
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Strict cross-support forces opposite signs in any orthonormal frame
whose first axis points from the sphere centre to the projected ridge. -/
theorem tangent_cross_support_opposite {u v a b : E} {r : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner u v = (0 : ℝ))
    (hr : 0 < r) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : a ∈ Submodule.span ℝ ({u, v} : Set E))
    (hb : b ∈ Submodule.span ℝ ({u, v} : Set E))
    (hta : inner (r • u - a) a = (0 : ℝ))
    (htb : inner (r • u - b) b = (0 : ℝ))
    (hab : (inner a b : ℝ) < inner a a) (hba : (inner a b : ℝ) < inner b b) :
    inner v a * inner v b < (0 : ℝ) := by
  obtain ⟨x, y, hxy⟩ := Submodule.mem_span_pair.mp ha
  obtain ⟨x', y', hxy'⟩ := Submodule.mem_span_pair.mp hb
  have hc := orthonormal_pair_coordinates hu hv huv x y
  have hc' := orthonormal_pair_coordinates hu hv huv x' y'
  rw [hxy] at hc
  rw [hxy'] at hc'
  have haa : inner a a = x ^ 2 + y ^ 2 := by
    rw [real_inner_self_eq_norm_sq, hc.2.2]
  have hbb : inner b b = x' ^ 2 + y' ^ 2 := by
    rw [real_inner_self_eq_norm_sq, hc'.2.2]
  have hd : inner a b = x * x' + y * y' := by
    rw [← hxy, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      hc'.1, hc'.2.1]
  have hta' : r * x = x ^ 2 + y ^ 2 := by
    rw [inner_sub_left, real_inner_smul_left, hc.1, haa] at hta
    linarith
  have htb' : r * x' = x' ^ 2 + y' ^ 2 := by
    rw [inner_sub_left, real_inner_smul_left, hc'.1, hbb] at htb
    linarith
  have hx : 0 < x := by
    have hh := real_inner_self_pos.mpr ha0
    rw [haa, ← hta'] at hh
    exact (mul_pos_iff_of_pos_left hr).mp hh
  have hx' : 0 < x' := by
    have hh := real_inner_self_pos.mpr hb0
    rw [hbb, ← htb'] at hh
    exact (mul_pos_iff_of_pos_left hr).mp hh
  rw [hd, haa] at hab
  rw [hd, hbb] at hba
  have h1 := mul_lt_mul_of_pos_right hab hx'
  have h2 := mul_lt_mul_of_pos_right hba hx
  have hd1 : y' * (x' * y - x * y') < 0 := by nlinarith [hta', htb']
  have hd2 : 0 < y * (x' * y - x * y') := by nlinarith [hta', htb']
  rw [hc.2.1, hc'.2.1]
  rcases lt_trichotomy (x' * y - x * y') 0 with hneg | hz | hpos
  · have hy : y < 0 := (mul_pos_iff.mp hd2).resolve_left (by rintro ⟨_, h⟩; linarith) |>.1
    have hy' : 0 < y' := (mul_neg_iff.mp hd1).resolve_right (by rintro ⟨_, h⟩; linarith) |>.1
    exact mul_neg_of_neg_of_pos hy hy'
  · rw [hz, mul_zero] at hd2
    exact (lt_irrefl _ hd2).elim
  · have hy : 0 < y := (mul_pos_iff.mp hd2).resolve_right (by rintro ⟨_, h⟩; linarith) |>.1
    have hy' : y' < 0 := (mul_neg_iff.mp hd1).resolve_left (by rintro ⟨_, h⟩; linarith) |>.1
    exact mul_neg_of_pos_of_neg hy hy'

variable [FiniteDimensional ℝ E]

/-- The orthogonal projection belongs to the actual affine span. -/
theorem spanProjection_mem (S : Set E) (hne : S.Nonempty) (c : E) :
    spanProjection S hne c ∈ affineSpan ℝ S := by
  letI : Nonempty (affineSpan ℝ S) :=
    ⟨⟨hne.choose, subset_affineSpan ℝ S hne.choose_spec⟩⟩
  exact EuclideanGeometry.orthogonalProjection_mem c

/-- The displacement to the projection is perpendicular to the face directions. -/
theorem spanProjection_sub_mem_orthogonal (S : Set E) (hne : S.Nonempty) (c : E) :
    spanProjection S hne c - c ∈ (affineSpan ℝ S).directionᗮ := by
  letI : Nonempty (affineSpan ℝ S) :=
    ⟨⟨hne.choose, subset_affineSpan ℝ S hne.choose_spec⟩⟩
  exact EuclideanGeometry.orthogonalProjection_vsub_mem_direction_orthogonal
    (affineSpan ℝ S) c

/-- For a full-dimensional polytope a genuine ridge has a genuinely
two-dimensional orthogonal complement. -/
theorem ridge_orthogonal_finrank {P R : Set E}
    (hfull : affineDimension P = Module.finrank ℝ E)
    (hrank : affineDimension R + 2 = affineDimension P) :
    Module.finrank ℝ (affineSpan ℝ R).directionᗮ = 2 := by
  have h := (affineSpan ℝ R).direction.finrank_add_finrank_orthogonal
  unfold affineDimension Uniform5.affineDimension at hfull hrank
  omega

/-- Every facet projection lies in the orthogonal ridge plane. -/
theorem spanProjection_mem_ridge_orthogonal {F R : Set E}
    (hne : F.Nonempty) (hRF : R ⊆ F) :
    spanProjection F hne (0 : E) ∈ (affineSpan ℝ R).directionᗮ := by
  have h := spanProjection_sub_mem_orthogonal F hne (0 : E)
  simp only [sub_zero] at h
  exact Submodule.orthogonal_le (AffineSubspace.direction_le (affineSpan_mono ℝ hRF)) h

/-- Projecting the ridge and a containing facet gives the tangent identity. -/
theorem spanProjection_ridge_tangent {F R : Set E}
    (hFne : F.Nonempty) (hRne : R.Nonempty) (hRF : R ⊆ F) :
    inner (spanProjection R hRne (0 : E) - spanProjection F hFne 0)
      (spanProjection F hFne 0) = (0 : ℝ) := by
  have hp := (affineSpan_mono ℝ hRF) (spanProjection_mem R hRne (0 : E))
  have ha := spanProjection_mem F hFne (0 : E)
  have hdir := (affineSpan ℝ F).vsub_mem_direction hp ha
  have horth := spanProjection_sub_mem_orthogonal F hFne (0 : E)
  simp only [sub_zero] at horth
  exact ((Submodule.mem_orthogonal _ _).mp horth) _ hdir

/-- Actual projection geometry of two distinct facets incident to a
ridge. The only centre assumptions are membership in the parent's relative
interior and relative interior membership of the actual projection feet. -/
theorem finitePolytope_ridge_projection {P F G R : Set E}
    (hP : FinitePolytope P) (hF : Facet P F) (hG : Facet P G) (hFG : F ≠ G)
    (hRne : R.Nonempty) (hRF : R ⊆ F) (hRG : R ⊆ G)
    (hrank : affineDimension R + 2 = affineDimension P)
    (hfull : affineDimension P = Module.finrank ℝ E)
    (hzero : (0 : E) ∈ intrinsicInterior ℝ P)
    (ha : spanProjection F hF.2.1 (0 : E) ∈ intrinsicInterior ℝ F)
    (hb : spanProjection G hG.2.1 (0 : E) ∈ intrinsicInterior ℝ G) :
    let W := (affineSpan ℝ R).directionᗮ
    let p := spanProjection R hRne (0 : E)
    let a := spanProjection F hF.2.1 (0 : E)
    let b := spanProjection G hG.2.1 (0 : E)
    Module.finrank ℝ W = 2 ∧ p ∈ W ∧ a ∈ W ∧ b ∈ W ∧
      p ≠ 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧ p ≠ a ∧ p ≠ b ∧
      inner (p - a) a = (0 : ℝ) ∧ inner (p - b) b = (0 : ℝ) ∧
      (inner a b : ℝ) < inner a a ∧ (inner a b : ℝ) < inner b b := by
  dsimp only
  let p := spanProjection R hRne (0 : E)
  let a := spanProjection F hF.2.1 (0 : E)
  let b := spanProjection G hG.2.1 (0 : E)
  have hFproper : F ≠ P := by
    intro hh
    have hd := hF.2.2
    rw [hh] at hd
    omega
  have hGproper : G ≠ P := by
    intro hh
    have hd := hG.2.2
    rw [hh] at hd
    omega
  have h0F := intrinsicInterior_not_mem_proper_face hF.1 hFproper hzero
  have h0G := intrinsicInterior_not_mem_proper_face hG.1 hGproper hzero
  have haF : a ∈ F := intrinsicInterior_subset ha
  have hbG : b ∈ G := intrinsicInterior_subset hb
  have ha0 : a ≠ 0 := fun h => h0F (h ▸ haF)
  have hb0 : b ≠ 0 := fun h => h0G (h ▸ hbG)
  have haorth : a ∈ (affineSpan ℝ F).directionᗮ := by
    simpa only [sub_zero] using spanProjection_sub_mem_orthogonal F hF.2.1 (0 : E)
  have hborth : b ∈ (affineSpan ℝ G).directionᗮ := by
    simpa only [sub_zero] using spanProjection_sub_mem_orthogonal G hG.2.1 (0 : E)
  have hFplane := affineSpan_eq_normal_hyperplane (spanProjection_mem F hF.2.1 (0 : E))
    ha0 (hF.2.2.trans hfull) haorth
  have hGplane := affineSpan_eq_normal_hyperplane (spanProjection_mem G hG.2.1 (0 : E))
    hb0 (hG.2.2.trans hfull) hborth
  have hFsupport := face_outward_normal hP hF.1 (intrinsicInterior_subset hzero)
    h0F haF (by simpa only [sub_zero] using hFplane)
  have hGsupport := face_outward_normal hP hG.1 (intrinsicInterior_subset hzero)
    h0G hbG (by simpa only [sub_zero] using hGplane)
  have hbnot := facet_intrinsicInterior_not_mem_other_span hG hF hFG.symm hb
  have hanot := facet_intrinsicInterior_not_mem_other_span hF hG hFG ha
  have hab : (inner a b : ℝ) < inner a a := by
    have hle := hFsupport b (hG.1.2.1 hbG)
    simp only [sub_zero, inner_sub_right] at hle
    have hne : (inner a b : ℝ) - inner a a ≠ 0 := by
      intro hz
      apply hbnot
      change b ∈ (affineSpan ℝ F : Set E)
      rw [hFplane]
      simpa only [Set.mem_setOf_eq, inner_sub_right] using hz
    exact sub_neg.mp (lt_of_le_of_ne hle hne)
  have hba : (inner a b : ℝ) < inner b b := by
    have hle := hGsupport a (hF.1.2.1 haF)
    simp only [sub_zero, inner_sub_right] at hle
    have hne : (inner b a : ℝ) - inner b b ≠ 0 := by
      intro hz
      apply hanot
      change a ∈ (affineSpan ℝ G : Set E)
      rw [hGplane]
      simpa only [Set.mem_setOf_eq, inner_sub_right] using hz
    rw [real_inner_comm a b] at hle hne
    exact sub_neg.mp (lt_of_le_of_ne hle hne)
  have hta : inner (p - a) a = (0 : ℝ) :=
    spanProjection_ridge_tangent hF.2.1 hRne hRF
  have htb : inner (p - b) b = (0 : ℝ) :=
    spanProjection_ridge_tangent hG.2.1 hRne hRG
  have hp0 : p ≠ 0 := by
    intro hz
    rw [hz, zero_sub, inner_neg_left] at hta
    have haa0 : (inner a a : ℝ) = 0 := by linarith
    exact ha0 (inner_self_eq_zero.mp haa0)
  have hpa : p ≠ a := by
    intro hh
    apply hanot
    change a ∈ affineSpan ℝ G
    rw [← hh]
    exact affineSpan_mono ℝ hRG (spanProjection_mem R hRne (0 : E))
  have hpb : p ≠ b := by
    intro hh
    apply hbnot
    change b ∈ affineSpan ℝ F
    rw [← hh]
    exact affineSpan_mono ℝ hRF (spanProjection_mem R hRne (0 : E))
  exact ⟨ridge_orthogonal_finrank hfull hrank,
    by simpa only [sub_zero] using spanProjection_sub_mem_orthogonal R hRne (0 : E),
    spanProjection_mem_ridge_orthogonal hF.2.1 hRF,
    spanProjection_mem_ridge_orthogonal hG.2.1 hRG,
    hp0, ha0, hb0, hpa, hpb, hta, htb, hab, hba⟩

/-- An actual two-plane and a nondegenerate tangent foot determine an
orthonormal frame whose first axis is the projected ridge direction. -/
theorem two_dimensional_tangent_frame (W : Submodule ℝ E)
    (hW : Module.finrank ℝ W = 2) {p a : E} (hpW : p ∈ W) (haW : a ∈ W)
    (hp0 : p ≠ 0) (ha0 : a ≠ 0) (hpa : p ≠ a)
    (ht : inner (p - a) a = (0 : ℝ)) :
    ∃ u v : E, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ inner u v = (0 : ℝ) ∧
      p = ‖p‖ • u ∧ Submodule.span ℝ ({u, v} : Set E) = W := by
  let u := ‖p‖⁻¹ • p
  have hu : ‖u‖ = 1 := by simpa only [u] using norm_smul_inv_norm hp0
  have hu0 : u ≠ 0 := by intro hz; rw [hz, norm_zero] at hu; norm_num at hu
  have huu : inner u u = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hpu : p = ‖p‖ • u := by
    dsimp [u]
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hp0), one_smul]
  have huW : u ∈ W := W.smul_mem _ hpW
  let t : ℝ := inner u a
  let w := a - t • u
  have hw0 : w ≠ 0 := by
    intro hz
    have haeq : a = t • u := sub_eq_zero.mp hz
    have ht0 : t ≠ 0 := by
      intro htt
      apply ha0
      rw [haeq, htt, zero_smul]
    have heq : (‖p‖ - t) * t = 0 := by
      have ht' : inner ((‖p‖ - t) • u) (t • u) = (0 : ℝ) := by
        rw [sub_smul, ← hpu, ← haeq]
        exact ht
      calc
        (‖p‖ - t) * t = (‖p‖ - t) * (t * inner u u) := by rw [huu]; ring
        _ = inner ((‖p‖ - t) • u) (t • u) := by
          conv_rhs => rw [real_inner_smul_left, real_inner_smul_right]
        _ = 0 := ht'
    have hrt : ‖p‖ = t := sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_right ht0)
    exact hpa (by rw [hpu, haeq, hrt])
  have huw : inner u w = (0 : ℝ) := by
    simp only [w, inner_sub_right, real_inner_smul_right, huu, mul_one]
    exact sub_self _
  let v := ‖w‖⁻¹ • w
  have hv : ‖v‖ = 1 := by simpa only [v] using norm_smul_inv_norm hw0
  have huv : inner u v = (0 : ℝ) := by simp only [v, real_inner_smul_right, huw, mul_zero]
  have hvW : v ∈ W := W.smul_mem _ (W.sub_mem haW (W.smul_mem _ huW))
  have hnot : v ∉ Submodule.span ℝ ({u} : Set E) := by
    intro hh
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hh
    have hkv := congrArg (fun x => (inner u x : ℝ)) hk
    change inner u (k • u) = (inner u v : ℝ) at hkv
    rw [real_inner_smul_right, huu, huv, mul_one] at hkv
    have hv0 : v = 0 := by rw [← hk, hkv, zero_smul]
    rw [hv0, norm_zero] at hv
    norm_num at hv
  have hle : Submodule.span ℝ ({u} : Set E) ≤ Submodule.span ℝ ({u, v} : Set E) :=
    Submodule.span_mono (by intro x hx; simp only [Set.mem_singleton_iff] at hx; simp [hx])
  have hlt : Submodule.span ℝ ({u} : Set E) < Submodule.span ℝ ({u, v} : Set E) := by
    refine lt_of_le_of_ne hle ?_
    intro hh
    apply hnot
    rw [hh]
    exact Submodule.subset_span (by simp)
  have hdim := Submodule.finrank_lt_finrank_of_lt hlt
  rw [finrank_span_singleton hu0] at hdim
  have hleW : Submodule.span ℝ ({u, v} : Set E) ≤ W := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with rfl | hx
    · exact huW
    · exact Set.mem_singleton_iff.mp hx ▸ hvW
  have hdimle := Submodule.finrank_mono hleW
  have heq : Submodule.span ℝ ({u, v} : Set E) = W :=
    Submodule.eq_of_le_of_finrank_eq hleW (by omega)
  exact ⟨u, v, hu, hv, huv, hpu, heq⟩

/-- Concrete opposite-tangent data for two actual convex polytopes after
a facet and its ridge have been aligned. Interior and projection hypotheses
are explicit; strict opposite sides and the two-plane are conclusions.
Equal adjacent offsets are the metric input supplied by equal facet types. -/
noncomputable def finitePolytope_oppositeTangentData
    {P P' F G G' R : Set E}
    (hP : FinitePolytope P) (hP' : FinitePolytope P')
    (hF : Facet P F) (hF' : Facet P' F)
    (hG : Facet P G) (hG' : Facet P' G')
    (hFG : F ≠ G) (hFG' : F ≠ G')
    (hRne : R.Nonempty) (hRF : R ⊆ F) (hRG : R ⊆ G) (hRG' : R ⊆ G')
    (hrank : affineDimension R + 2 = affineDimension P)
    (hfull : affineDimension P = Module.finrank ℝ E)
    (hfull' : affineDimension P' = Module.finrank ℝ E)
    (hzero : (0 : E) ∈ intrinsicInterior ℝ P)
    (hzero' : (0 : E) ∈ intrinsicInterior ℝ P')
    (ha : spanProjection F hF.2.1 (0 : E) ∈ intrinsicInterior ℝ F)
    (hb : spanProjection G hG.2.1 (0 : E) ∈ intrinsicInterior ℝ G)
    (hb' : spanProjection G' hG'.2.1 (0 : E) ∈ intrinsicInterior ℝ G')
    (hradius : ‖spanProjection G hG.2.1 (0 : E)‖ =
      ‖spanProjection G' hG'.2.1 (0 : E)‖) :
    OppositeTangentData (spanProjection G hG.2.1 (0 : E))
      (spanProjection G' hG'.2.1 (0 : E)) := Classical.choice <| by
  let W := (affineSpan ℝ R).directionᗮ
  let p := spanProjection R hRne (0 : E)
  let a := spanProjection F hF.2.1 (0 : E)
  let b := spanProjection G hG.2.1 (0 : E)
  let b' := spanProjection G' hG'.2.1 (0 : E)
  obtain ⟨hW, hpW, haW, hbW, hp0, ha0, hb0, hpa, _, hta, htb, hab, hba⟩ :=
    finitePolytope_ridge_projection hP hF hG hFG hRne hRF hRG hrank hfull hzero ha hb
  have hrank' : affineDimension R + 2 = affineDimension P' :=
    hrank.trans (hfull.trans hfull'.symm)
  obtain ⟨_, _, _, hbW', _, _, hb0', _, _, _, htb', hab', hba'⟩ :=
    finitePolytope_ridge_projection hP' hF' hG' hFG' hRne hRF hRG'
      hrank' hfull' hzero' ha hb'
  obtain ⟨u, v, hu, hv, huv, hpu, hplane⟩ :=
    two_dimensional_tangent_frame W hW hpW haW hp0 ha0 hpa hta
  have haplane : a ∈ Submodule.span ℝ ({u, v} : Set E) := by rw [hplane]; exact haW
  have hbplane : b ∈ Submodule.span ℝ ({u, v} : Set E) := by rw [hplane]; exact hbW
  have hbplane' : b' ∈ Submodule.span ℝ ({u, v} : Set E) := by rw [hplane]; exact hbW'
  have hr : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  have hta' : inner (‖p‖ • u - a) a = (0 : ℝ) := by rw [← hpu]; exact hta
  have htb'' : inner (‖p‖ • u - b) b = (0 : ℝ) := by rw [← hpu]; exact htb
  have htb''' : inner (‖p‖ • u - b') b' = (0 : ℝ) := by rw [← hpu]; exact htb'
  exact ⟨{
    p := p
    u := u
    v := v
    existingFoot := a
    r := ‖p‖
    d := ‖b‖
    unit_u := hu
    unit_v := hv
    orthogonal := huv
    p_eq := hpu
    r_ne_zero := hr.ne'
    mem_plane := hbplane
    mem_plane' := hbplane'
    radius := rfl
    radius' := hradius.symm
    tangent := htb
    tangent' := htb'
    opposite := tangent_cross_support_opposite hu hv huv hr ha0 hb0
      haplane hbplane hta' htb'' hab hba
    opposite' := tangent_cross_support_opposite hu hv huv hr ha0 hb0'
      haplane hbplane' hta' htb''' hab' hba'
  }⟩

end Uniform5.Composition
