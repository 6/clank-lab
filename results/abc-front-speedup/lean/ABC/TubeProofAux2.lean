import ABC.TubeProofAux1

/-!
# Auxiliary facts for the tube construction: local crossing structure near `p`

For `a` within `r₀` of the certified fixed point `p`, the orbit from `(a, 0)` has
`V_z ≥ 1.9` on the time window `[-4, 4]`, so it crosses every height in `[-7, 7]` exactly once
there. `crossP a c` is the crossing point. `retMap a = crossP a (2π)`, and
`Pinv a := crossP a (-2π)` inverts `retMap` near `p`.
-/

open Set Metric Real

noncomputable section

namespace ABC

/-- The radius of the ball around `p` on which the crossing structure is controlled. -/
def r₀ : ℝ := 1 / (500 * Real.exp 12)

lemma r₀_pos : 0 < r₀ := by unfold r₀; positivity

lemma r₀_mul_exp : r₀ * Real.exp 12 = 1 / 500 := by
  unfold r₀; field_simp

lemma r₀_le : r₀ ≤ 1 / 500 := by
  have h1 : 1 ≤ Real.exp 12 := Real.one_le_exp (by norm_num)
  unfold r₀
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- The height along the orbit from `(a, 0)`. -/
abbrev zz (a : E 2) (t : ℝ) : ℝ := Γ (lift a 0) t 2

lemma zz_zero (a : E 2) : zz a 0 = 0 := by
  show Γ (lift a 0) 0 2 = 0
  rw [Γ_zero]; simp

lemma two_pi_lt_seven : 2 * π < 7 := by linarith [Real.pi_lt_d2]

lemma mem_Icc_two_pi : 2 * π ∈ Icc (-7 : ℝ) 7 :=
  ⟨by linarith [Real.pi_pos], two_pi_lt_seven.le⟩

lemma mem_Icc_neg_two_pi : -(2 * π) ∈ Icc (-7 : ℝ) 7 :=
  ⟨by linarith [two_pi_lt_seven], by linarith [Real.pi_pos]⟩

/-! ### The fixed orbit -/

lemma fixed_orbit {p : E 2} (hp : CertFacts p) :
    ∃ T, 32352 / 10000 ≤ T ∧ T ≤ 32354 / 10000 ∧ Γ (lift p 0) T = lift p (2 * π) ∧
      Γ (lift p 0) (-T) = lift p (-(2 * π)) ∧ ∀ t, 192 / 100 ≤ abcField (Γ (lift p 0) t) 2 := by
  obtain ⟨γ, T, hγ, h0, hT1, hT2, hT, hV⟩ := hp.orbit
  have hΓ : Γ (lift p 0) = γ := Γ_eq hγ h0
  rw [hΓ]
  have hper : (fun t => γ (t + T)) = fun t => γ t + latt 0 0 1 := by
    apply orbit_unique (isOrbit_comp_add hγ T) (isOrbit_add_Lat hγ (latt_mem_Lat 0 0 1))
      (t₀ := 0)
    simp only [zero_add, hT, h0]
    exact ext3 (by simp) (by simp) (by simp)
  have hTpos : 0 < T := by linarith
  refine ⟨T, hT1, hT2, hT, ?_, ?_⟩
  · have := congrFun hper (-T)
    simp only [neg_add_cancel, h0] at this
    apply ext3
    · have := congrArg (fun x : E 3 => x 0) this; simp at this; simp [this]
    · have := congrArg (fun x : E 3 => x 1) this; simp at this; simp [this]
    · have := congrArg (fun x : E 3 => x 2) this; simp at this; simp; linarith
  · have hf : Function.Periodic (fun t => abcField (γ t) 2) T := by
      intro t
      simp only
      rw [congrFun hper t, abcField_add_Lat _ (latt_mem_Lat 0 0 1)]
    intro t
    obtain ⟨y, hy, hty⟩ := hf.exists_mem_Ico₀ hTpos t
    simp only at hty
    rw [hty]
    exact hV y ⟨hy.1, hy.2.le⟩

/-! ### The window around `p` -/

section window

variable {p : E 2} (hp : CertFacts p)
include hp

lemma window_Vz {a : E 2} (ha : a ∈ closedBall p r₀) {t : ℝ} (ht : t ∈ Icc (-4 : ℝ) 4) :
    19 / 10 ≤ abcField (Γ (lift a 0) t) 2 := by
  obtain ⟨T, -, -, -, -, hV⟩ := fixed_orbit hp
  have hd := orbit_dist_le (Γ_orbit (lift a 0)) (Γ_orbit (lift p 0)) t
  rw [Γ_zero, Γ_zero, dist_lift] at hd
  have he : Real.exp (3 * |t|) ≤ Real.exp 12 := by
    apply Real.exp_le_exp.2
    have := abs_le.2 ⟨ht.1, ht.2⟩
    linarith
  have hd' : dist (Γ (lift a 0) t) (Γ (lift p 0) t) ≤ 1 / 500 := by
    calc _ ≤ dist a p * Real.exp (3 * |t|) := hd
      _ ≤ r₀ * Real.exp 12 := mul_le_mul (mem_closedBall.1 ha) he (by positivity) r₀_pos.le
      _ = 1 / 500 := r₀_mul_exp
  have := abcField_two_lip (Γ (lift a 0) t) (Γ (lift p 0) t)
  have := hV t
  rw [abs_le] at *
  linarith

lemma window_mono {a : E 2} (ha : a ∈ closedBall p r₀) {x y : ℝ} (hx : x ∈ Icc (-4 : ℝ) 4)
    (hy : y ∈ Icc (-4 : ℝ) 4) (hxy : x ≤ y) : 19 / 10 * (y - x) ≤ zz a y - zz a x :=
  z_lower (Γ_orbit _) (fun _ ht => window_Vz hp ha ht) hx hy hxy

lemma window_inj {a : E 2} (ha : a ∈ closedBall p r₀) {x y : ℝ} (hx : x ∈ Icc (-4 : ℝ) 4)
    (hy : y ∈ Icc (-4 : ℝ) 4) (h : zz a x = zz a y) : x = y := by
  rcases le_total x y with hxy | hxy
  · have := window_mono hp ha hx hy hxy; linarith
  · have := window_mono hp ha hy hx hxy; linarith

lemma window_lt {a : E 2} (ha : a ∈ closedBall p r₀) {x y : ℝ} (hx : x ∈ Icc (-4 : ℝ) 4)
    (hy : y ∈ Icc (-4 : ℝ) 4) (hxy : x < y) : zz a x < zz a y := by
  have := window_mono hp ha hx hy hxy.le; linarith

lemma window_exists {a : E 2} (ha : a ∈ closedBall p r₀) {c : ℝ} (hc : c ∈ Icc (-7 : ℝ) 7) :
    ∃ u ∈ Icc (-4 : ℝ) 4, zz a u = c := by
  have h4 := window_mono hp ha (x := 0) (y := 4) (by norm_num) (by norm_num) (by norm_num)
  have h4' := window_mono hp ha (x := -4) (y := 0) (by norm_num) (by norm_num) (by norm_num)
  rw [zz_zero] at h4 h4'
  have hcont : ContinuousOn (zz a) (Icc (-4) 4) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.comp
      (orbit_continuous (Γ_orbit (lift a 0)))).continuousOn
  have := intermediate_value_Icc (by norm_num : (-4 : ℝ) ≤ 4) hcont
    (show c ∈ Icc (zz a (-4)) (zz a 4) from ⟨by linarith [hc.1], by linarith [hc.2]⟩)
  obtain ⟨u, hu, huc⟩ := this
  exact ⟨u, hu, huc⟩

end window

/-! ### Crossing times and points -/

open Classical in
/-- The time in `[-4, 4]` at which the orbit from `(a, 0)` has height `c` (junk `0`). -/
def crossT (a : E 2) (c : ℝ) : ℝ :=
  if h : ∃ u ∈ Icc (-4 : ℝ) 4, zz a u = c then h.choose else 0

/-- The crossing point at height `c`. -/
def crossP (a : E 2) (c : ℝ) : E 2 := proj (Γ (lift a 0) (crossT a c))

/-- The inverse first-crossing map near `p`: the crossing point at height `-2π`. -/
def Pinv (a : E 2) : E 2 := crossP a (-(2 * π))

lemma crossT_spec' {a : E 2} {c : ℝ} (h : ∃ u ∈ Icc (-4 : ℝ) 4, zz a u = c) :
    crossT a c ∈ Icc (-4 : ℝ) 4 ∧ zz a (crossT a c) = c := by
  unfold crossT; rw [dif_pos h]; exact h.choose_spec

lemma Γ_crossT' {a : E 2} {c : ℝ} (h : ∃ u ∈ Icc (-4 : ℝ) 4, zz a u = c) :
    Γ (lift a 0) (crossT a c) = lift (crossP a c) c :=
  (lift_proj (crossT_spec' h).2).symm

section window2

variable {p : E 2} (hp : CertFacts p)
include hp

lemma crossT_spec {a : E 2} (ha : a ∈ closedBall p r₀) {c : ℝ} (hc : c ∈ Icc (-7 : ℝ) 7) :
    crossT a c ∈ Icc (-4 : ℝ) 4 ∧ zz a (crossT a c) = c :=
  crossT_spec' (window_exists hp ha hc)

lemma Γ_crossT {a : E 2} (ha : a ∈ closedBall p r₀) {c : ℝ} (hc : c ∈ Icc (-7 : ℝ) 7) :
    Γ (lift a 0) (crossT a c) = lift (crossP a c) c :=
  Γ_crossT' (window_exists hp ha hc)

lemma crossT_unique {a : E 2} (ha : a ∈ closedBall p r₀) {u c : ℝ} (hu : u ∈ Icc (-4 : ℝ) 4)
    (h : zz a u = c) : u = crossT a c := by
  have hs := crossT_spec' ⟨u, hu, h⟩
  exact window_inj hp ha hu hs.1 (by rw [h, hs.2])

lemma crossP_eq {a b : E 2} (ha : a ∈ closedBall p r₀) {u c : ℝ} (hu : u ∈ Icc (-4 : ℝ) 4)
    (h : Γ (lift a 0) u = lift b c) : crossP a c = b := by
  have hz : zz a u = c := by simp [zz, h]
  unfold crossP
  rw [← crossT_unique hp ha hu hz, h, proj_lift]

lemma crossT_pos_ge {a : E 2} (ha : a ∈ closedBall p r₀) :
    π ≤ crossT a (2 * π) ∧ crossT a (2 * π) ≤ 4 := by
  obtain ⟨hu, hz⟩ := crossT_spec hp ha mem_Icc_two_pi
  refine ⟨?_, hu.2⟩
  have hl := z_lip (Γ_orbit (lift a 0)) (crossT a (2 * π)) 0
  have hpos : 0 < crossT a (2 * π) := by
    by_contra hneg
    push Not at hneg
    have := window_mono hp ha hu (by norm_num : (0 : ℝ) ∈ Icc (-4 : ℝ) 4) hneg
    rw [hz, zz_zero] at this
    linarith [Real.pi_pos]
  simp only [zz] at hz
  rw [hz, Γ_zero, lift_apply_two, sub_zero, sub_zero, abs_of_pos (by positivity),
    abs_of_pos hpos] at hl
  linarith

lemma crossT_neg_le {a : E 2} (ha : a ∈ closedBall p r₀) :
    -4 ≤ crossT a (-(2 * π)) ∧ crossT a (-(2 * π)) ≤ -π := by
  obtain ⟨hu, hz⟩ := crossT_spec hp ha mem_Icc_neg_two_pi
  refine ⟨hu.1, ?_⟩
  have hl := z_lip (Γ_orbit (lift a 0)) (crossT a (-(2 * π))) 0
  have hneg : crossT a (-(2 * π)) < 0 := by
    by_contra hpos
    push Not at hpos
    have := window_mono hp ha (by norm_num : (0 : ℝ) ∈ Icc (-4 : ℝ) 4) hu hpos
    rw [hz, zz_zero] at this
    linarith [Real.pi_pos]
  simp only [zz] at hz
  rw [hz, Γ_zero, lift_apply_two, sub_zero, sub_zero, abs_neg, abs_of_pos (by positivity),
    abs_of_neg hneg] at hl
  linarith

/-- `retMap` is the crossing at height `2π`. -/
lemma returnsTo_crossP {a : E 2} (ha : a ∈ closedBall p r₀) :
    ReturnsTo a (crossP a (2 * π)) := by
  obtain ⟨hu, hz⟩ := crossT_spec hp ha mem_Icc_two_pi
  have hT := crossT_pos_ge hp ha
  refine ⟨Γ (lift a 0), crossT a (2 * π), Γ_orbit _, Γ_zero _, by linarith [Real.pi_pos],
    Γ_crossT hp ha mem_Icc_two_pi, fun t ht => ?_⟩
  have htw : t ∈ Icc (-4 : ℝ) 4 := ⟨by linarith [ht.1], by linarith [ht.2, hu.2]⟩
  have := window_lt hp ha htw hu ht.2
  rw [hz] at this
  exact this

end window2

lemma returnsTo_unique {a b b' : E 2} (h : ReturnsTo a b) (h' : ReturnsTo a b') : b = b' := by
  obtain ⟨γ, T, hγ, h0, hT, hγT, hlt⟩ := h
  obtain ⟨γ', T', hγ', h0', hT', hγT', hlt'⟩ := h'
  have he : γ = γ' := orbit_unique hγ hγ' (t₀ := 0) (by rw [h0, h0'])
  subst he
  have hTT : T = T' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hl | hl
    · have := hlt' T ⟨hT.le, hl⟩
      rw [hγT] at this; simp at this
    · have := hlt T' ⟨hT'.le, hl⟩
      rw [hγT'] at this; simp at this
  subst hTT
  rw [hγT] at hγT'
  exact (lift_inj hγT').1

lemma retMap_eq {a b : E 2} (h : ReturnsTo a b) : retMap a = b := by
  unfold retMap
  rw [dif_pos ⟨b, h⟩]
  exact returnsTo_unique (Exists.choose_spec (⟨b, h⟩ : ∃ b, ReturnsTo a b)) h

section window3

variable {p : E 2} (hp : CertFacts p)
include hp

lemma retMap_eq_crossP {a : E 2} (ha : a ∈ closedBall p r₀) :
    retMap a = crossP a (2 * π) :=
  retMap_eq (returnsTo_crossP hp ha)

omit hp in
/-- Two crossings at the same height `c`, of an orbit with `V_z ≥ 1.9` on an interval and of a
nearby orbit, are close in time and in space. -/
lemma cross_est {γ₁ γ₂ : ℝ → E 3} (h₁ : IsOrbit γ₁) {l r u₁ u₂ : ℝ}
    (hV : ∀ t ∈ Icc l r, 19 / 10 ≤ abcField (γ₁ t) 2) (hu₁ : u₁ ∈ Icc l r) (hu₂ : u₂ ∈ Icc l r)
    (hz : γ₁ u₁ 2 = γ₂ u₂ 2) :
    |u₁ - u₂| ≤ dist (γ₁ u₂) (γ₂ u₂) / (19 / 10) ∧
      dist (γ₁ u₁) (γ₂ u₂) ≤ 4 * dist (γ₁ u₂) (γ₂ u₂) := by
  have hd := abs_sub_le_dist3 (γ₁ u₂) (γ₂ u₂) 2
  rw [← hz] at hd
  have h1 : 19 / 10 * |u₁ - u₂| ≤ dist (γ₁ u₂) (γ₂ u₂) := by
    rcases le_total u₁ u₂ with hle | hle
    · have := z_lower h₁ hV hu₁ hu₂ hle
      rw [abs_of_nonpos (by linarith : u₁ - u₂ ≤ 0)]
      linarith [le_abs_self ((γ₁ u₂) 2 - (γ₁ u₁) 2)]
    · have := z_lower h₁ hV hu₂ hu₁ hle
      rw [abs_of_nonneg (by linarith : 0 ≤ u₁ - u₂)]
      linarith [neg_abs_le ((γ₁ u₂) 2 - (γ₁ u₁) 2)]
  have ht : |u₁ - u₂| ≤ dist (γ₁ u₂) (γ₂ u₂) / (19 / 10) := by
    rw [le_div_iff₀ (by norm_num)]; linarith
  refine ⟨ht, ?_⟩
  calc dist (γ₁ u₁) (γ₂ u₂) ≤ dist (γ₁ u₁) (γ₁ u₂) + dist (γ₁ u₂) (γ₂ u₂) := dist_triangle _ _ _
    _ ≤ 4 * |u₁ - u₂| + dist (γ₁ u₂) (γ₂ u₂) := by
        gcongr; simpa [Real.dist_eq] using orbit_lip h₁ u₁ u₂
    _ ≤ 4 * dist (γ₁ u₂) (γ₂ u₂) := by nlinarith [dist_nonneg (x := γ₁ u₂) (y := γ₂ u₂)]

lemma crossP_lip {a b : E 2} (ha : a ∈ closedBall p r₀) (hb : b ∈ closedBall p r₀) {c : ℝ}
    (hc : c ∈ Icc (-7 : ℝ) 7) :
    dist (crossP a c) (crossP b c) ≤ 4 * Real.exp 12 * dist a b := by
  obtain ⟨hua, hza⟩ := crossT_spec hp ha hc
  obtain ⟨hub, hzb⟩ := crossT_spec hp hb hc
  have hest := cross_est (Γ_orbit (lift a 0)) (γ₂ := Γ (lift b 0)) (fun t ht => window_Vz hp ha ht)
    hua hub (by simp only [zz] at hza hzb; rw [hza, hzb])
  have hg := orbit_dist_le (Γ_orbit (lift a 0)) (Γ_orbit (lift b 0)) (crossT b c)
  rw [Γ_zero, Γ_zero, dist_lift] at hg
  have he : Real.exp (3 * |crossT b c|) ≤ Real.exp 12 := by
    apply Real.exp_le_exp.2
    have := abs_le.2 ⟨hub.1, hub.2⟩
    linarith
  calc dist (crossP a c) (crossP b c)
      ≤ dist (Γ (lift a 0) (crossT a c)) (Γ (lift b 0) (crossT b c)) := dist_proj_le _ _
    _ ≤ 4 * dist (Γ (lift a 0) (crossT b c)) (Γ (lift b 0) (crossT b c)) := hest.2
    _ ≤ 4 * (dist a b * Real.exp 12) := by
        gcongr; exact hg.trans (mul_le_mul_of_nonneg_left he dist_nonneg)
    _ = 4 * Real.exp 12 * dist a b := by ring

lemma crossP_continuousOn {c : ℝ} (hc : c ∈ Icc (-7 : ℝ) 7) :
    ContinuousOn (fun a => crossP a c) (closedBall p r₀) := by
  have : LipschitzOnWith (Real.toNNReal (4 * Real.exp 12)) (fun a => crossP a c)
      (closedBall p r₀) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    rw [Real.coe_toNNReal _ (by positivity)]
    exact crossP_lip hp ha hb hc
  exact this.continuousOn

lemma crossP_p_pos : crossP p (2 * π) = p := by
  obtain ⟨T, hT1, hT2, hT, -, -⟩ := fixed_orbit hp
  exact crossP_eq hp (mem_closedBall_self r₀_pos.le) ⟨by linarith, by linarith⟩ hT

lemma crossP_p_neg : crossP p (-(2 * π)) = p := by
  obtain ⟨T, hT1, hT2, -, hT, -⟩ := fixed_orbit hp
  exact crossP_eq hp (mem_closedBall_self r₀_pos.le) ⟨by linarith, by linarith⟩ hT

/-- The radius on which `retMap` and `Pinv` land in the controlled ball. -/
def δ₀ : ℝ := r₀ / (4 * Real.exp 12)

omit hp in
lemma δ₀_pos : 0 < δ₀ := by unfold δ₀; have := r₀_pos; positivity

omit hp in
lemma δ₀_le : δ₀ ≤ r₀ := by
  unfold δ₀
  have h1 : 1 ≤ Real.exp 12 := Real.one_le_exp (by norm_num)
  rw [div_le_iff₀ (by positivity)]
  nlinarith [r₀_pos]

lemma crossP_mem {a : E 2} (ha : a ∈ closedBall p δ₀) {c : ℝ} (hc : c ∈ Icc (-7 : ℝ) 7)
    (hcp : crossP p c = p) : crossP a c ∈ closedBall p r₀ := by
  have ha' : a ∈ closedBall p r₀ := closedBall_subset_closedBall δ₀_le ha
  have := crossP_lip hp ha' (mem_closedBall_self r₀_pos.le) hc
  rw [hcp] at this
  rw [mem_closedBall]
  calc _ ≤ 4 * Real.exp 12 * dist a p := this
    _ ≤ 4 * Real.exp 12 * δ₀ := by gcongr; exact mem_closedBall.1 ha
    _ = r₀ := by unfold δ₀; field_simp

lemma retMap_mem {a : E 2} (ha : a ∈ closedBall p δ₀) : retMap a ∈ closedBall p r₀ := by
  rw [retMap_eq_crossP hp (closedBall_subset_closedBall δ₀_le ha)]
  exact crossP_mem hp ha mem_Icc_two_pi (crossP_p_pos hp)

lemma Pinv_mem {a : E 2} (ha : a ∈ closedBall p δ₀) : Pinv a ∈ closedBall p r₀ :=
  crossP_mem hp ha mem_Icc_neg_two_pi (crossP_p_neg hp)

/-- The orbit from `(a, 0)` reaches `(retMap a, 2π)` at a time in `[π, 4]`. -/
lemma step_pos {a : E 2} (ha : a ∈ closedBall p r₀) :
    ∃ σ, π ≤ σ ∧ σ ≤ 4 ∧ Γ (lift a 0) σ = lift (retMap a) 0 + latt 0 0 1 := by
  refine ⟨crossT a (2 * π), (crossT_pos_ge hp ha).1, (crossT_pos_ge hp ha).2, ?_⟩
  rw [Γ_crossT hp ha mem_Icc_two_pi, retMap_eq_crossP hp ha]
  exact ext3 (by simp) (by simp) (by simp)

/-- The orbit from `(a, 0)` reaches `(Pinv a, -2π)` at a time in `[-4, -π]`. -/
lemma step_neg {a : E 2} (ha : a ∈ closedBall p r₀) :
    ∃ σ, -4 ≤ σ ∧ σ ≤ -π ∧ Γ (lift a 0) σ = lift (Pinv a) 0 + latt 0 0 (-1) := by
  refine ⟨crossT a (-(2 * π)), (crossT_neg_le hp ha).1, (crossT_neg_le hp ha).2, ?_⟩
  rw [Γ_crossT hp ha mem_Icc_neg_two_pi]
  exact ext3 (by simp [Pinv]) (by simp [Pinv]) (by simp)

lemma retMap_Pinv {a : E 2} (ha : a ∈ closedBall p r₀) : retMap (Pinv a) = a := by
  obtain ⟨σ, hσ1, hσ2, hσ⟩ := step_neg hp ha
  have hΓ : Γ (lift (Pinv a) 0) = fun t => Γ (lift a 0) (t + σ) + latt 0 0 1 := by
    apply Γ_eq (isOrbit_add_Lat (isOrbit_comp_add (Γ_orbit _) σ) (latt_mem_Lat 0 0 1))
    simp only [zero_add, hσ]
    exact ext3 (by simp) (by simp) (by simp)
  apply retMap_eq
  refine ⟨Γ (lift (Pinv a) 0), -σ, Γ_orbit _, Γ_zero _, by linarith [Real.pi_pos], ?_, ?_⟩
  · rw [hΓ]; simp only [neg_add_cancel, Γ_zero]
    exact ext3 (by simp) (by simp) (by simp)
  · intro t ht
    rw [hΓ]
    have := window_lt hp ha (x := t + σ) (y := 0) ⟨by linarith [ht.1], by linarith [ht.2]⟩
      (by norm_num) (by linarith [ht.2])
    rw [zz_zero] at this
    simp only [zz] at this
    simp; linarith

lemma Pinv_retMap {a : E 2} (ha : a ∈ closedBall p r₀) (hb : retMap a ∈ closedBall p r₀) :
    Pinv (retMap a) = a := by
  obtain ⟨σ, hσ1, hσ2, hσ⟩ := step_pos hp ha
  have hΓ : Γ (lift (retMap a) 0) = fun t => Γ (lift a 0) (t + σ) + latt 0 0 (-1) := by
    apply Γ_eq (isOrbit_add_Lat (isOrbit_comp_add (Γ_orbit _) σ) (latt_mem_Lat 0 0 (-1)))
    simp only [zero_add, hσ]
    exact ext3 (by simp) (by simp) (by simp)
  apply crossP_eq hp hb (u := -σ) ⟨by linarith, by linarith [Real.pi_pos]⟩
  rw [hΓ]; simp only [neg_add_cancel, Γ_zero]
  exact ext3 (by simp) (by simp) (by simp)

/-- Base case: a lattice translate of `(b, 0)` on the orbit from `(a, 0)` within the window is
`a`, `retMap a` or `Pinv a`, up to an `xy` lattice shift. -/
lemma window_base {a b : E 2} (ha : a ∈ closedBall p r₀) {s : ℝ} (hs : s ∈ Icc (-4 : ℝ) 4)
    {m n k : ℤ} (h : Γ (lift a 0) s = lift b 0 + latt m n k) :
    b + proj (latt m n k) = a ∨ b + proj (latt m n k) = retMap a ∨
      b + proj (latt m n k) = Pinv a := by
  rw [lift_add_latt, zero_add] at h
  have hz : zz a s = 2 * π * k := by simp [zz, h]
  have hl := z_lip (Γ_orbit (lift a 0)) s 0
  simp only [Γ_zero, lift_apply_two, sub_zero] at hl
  have hsz : |s| ≤ 4 := abs_le.2 ⟨hs.1, hs.2⟩
  have hk : |(k : ℝ)| < 2 := by
    have h1 : |Γ (lift a 0) s 2| = 2 * π * |(k : ℝ)| := by
      simp only [zz] at hz
      rw [hz, abs_mul, abs_of_pos (by positivity : 0 < 2 * π)]
    have hpi := Real.pi_gt_three
    nlinarith [abs_nonneg (k : ℝ)]
  have hk' : k = 0 ∨ k = 1 ∨ k = -1 := by
    have : |k| < 2 := by exact_mod_cast hk
    rw [abs_lt] at this
    omega
  rcases hk' with rfl | rfl | rfl
  · left
    have : s = 0 := window_inj hp ha hs (by norm_num) (by rw [hz, zz_zero]; simp)
    subst this
    rw [Γ_zero] at h
    exact ((lift_inj h).1).symm
  · right; left
    rw [retMap_eq_crossP hp ha]
    exact (crossP_eq hp ha hs (by rw [h]; simp)).symm
  · right; right
    exact (crossP_eq hp ha hs (by rw [h]; simp)).symm

end window3

end ABC
