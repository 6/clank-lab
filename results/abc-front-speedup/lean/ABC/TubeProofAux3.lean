import ABC.TubeProofAux2

/-!
# Auxiliary facts for the tube construction: the function `W`

`Wf w ξ` is the supremum of `0` and of the values `w a` over all `(a, 0)` that a lattice
translate of the orbit through `ξ` passes through. It is flow invariant and `2π`-periodic by
construction. If `w ≥ 0` is supported in a small ball around `p` and invariant under
`retMap` and `Pinv` on its support, the orbit through a point of `{w ≠ 0}` meets the planes
`z ∈ 2πℤ` only at (lattice translates of) points of `{w ≠ 0}` with the same `w`-value, so
`Wf w ξ` is `w` of the base point of `ξ`, and `Wf w` is Lipschitz.
-/

open Set Metric Real

noncomputable section

namespace ABC

/-- The values of `w` at the points where lattice translates of the orbit through `ξ` cross
`z = 0`, together with `0`. -/
def wSet (w : E 2 → ℝ) (ξ : E 3) : Set ℝ :=
  insert 0 {x | ∃ a s v, v ∈ Lat ∧ Γ ξ s = lift a 0 + v ∧ x = w a}

/-- The vortex-tube function. -/
def Wf (w : E 2 → ℝ) (ξ : E 3) : ℝ := sSup (wSet w ξ)

lemma Γ_rep {ξ ζ v : E 3} {s : ℝ} (hv : v ∈ Lat) (h : Γ ξ s = ζ + v) (u : ℝ) :
    Γ ζ u = Γ ξ (u + s) - v := by
  have : ζ = Γ ξ s + -v := by rw [h]; abel
  rw [this, Γ_add_Lat _ (neg_mem_Lat hv), Γ_Γ]
  simp [sub_eq_add_neg]

lemma wSet_Γ (w : E 2 → ℝ) (ξ : E 3) (t : ℝ) : wSet w (Γ ξ t) = wSet w ξ := by
  unfold wSet
  congr 1
  ext x
  simp only [mem_setOf_eq, Γ_Γ]
  constructor
  · rintro ⟨a, s, v, hv, h, rfl⟩; exact ⟨a, s + t, v, hv, h, rfl⟩
  · rintro ⟨a, s, v, hv, h, rfl⟩; exact ⟨a, s - t, v, hv, by simpa using h, rfl⟩

lemma wSet_add_Lat (w : E 2 → ℝ) (ξ : E 3) {u : E 3} (hu : u ∈ Lat) :
    wSet w (ξ + u) = wSet w ξ := by
  unfold wSet
  congr 1
  ext x
  simp only [mem_setOf_eq, Γ_add_Lat _ hu]
  constructor
  · rintro ⟨a, s, v, hv, h, rfl⟩
    exact ⟨a, s, v - u, sub_mem_Lat hv hu, by rw [← add_sub_assoc, ← h]; abel, rfl⟩
  · rintro ⟨a, s, v, hv, h, rfl⟩
    exact ⟨a, s, v + u, add_mem_Lat hv hu, by rw [h]; abel, rfl⟩

lemma Wf_Γ (w : E 2 → ℝ) (ξ : E 3) (t : ℝ) : Wf w (Γ ξ t) = Wf w ξ := by
  unfold Wf; rw [wSet_Γ]

lemma Wf_orbit (w : E 2 → ℝ) {γ : ℝ → E 3} (hγ : IsOrbit γ) (t : ℝ) : Wf w (γ t) = Wf w (γ 0) := by
  rw [← Wf_Γ w (γ 0) t, Γ_eq hγ rfl]

lemma Wf_add_Lat (w : E 2 → ℝ) (ξ : E 3) {u : E 3} (hu : u ∈ Lat) : Wf w (ξ + u) = Wf w ξ := by
  unfold Wf; rw [wSet_add_Lat _ _ hu]

lemma Wf_periodic (w : E 2 → ℝ) : Periodic (2 * π) (Wf w) := fun i ξ =>
  Wf_add_Lat w ξ (smul_ev_mem_Lat i)

section tube

variable {p : E 2} (hp : CertFacts p) {w : E 2 → ℝ} {δ : ℝ} (hδ : δ ≤ δ₀)
  (hsupp : ∀ a, w a ≠ 0 → a ∈ ball p δ)
  (hinv : ∀ a, w a ≠ 0 → w (retMap a) = w a ∧ w (Pinv a) = w a)

lemma δ₀_le_small : δ₀ ≤ 1 / 500 := δ₀_le.trans r₀_le

include hδ hsupp in
lemma supp_mem_N {a : E 2} (ha : w a ≠ 0) : a ∈ closedBall p r₀ :=
  ball_subset_closedBall (ball_subset_ball (hδ.trans δ₀_le) (hsupp a ha))

include hδ hsupp in
lemma supp_dist {a : E 2} (ha : w a ≠ 0) : dist a p < 1 / 500 :=
  lt_of_lt_of_le (mem_ball.1 (hsupp a ha)) (hδ.trans δ₀_le_small)

include hp hδ hsupp hinv

/-- Moving along the orbit through `ξ` from one crossing to the next, until the time lies in
`[-4, 4]`. -/
lemma near_rep_aux (ξ : E 3) (n : ℕ) :
    ∀ (s : ℝ) (a : E 2) (v : E 3), w a ≠ 0 → v ∈ Lat → |s| ≤ n * π + 4 →
      Γ ξ s = lift a 0 + v →
      ∃ s' ∈ Icc (-4 : ℝ) 4, ∃ a' v', w a' = w a ∧ v' ∈ Lat ∧ Γ ξ s' = lift a' 0 + v' := by
  induction n with
  | zero =>
    intro s a v _ hv hs h
    simp only [CharP.cast_eq_zero, zero_mul, zero_add] at hs
    exact ⟨s, ⟨(abs_le.1 hs).1, (abs_le.1 hs).2⟩, a, v, rfl, hv, h⟩
  | succ n ih =>
    intro s a v ha hv hs h
    by_cases hs4 : |s| ≤ 4
    · exact ⟨s, ⟨(abs_le.1 hs4).1, (abs_le.1 hs4).2⟩, a, v, rfl, hv, h⟩
    have haN := supp_mem_N hδ hsupp ha
    have hpi := Real.pi_gt_three
    push_cast at hs
    rcases le_or_gt s 0 with hs0 | hs0
    · -- go forward
      rw [abs_of_nonpos hs0] at hs hs4
      obtain ⟨σ, hσ1, hσ2, hσ⟩ := step_pos hp haN
      have hP := (hinv a ha).1
      have := ih (σ + s) (retMap a) (latt 0 0 1 + v) (by rw [hP]; exact ha)
        (add_mem_Lat (latt_mem_Lat 0 0 1) hv)
        (by rw [abs_le]; constructor <;> nlinarith)
        (by rw [← congrFun (Γ_Γ ξ s) σ, h, Γ_add_Lat _ hv]; beta_reduce; rw [hσ]; abel)
      obtain ⟨s', hs', a', v', hw, hv', h'⟩ := this
      exact ⟨s', hs', a', v', hw.trans hP, hv', h'⟩
    · -- go backward
      rw [abs_of_pos hs0] at hs hs4
      obtain ⟨σ, hσ1, hσ2, hσ⟩ := step_neg hp haN
      have hP := (hinv a ha).2
      have := ih (σ + s) (Pinv a) (latt 0 0 (-1) + v) (by rw [hP]; exact ha)
        (add_mem_Lat (latt_mem_Lat 0 0 (-1)) hv)
        (by rw [abs_le]; constructor <;> nlinarith)
        (by rw [← congrFun (Γ_Γ ξ s) σ, h, Γ_add_Lat _ hv]; beta_reduce; rw [hσ]; abel)
      obtain ⟨s', hs', a', v', hw, hv', h'⟩ := this
      exact ⟨s', hs', a', v', hw.trans hP, hv', h'⟩

lemma near_rep {ξ : E 3} {s : ℝ} {a : E 2} {v : E 3} (ha : w a ≠ 0) (hv : v ∈ Lat)
    (h : Γ ξ s = lift a 0 + v) :
    ∃ s' ∈ Icc (-4 : ℝ) 4, ∃ a' v', w a' = w a ∧ v' ∈ Lat ∧ Γ ξ s' = lift a' 0 + v' := by
  apply near_rep_aux hp hδ hsupp hinv ξ ⌈|s| / π⌉₊ s a v ha hv _ h
  have := Nat.le_ceil (|s| / π)
  rw [div_le_iff₀ Real.pi_pos] at this
  linarith

/-- Key lemma: a point `(b, 0)` near `p` on a lattice translate of the orbit of a point `a`
of the support has the same `w`-value. -/
lemma key {a b : E 2} {s : ℝ} {v : E 3} (ha : w a ≠ 0) (hb : dist b p < 1) (hv : v ∈ Lat)
    (h : Γ (lift a 0) s = lift b 0 + v) : w b = w a := by
  have h1 : Γ (lift b 0) (-s) = lift a 0 + -v := by
    rw [Γ_rep hv h]; simp [sub_eq_add_neg]
  obtain ⟨s', hs', a', v', hw, hv', h'⟩ :=
    near_rep hp hδ hsupp hinv ha (neg_mem_Lat hv) h1
  have ha' : w a' ≠ 0 := by rw [hw]; exact ha
  have h2 : Γ (lift a' 0) (-s') = lift b 0 + -v' := by
    rw [Γ_rep hv' h']; simp [sub_eq_add_neg]
  obtain ⟨m, n, k, hmnk⟩ := neg_mem_Lat hv'
  rw [hmnk] at h2
  have hs'' : -s' ∈ Icc (-4 : ℝ) 4 := ⟨by linarith [hs'.2], by linarith [hs'.1]⟩
  have hproj : proj (latt m n k) = proj (latt m n 0) := ext2 (by simp) (by simp)
  have hbd : ∀ x, w x ≠ 0 → dist x p < 1 / 500 := fun x hx => supp_dist hδ hsupp hx
  rcases window_base hp (supp_mem_N hδ hsupp ha') hs'' h2 with hc | hc | hc
  · have := eq_of_near hb (by linarith [hbd a' ha']) (hproj ▸ hc).symm
    rw [← this, hw]
  · have hP := (hinv a' ha').1
    have := eq_of_near hb (by linarith [hbd (retMap a') (show w (retMap a') ≠ 0 by rw [hP]; exact ha')])
      (hproj ▸ hc).symm
    rw [← this, hP, hw]
  · have hP := (hinv a' ha').2
    have := eq_of_near hb (by linarith [hbd (Pinv a') (show w (Pinv a') ≠ 0 by rw [hP]; exact ha')])
      (hproj ▸ hc).symm
    rw [← this, hP, hw]

variable (hw0 : ∀ a, 0 ≤ w a)
include hw0

lemma Wf_eq_of_near {ξ : E 3} {b : E 2} {s : ℝ} {v : E 3} (hb : dist b p < 1) (hv : v ∈ Lat)
    (h : Γ ξ s = lift b 0 + v) : Wf w ξ = w b := by
  apply IsGreatest.csSup_eq
  refine ⟨Or.inr ⟨b, s, v, hv, h, rfl⟩, ?_⟩
  rintro x (rfl | ⟨a, s', v', hv', h', rfl⟩)
  · exact hw0 b
  · by_cases ha : w a = 0
    · rw [ha]; exact hw0 b
    · have h'' : Γ (lift a 0) (s - s') = lift b 0 + (v - v') := by
        rw [Γ_rep hv' h', sub_add_cancel, h]; abel
      exact (key hp hδ hsupp hinv ha hb (sub_mem_Lat hv hv') h'').ge

lemma Wf_cases (ξ : E 3) : Wf w ξ = 0 ∨
    ∃ a s v, w a ≠ 0 ∧ v ∈ Lat ∧ Γ ξ s = lift a 0 + v ∧ Wf w ξ = w a := by
  by_cases hex : ∃ a s v, w a ≠ 0 ∧ v ∈ Lat ∧ Γ ξ s = lift a 0 + v
  · obtain ⟨a, s, v, ha, hv, h⟩ := hex
    right
    refine ⟨a, s, v, ha, hv, h, Wf_eq_of_near hp hδ hsupp hinv hw0 ?_ hv h⟩
    linarith [supp_dist hδ hsupp ha]
  · left
    push Not at hex
    apply IsGreatest.csSup_eq
    refine ⟨Or.inl rfl, ?_⟩
    rintro x (rfl | ⟨a, s', v', hv', h', rfl⟩)
    · exact le_rfl
    · by_contra hlt
      exact hex a s' v' (by intro h0; rw [h0] at hlt; exact hlt le_rfl) hv' h'

lemma Wf_nonneg (ξ : E 3) : 0 ≤ Wf w ξ := by
  rcases Wf_cases hp hδ hsupp hinv hw0 ξ with h | ⟨a, -, -, -, -, -, h⟩
  · rw [h]
  · rw [h]; exact hw0 a

lemma Wf_ne_zero_rep {ξ : E 3} (hξ : Wf w ξ ≠ 0) :
    ∃ s ∈ Icc (-4 : ℝ) 4, ∃ a v, w a ≠ 0 ∧ v ∈ Lat ∧ Γ ξ s = lift a 0 + v ∧ Wf w ξ = w a := by
  rcases Wf_cases hp hδ hsupp hinv hw0 ξ with h | ⟨a, s, v, ha, hv, h, hW⟩
  · exact absurd h hξ
  obtain ⟨s', hs', a', v', hw, hv', h'⟩ := near_rep hp hδ hsupp hinv ha hv h
  exact ⟨s', hs', a', v', by rw [hw]; exact ha, hv', h', hW.trans hw.symm⟩

lemma Wf_Vz {ξ : E 3} (hξ : Wf w ξ ≠ 0) : 19 / 10 ≤ abcField ξ 2 := by
  obtain ⟨s, hs, a, v, ha, hv, h, -⟩ := Wf_ne_zero_rep hp hδ hsupp hinv hw0 hξ
  have h1 : Γ (lift a 0) (-s) = ξ + -v := by
    rw [Γ_rep hv h]; simp [sub_eq_add_neg]
  have := window_Vz hp (supp_mem_N hδ hsupp ha) (t := -s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
  rwa [h1, abcField_add_Lat _ (neg_mem_Lat hv)] at this

lemma Wf_lift_p : Wf w (lift p 0) = w p :=
  Wf_eq_of_near hp hδ hsupp hinv hw0 (s := 0) (by simp) zero_mem_Lat (by simp)

/-- The local Lipschitz estimate, one-sided. -/
lemma Wf_local {C : NNReal} (hwL : LipschitzWith C w) {ξ η : E 3} (hξ : Wf w ξ ≠ 0)
    (hd : dist ξ η ≤ 1 / (10 * Real.exp 15)) :
    |Wf w ξ - Wf w η| ≤ C * (4 * Real.exp 15) * dist ξ η := by
  obtain ⟨s, hs, a, v, ha, hv, h, hW⟩ := Wf_ne_zero_rep hp hδ hsupp hinv hw0 hξ
  have haN := supp_mem_N hδ hsupp ha
  set γa := Γ (lift a 0) with hγa
  set β : ℝ → E 3 := fun u => Γ η (u + s) - v with hβ
  have hβo : IsOrbit β := by
    have := isOrbit_add_Lat (isOrbit_comp_add (Γ_orbit η) s) (neg_mem_Lat hv)
    rw [hβ]; simp only [sub_eq_add_neg]; exact this
  have hγo : IsOrbit γa := Γ_orbit _
  have hγs : γa (-s) = ξ - v := by rw [hγa, Γ_rep hv h]; simp
  have hβs : β (-s) = η - v := by simp [hβ]
  set d := dist ξ η with hd_def
  have he15 : 0 < Real.exp 15 := Real.exp_pos _
  -- Gronwall on `[-1, 1]`
  have hG : ∀ u ∈ Icc (-1 : ℝ) 1, dist (γa u) (β u) ≤ d * Real.exp 15 := by
    intro u hu
    have := orbit_dist_le' hγo hβo (-s) u
    rw [hγs, hβs, dist_sub_right] at this
    refine this.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) dist_nonneg)
    have : |u - -s| ≤ 5 := by
      rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hs.1, hs.2]
    linarith
  have hd' : d * Real.exp 15 ≤ 1 / 10 := by
    rw [le_div_iff₀ (by norm_num)]
    calc d * Real.exp 15 * 10 = d * (10 * Real.exp 15) := by ring
      _ ≤ 1 / (10 * Real.exp 15) * (10 * Real.exp 15) := by gcongr
      _ = 1 := by field_simp
  -- a crossing of `z = 0` by `β` in `[-1, 1]`
  have hz1 : 19 / 10 ≤ γa 1 2 := by
    have := window_mono hp haN (x := 0) (y := 1) (by norm_num) (by norm_num) (by norm_num)
    simp only [zz, zz_zero] at this
    rw [hγa]; linarith
  have hzm1 : γa (-1) 2 ≤ -(19 / 10) := by
    have := window_mono hp haN (x := -1) (y := 0) (by norm_num) (by norm_num) (by norm_num)
    simp only [zz, zz_zero] at this
    rw [hγa]; linarith
  have hb1 : 0 ≤ β 1 2 := by
    have h1 := abs_sub_le_dist3 (γa 1) (β 1) 2
    have h2 := hG 1 (by norm_num)
    rw [abs_le] at h1; linarith
  have hbm1 : β (-1) 2 ≤ 0 := by
    have h1 := abs_sub_le_dist3 (γa (-1)) (β (-1)) 2
    have h2 := hG (-1) (by norm_num)
    rw [abs_le] at h1; linarith
  have hcont : ContinuousOn (fun u => β u 2) (Icc (-1) 1) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.comp
      (orbit_continuous hβo)).continuousOn
  obtain ⟨u₀, hu₀, hzu₀⟩ := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1) hcont
    (show (0 : ℝ) ∈ Icc (β (-1) 2) (β 1 2) from ⟨hbm1, hb1⟩)
  simp only at hzu₀
  have hest := cross_est hγo (γ₂ := β) (l := -4) (r := 4) (u₁ := 0) (u₂ := u₀)
    (fun t ht => window_Vz hp haN ht) (by norm_num) ⟨by linarith [hu₀.1], by linarith [hu₀.2]⟩
    (by rw [hzu₀, hγa, Γ_zero]; simp)
  set b := proj (β u₀) with hb_def
  have hβb : β u₀ = lift b 0 := (lift_proj hzu₀).symm
  have hab : dist a b ≤ 4 * (d * Real.exp 15) := by
    rw [← dist_lift a b 0, ← hβb]
    have : γa 0 = lift a 0 := by rw [hγa, Γ_zero]
    rw [← this]
    exact hest.2.trans (by gcongr; exact hG u₀ hu₀)
  have hbp : dist b p < 1 := by
    have := supp_dist hδ hsupp ha
    calc dist b p ≤ dist b a + dist a p := dist_triangle _ _ _
      _ < 1 := by rw [dist_comm]; linarith
  have hη : Γ η (u₀ + s) = lift b 0 + v := by
    rw [← hβb]; simp [hβ]
  rw [hW, Wf_eq_of_near hp hδ hsupp hinv hw0 hbp hv hη]
  calc |w a - w b| = dist (w a) (w b) := (Real.dist_eq _ _).symm
    _ ≤ C * dist a b := hwL.dist_le_mul a b
    _ ≤ C * (4 * (d * Real.exp 15)) := by gcongr
    _ = C * (4 * Real.exp 15) * d := by ring

lemma Wf_bound {C : NNReal} (hwL : LipschitzWith C w) (ξ : E 3) : Wf w ξ ≤ w p + C := by
  rcases Wf_cases hp hδ hsupp hinv hw0 ξ with h | ⟨a, -, -, ha, -, -, h⟩
  · rw [h]; have := hw0 p; positivity
  · rw [h]
    have h1 := hwL.dist_le_mul a p
    have h2 := supp_dist hδ hsupp ha
    rw [Real.dist_eq] at h1
    have : C * dist a p ≤ C * 1 := by gcongr; linarith
    linarith [le_abs_self (w a - w p)]

lemma Wf_lipschitz {C : NNReal} (hwL : LipschitzWith C w) : ∃ K, LipschitzWith K (Wf w) := by
  set ε : ℝ := 1 / (10 * Real.exp 15) with hε
  have hεpos : 0 < ε := by positivity
  set B : ℝ := w p + C with hB
  have hB0 : 0 ≤ B := by have := hw0 p; positivity
  set K : ℝ := max (C * (4 * Real.exp 15)) (2 * B / ε) with hK
  have hK0 : 0 ≤ K := le_max_of_le_right (by positivity)
  refine ⟨Real.toNNReal K, LipschitzWith.of_dist_le_mul fun ξ η => ?_⟩
  rw [Real.coe_toNNReal _ hK0, Real.dist_eq]
  have hloc : dist ξ η ≤ ε → |Wf w ξ - Wf w η| ≤ K * dist ξ η := by
    intro hd
    by_cases hξ : Wf w ξ ≠ 0
    · exact (Wf_local hp hδ hsupp hinv hw0 hwL hξ hd).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg)
    by_cases hη : Wf w η ≠ 0
    · rw [abs_sub_comm, dist_comm]
      rw [dist_comm] at hd
      exact (Wf_local hp hδ hsupp hinv hw0 hwL hη hd).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg)
    push Not at hξ hη
    rw [hξ, hη]; simp only [sub_self, abs_zero]; positivity
  rcases le_or_gt (dist ξ η) ε with hd | hd
  · exact hloc hd
  · have h1 := Wf_nonneg hp hδ hsupp hinv hw0 ξ
    have h2 := Wf_nonneg hp hδ hsupp hinv hw0 η
    have h3 := Wf_bound hp hδ hsupp hinv hw0 hwL ξ
    have h4 := Wf_bound hp hδ hsupp hinv hw0 hwL η
    have : |Wf w ξ - Wf w η| ≤ 2 * B := by rw [abs_le]; constructor <;> linarith
    calc |Wf w ξ - Wf w η| ≤ 2 * B := this
      _ = 2 * B / ε * ε := by field_simp
      _ ≤ K * dist ξ η := mul_le_mul (le_max_right _ _) hd.le hεpos.le hK0

end tube

end ABC
