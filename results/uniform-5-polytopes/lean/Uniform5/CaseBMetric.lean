import Uniform5.Formulas
import Uniform5.Separation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Real.Pi.Bounds

/-!
Metric arguments in the Case B section. All points are actual vectors in a
real inner-product space. The long-edge proof uses the Euclidean triangle
inequality at the antipode; its sufficient bound `4 sin (π/17) < 1` avoids
the rounded decimal in the manuscript.
-/

noncomputable section
open scoped RealInnerProductSpace

namespace Uniform5.CaseB

noncomputable def chord (q : ℝ) : ℝ := 2 * Real.cos (Real.pi / q)

noncomputable def polygonRadius (q : ℝ) : ℝ := 1 / (2 * Real.sin (Real.pi / q))

noncomputable def antiprismHeightSq (n : ℝ) : ℝ :=
  1 - 1 / (4 * Real.cos (Real.pi / (2 * n)) ^ 2)

noncomputable def antiprismRadiusSq (n : ℝ) : ℝ :=
  polygonRadius n ^ 2 + antiprismHeightSq n / 4

theorem chord_mono {m n : ℝ} (hm : 3 ≤ m) (hmn : m ≤ n) :
    chord m ≤ chord n := by
  have hm0 : 0 < m := by linarith
  have hn0 : 0 < n := by linarith
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.cos_le_cos_of_nonneg_of_le_pi
  · positivity
  · exact (div_le_iff₀ hm0).mpr (by nlinarith [Real.pi_pos])
  · exact div_le_div_of_nonneg_left Real.pi_pos.le hm0 hmn

theorem chord_strictMono : StrictMonoOn chord (Set.Ici 3) := by
  intro m hm n hn hmn
  change 3 ≤ m at hm
  change 3 ≤ n at hn
  have hm0 : 0 < m := by linarith [hm]
  have hn0 : 0 < n := by linarith [hn]
  apply mul_lt_mul_of_pos_left _ (by norm_num : (0 : ℝ) < 2)
  apply Real.cos_lt_cos_of_nonneg_of_le_pi
  · positivity
  · exact (div_le_iff₀ hm0).mpr (by nlinarith [Real.pi_pos, hm])
  · exact div_lt_div_of_pos_left Real.pi_pos hm0 hmn

theorem chord_four : chord 4 = Real.sqrt 2 := by
  simp [chord, Real.cos_pi_div_four]
  ring

theorem chord_eq_sqrt_two_iff {q : ℝ} (hq : 3 ≤ q) :
    chord q = Real.sqrt 2 ↔ q = 4 := by
  rw [← chord_four]
  exact ⟨fun h => chord_strictMono.injOn hq (by norm_num) h, fun h => congrArg chord h⟩

theorem chord_seventeen_gt : 7 / 4 < chord 17 := by
  have h := Real.one_sub_sq_div_two_le_cos (x := Real.pi / 17)
  have hp := Real.pi_lt_four
  have hp0 := Real.pi_pos
  unfold chord
  nlinarith

/-- The three small paired candidates `(m,3,3)`, `(m,3,4)` and `(m,3,5)`
fail the acute-triangle criterion for every `m≥17`. -/
theorem paired_small_triangle_obtuse {m : ℝ} (hm : 17 ≤ m)
    {q : ℝ} (hq : 3 ≤ q) (hq5 : q ≤ 5) :
    chord 3 ^ 2 + chord q ^ 2 < chord m ^ 2 := by
  have h17 : 31 / 16 < chord 17 := by
    have h := Real.one_sub_sq_div_two_le_cos (x := Real.pi / 17)
    have hp := Real.pi_lt_four
    have hp0 := Real.pi_pos
    unfold chord
    nlinarith
  have hm' := h17.trans_le (chord_mono (by norm_num) hm)
  have hq' := chord_mono hq hq5
  have hq0 : 0 ≤ chord q := by
    have h := chord_mono (m := 3) (by norm_num) hq
    norm_num [chord, Real.cos_pi_div_three] at h
    change 0 ≤ 2 * Real.cos (Real.pi / q)
    linarith
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hs0 := Real.sqrt_nonneg (5 : ℝ)
  have hslt : Real.sqrt 5 < 5 / 2 := by nlinarith
  have h5 : chord 5 = (1 + Real.sqrt 5) / 2 := by
    simp [chord, Real.cos_pi_div_five]; ring
  have hq_sq := pow_le_pow_left₀ hq0 hq' 2
  rw [h5] at hq_sq
  norm_num [chord, Real.cos_pi_div_three] at ⊢
  change 1 + chord q ^ 2 < (2 * Real.cos (Real.pi / m)) ^ 2
  change 31 / 16 < 2 * Real.cos (Real.pi / m) at hm'
  nlinarith

theorem chord_lt_two {q : ℝ} (hq : 3 ≤ q) : chord q < 2 := by
  have hq0 : 0 < q := by linarith
  have hp : Real.pi / q ≤ Real.pi :=
    (div_le_iff₀ hq0).mpr (by nlinarith [Real.pi_pos])
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0)
    hp (div_pos Real.pi_pos hq0)
  simp only [Real.cos_zero] at h
  unfold chord
  linarith

/-- The antiprism diagonal is strictly between the 5- and 6-gon chords;
this proves the metric exclusion used in the mixed paired case. -/
theorem antiprism_diagonal_between {n : ℝ} (hn : 17 ≤ n) :
    chord 5 < Real.sqrt (1 + chord n) ∧ Real.sqrt (1 + chord n) < chord 6 := by
  have hc := (chord_seventeen_gt.trans_le (chord_mono (by norm_num) hn))
  have hc2 := chord_lt_two (q := n) (by linarith)
  have hd := Real.sq_sqrt (show 0 ≤ 1 + chord n by linarith)
  have hd0 := Real.sqrt_nonneg (1 + chord n)
  have hs5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hs50 := Real.sqrt_nonneg (5 : ℝ)
  have hs3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hs30 := Real.sqrt_nonneg (3 : ℝ)
  have h5 : chord 5 = (1 + Real.sqrt 5) / 2 := by
    simp [chord, Real.cos_pi_div_five]; ring
  have h6 : chord 6 = Real.sqrt 3 := by simp [chord, Real.cos_pi_div_six]; ring
  rw [h5, h6]
  have hs5lt : Real.sqrt 5 < 5 / 2 := by nlinarith
  constructor
  · apply (sq_lt_sq₀ (by positivity) hd0).mp
    nlinarith
  · apply (sq_lt_sq₀ hd0 hs30).mp
    linarith

theorem antiprism_diagonal_not_chord {n : ℝ} (hn : 17 ≤ n)
    {q : ℕ} (hq : 3 ≤ q) : Real.sqrt (1 + chord n) ≠ chord q := by
  obtain ⟨hl, hu⟩ := antiprism_diagonal_between hn
  by_cases hq5 : q ≤ 5
  · have h := chord_mono (m := q) (n := 5) (by exact_mod_cast hq) (by exact_mod_cast hq5)
    linarith
  · have hq6 : 6 ≤ q := by omega
    have h := chord_mono (m := 6) (n := q) (by norm_num) (by exact_mod_cast hq6)
    linarith

theorem antiprism_diagonal_ne_sqrt_two {n : ℝ} (hn : 17 ≤ n) :
    Real.sqrt (1 + chord n) ≠ Real.sqrt 2 := by
  rw [← chord_four]
  exact antiprism_diagonal_not_chord hn (q := 4) (by decide)

theorem four_sin_pi_seventeen_lt_one : 4 * Real.sin (Real.pi / 17) < 1 := by
  have hs := Real.sin_le (show 0 ≤ Real.pi / 17 by positivity)
  have hp := Real.pi_lt_four
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A long chord puts its other endpoint within `2 sin (π/17)` of
the antipode. The radius is at most one; no angle comparison is assumed. -/
theorem long_chord_antipode_bound {a b : E} {r : ℝ}
    (ha : ‖a‖ = r) (hb : ‖b‖ = r) (hr : r ≤ 1)
    (hlong : chord 17 ≤ dist a b) :
    ‖a + b‖ ≤ 2 * Real.sin (Real.pi / 17) := by
  have hr0 : 0 ≤ r := ha ▸ norm_nonneg a
  have hs : 0 ≤ Real.sin (Real.pi / 17) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos (Real.pi / 17) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have htrig := Real.sin_sq_add_cos_sq (Real.pi / 17)
  have hsum := norm_add_sq_real a b
  have hsub := norm_sub_sq_real a b
  rw [ha, hb] at hsum hsub
  simp only [chord, dist_eq_norm] at hlong
  have hsq : (2 * Real.cos (Real.pi / 17)) ^ 2 ≤ ‖a - b‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlong 2
  nlinarith [norm_nonneg (a + b)]

/-- Paper `lem:long`, pointwise form. Two long chords from one point on
the VF sphere cannot have distinct endpoints in a unit-separated set. -/
theorem long_edges_same_endpoint {a b b' o : E} {r : ℝ}
    (ha : dist a o = r) (hb : dist b o = r) (hb' : dist b' o = r)
    (hr : r ≤ 1) (hab : chord 17 ≤ dist a b) (hab' : chord 17 ≤ dist a b')
    (hsep : b ≠ b' → 1 ≤ dist b b') : b = b' := by
  by_contra hne
  have h₁ := long_chord_antipode_bound (a := a - o) (b := b - o)
    (by simpa [dist_eq_norm] using ha) (by simpa [dist_eq_norm] using hb) hr
    (by simpa [dist_eq_norm] using hab)
  have h₂ := long_chord_antipode_bound (a := a - o) (b := b' - o)
    (by simpa [dist_eq_norm] using ha) (by simpa [dist_eq_norm] using hb') hr
    (by simpa [dist_eq_norm] using hab')
  have htri := norm_sub_le ((a - o) + (b - o)) ((a - o) + (b' - o))
  have heq : (a - o + (b - o)) - (a - o + (b' - o)) = b - b' := by abel
  rw [heq] at htri
  have hsep' := hsep hne
  rw [dist_eq_norm] at hsep'
  linarith [four_sin_pi_seventeen_lt_one]

/-- The same lemma for polygon sizes, including the threshold monotonicity. -/
theorem long_polygon_edges_same_endpoint {a b b' o : E} {r n m : ℝ}
    (ha : dist a o = r) (hb : dist b o = r) (hb' : dist b' o = r)
    (hr : r ≤ 1) (hn : 17 ≤ n) (hm : 17 ≤ m)
    (hab : dist a b = chord n) (hab' : dist a b' = chord m)
    (hsep : b ≠ b' → 1 ≤ dist b b') : b = b' := by
  apply long_edges_same_endpoint ha hb hb' hr
  · rw [hab]; exact chord_mono (by norm_num) hn
  · rw [hab']; exact chord_mono (by norm_num) hm
  · exact hsep

/-- Paper `lem:long`, disjointness of the endpoint sets of two distinct
unoriented long edges. Separation is inherited from the original polytope,
not an assertion that the edges of its vertex figure have unit length. -/
theorem long_edges_disjoint {V : Set E} {a b c d o : E} {r : ℝ}
    (hsphere : ∀ x ∈ V, dist x o = r) (hr : r ≤ 1)
    (hsep : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → 1 ≤ dist x y)
    (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V) (hd : d ∈ V)
    (hab : chord 17 ≤ dist a b) (hcd : chord 17 ≤ dist c d)
    (hne : ¬ (a = c ∧ b = d)) (hne' : ¬ (a = d ∧ b = c)) :
    Disjoint ({a, b} : Set E) {c, d} := by
  apply Set.disjoint_left.mpr
  intro z hz₁ hz₂
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz₁ hz₂
  rcases hz₁ with hza | hzb <;> rcases hz₂ with hzc | hzd
  · have hac : a = c := hza.symm.trans hzc
    exact hne ⟨hac, long_edges_same_endpoint (hsphere a ha) (hsphere b hb)
      (hsphere d hd) hr hab (by simpa [hac] using hcd) (hsep b hb d hd)⟩
  · have had : a = d := hza.symm.trans hzd
    have hbc := long_edges_same_endpoint (hsphere a ha) (hsphere b hb)
      (hsphere c hc) hr hab (by simpa [had, dist_comm] using hcd) (hsep b hb c hc)
    exact hne' ⟨had, hbc⟩
  · have hbc : b = c := hzb.symm.trans hzc
    have had := long_edges_same_endpoint (hsphere b hb) (hsphere a ha)
      (hsphere d hd) hr (by simpa [dist_comm] using hab)
      (by simpa [hbc] using hcd) (hsep a ha d hd)
    exact hne' ⟨had, hbc⟩
  · have hbd : b = d := hzb.symm.trans hzd
    have hac := long_edges_same_endpoint (hsphere b hb) (hsphere a ha)
      (hsphere c hc) hr (by simpa [dist_comm] using hab)
      (by simpa [hbd, dist_comm] using hcd) (hsep a ha c hc)
    exact hne ⟨hac, hbd⟩

/-- Solve the two equidistance equations in the plane of the two unit
prism rays. This derives the offset instead of assuming its length. -/
theorem two_ray_offset {z₁ z₂ w : E} {g : ℝ}
    (hz₁ : ‖z₁‖ = 1) (hz₂ : ‖z₂‖ = 1) (hg : ⟪z₁, z₂⟫ = g)
    (hg₁ : g ≠ 1) (hg₂ : g ≠ -1)
    (hw : ∃ α β : ℝ, w = α • z₁ + β • z₂)
    (hw₁ : ⟪w, z₁⟫ = 1 / 2) (hw₂ : ⟪w, z₂⟫ = 1 / 2) :
    w = (1 / (2 * (1 + g))) • (z₁ + z₂) ∧ ‖w‖ ^ 2 = 1 / (2 * (1 + g)) := by
  obtain ⟨α, β, rfl⟩ := hw
  have hg' : ⟪z₂, z₁⟫ = g := by rw [real_inner_comm, hg]
  simp only [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    hz₁, hz₂, hg, hg', one_pow, mul_one] at hw₁ hw₂
  have hab : α = β := by
    have : (α - β) * (1 - g) = 0 := by nlinarith [hw₁, hw₂]
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact (hg₁ (by linarith)).elim
  have hg0 : 1 + g ≠ 0 := by intro h; exact hg₂ (by linarith)
  have ha : α = 1 / (2 * (1 + g)) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hg0)).mpr
    nlinarith [hw₁]
  have hv : α • z₁ + β • z₂ = (1 / (2 * (1 + g))) • (z₁ + z₂) := by
    rw [hab, ← smul_add, ← ha, hab]
  refine ⟨hv, ?_⟩
  rw [hv, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_add_sq_real,
    hz₁, hz₂, hg]
  field_simp
  ring

/-- The planar offset for a `q`-gon equals its squared circumradius. -/
theorem two_ray_polygon_radius {z₁ z₂ w : E} {q : ℝ} (hq : 3 ≤ q)
    (hz₁ : ‖z₁‖ = 1) (hz₂ : ‖z₂‖ = 1)
    (hg : ⟪z₁, z₂⟫ = Real.cos (Real.pi * (1 - 2 / q)))
    (hw : ∃ α β : ℝ, w = α • z₁ + β • z₂)
    (hw₁ : ⟪w, z₁⟫ = 1 / 2) (hw₂ : ⟪w, z₂⟫ = 1 / 2) :
    ‖w‖ ^ 2 = polygonRadius q ^ 2 := by
  have hq0 : 0 < q := by linarith
  have ht0 : 0 < Real.pi / q := div_pos Real.pi_pos hq0
  have ht : Real.pi / q < Real.pi / 2 := by
    apply (div_lt_div_iff₀ hq0 (by norm_num : (0 : ℝ) < 2)).mpr
    nlinarith [Real.pi_pos]
  have hs := Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ht⟩
  have htrig := Real.sin_sq_add_cos_sq (Real.pi / q)
  have hangle : Real.cos (Real.pi * (1 - 2 / q)) =
      2 * Real.sin (Real.pi / q) ^ 2 - 1 := by
    have heq : Real.pi * (1 - 2 / q) = Real.pi - 2 * (Real.pi / q) := by ring
    rw [heq, Real.cos_sub, Real.cos_pi, Real.sin_pi, Real.cos_two_mul]
    nlinarith
  have hg₁ : Real.cos (Real.pi * (1 - 2 / q)) ≠ 1 := by
    rw [hangle]; nlinarith [sq_pos_of_pos hc]
  have hg₂ : Real.cos (Real.pi * (1 - 2 / q)) ≠ -1 := by
    rw [hangle]; nlinarith [sq_pos_of_pos hs]
  rw [(two_ray_offset hz₁ hz₂ hg hg₁ hg₂ hw hw₁ hw₂).2, hangle]
  unfold polygonRadius
  field_simp
  ring

/-- Paper type-(ii) radius identity, with the actual orthogonal rays and
equidistance equations as inputs. -/
theorem type_ii_radius {z₁ z₂ w h W : E} {q n R hA : ℝ}
    (hq : 3 ≤ q) (hz₁ : ‖z₁‖ = 1) (hz₂ : ‖z₂‖ = 1)
    (hg : ⟪z₁, z₂⟫ = Real.cos (Real.pi * (1 - 2 / q)))
    (hw : ∃ α β : ℝ, w = α • z₁ + β • z₂)
    (hw₁ : ⟪w, z₁⟫ = 1 / 2) (hw₂ : ⟪w, z₂⟫ = 1 / 2)
    (hh : ‖h‖ = 1) (hhw : ⟪h, w⟫ = 0)
    (hW : W = (hA / 2) • h + w)
    (hheight : hA ^ 2 = antiprismHeightSq n)
    (hR : R ^ 2 = polygonRadius n ^ 2 + ‖W‖ ^ 2) :
    R ^ 2 = antiprismRadiusSq n + polygonRadius q ^ 2 := by
  have hoff := two_ray_polygon_radius hq hz₁ hz₂ hg hw hw₁ hw₂
  rw [hW, norm_add_sq_real, real_inner_smul_left, hhw, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs, hh, hoff] at hR
  unfold antiprismRadiusSq
  nlinarith [hheight]

end Uniform5.CaseB
