import ABC.Flow

/-!
# Planar facts for `lemmaW`

For one radial graph `C_s = {g(ψ, s)(cos ψ, sin ψ)}` we split the plane into the inside
`{‖u‖ < g(arg u, s)}`, the curve `{‖u‖ = g(arg u, s)}` and the outside `{‖u‖ > g(arg u, s)}`,
and prove the elementary facts used in `ABC/LemmaW.lean`.
-/

open MeasureTheory Set Metric Filter Topology

noncomputable section

namespace ABC
namespace LemmaWAux

/-- A point of the plane as a complex number. -/
def toC (u : E 2) : ℂ := (u 0 : ℂ) + (u 1 : ℂ) * Complex.I

@[simp] lemma toC_re (u : E 2) : (toC u).re = u 0 := by simp [toC]

@[simp] lemma toC_im (u : E 2) : (toC u).im = u 1 := by simp [toC]

lemma continuous_toC : Continuous toC := by unfold toC; fun_prop

lemma norm_toC (u : E 2) : ‖toC u‖ = ‖u‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.normSq_apply,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, toC_re, toC_im]
  ring

lemma toC_smul (t : ℝ) (u : E 2) : toC (t • u) = t * toC u := by
  apply Complex.ext <;> simp

lemma toC_polarPt (r ψ : ℝ) :
    toC (polarPt r ψ) = r * (Real.cos ψ + Real.sin ψ * Complex.I) := by
  apply Complex.ext <;> simp [polarPt, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

lemma polarPt_arg (u : E 2) : polarPt ‖u‖ (Complex.arg (toC u)) = u := by
  ext i
  fin_cases i
  · simp [polarPt, ← norm_toC, Complex.norm_mul_cos_arg]
  · simp [polarPt, ← norm_toC, Complex.norm_mul_sin_arg]

/-- The hypotheses on one curve `g(·, s)`. -/
def Good (g : ℝ → ℝ → ℝ) (ρ s : ℝ) : Prop :=
  Continuous (fun ψ => g ψ s) ∧ (∀ ψ, g (ψ + 2 * Real.pi) s = g ψ s) ∧
    ∀ ψ, 0 < g ψ s ∧ g ψ s < ρ

/-- `g(arg u, s)`. -/
def G (g : ℝ → ℝ → ℝ) (s : ℝ) (u : E 2) : ℝ := g (Complex.arg (toC u)) s

/-- The inside `{‖u‖ < g(arg u, s)}`. -/
def Ins (g : ℝ → ℝ → ℝ) (s : ℝ) : Set (E 2) := {u | ‖u‖ < G g s u}

/-- The curve `{‖u‖ = g(arg u, s)}`. -/
def Crv (g : ℝ → ℝ → ℝ) (s : ℝ) : Set (E 2) := {u | ‖u‖ = G g s u}

/-- The outside `{g(arg u, s) < ‖u‖}`. -/
def Out (g : ℝ → ℝ → ℝ) (s : ℝ) : Set (E 2) := {u | G g s u < ‖u‖}

variable {g : ℝ → ℝ → ℝ} {ρ s : ℝ}

lemma Good.periodic (hs : Good g ρ s) : Function.Periodic (fun ψ => g ψ s) (2 * Real.pi) :=
  hs.2.1

lemma Good.continuous_lift (hs : Good g ρ s) : Continuous hs.periodic.lift :=
  (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 hs.1

lemma Good.G_eq (hs : Good g ρ s) (u : E 2) :
    G g s u = hs.periodic.lift ((Complex.arg (toC u) : Real.Angle)) := rfl

lemma Good.continuousAt_G (hs : Good g ρ s) {u : E 2} (hu : u ≠ 0) : ContinuousAt (G g s) u := by
  have h0 : toC u ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_toC]; exact norm_ne_zero_iff.2 hu
  have : G g s = hs.periodic.lift ∘ (((↑) ∘ Complex.arg : ℂ → Real.Angle) ∘ toC) := rfl
  rw [this]
  exact hs.continuous_lift.continuousAt.comp
    ((Complex.continuousAt_arg_coe_angle h0).comp continuous_toC.continuousAt)

lemma Good.G_pos (hs : Good g ρ s) (u : E 2) : 0 < G g s u := (hs.2.2 _).1

lemma Good.G_lt (hs : Good g ρ s) (u : E 2) : G g s u < ρ := (hs.2.2 _).2

lemma Good.exists_min (hs : Good g ρ s) : ∃ m > 0, ∀ u, m ≤ G g s u := by
  obtain ⟨ψ₀, -, hψ₀⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (by linarith [Real.pi_pos]))
    (hs.1.continuousOn (s := Icc (-Real.pi) Real.pi))
  refine ⟨g ψ₀ s, (hs.2.2 ψ₀).1, fun u => ?_⟩
  exact hψ₀ (Ioc_subset_Icc_self (Complex.arg_mem_Ioc _))

lemma norm_polarPt (r ψ : ℝ) : ‖polarPt r ψ‖ = |r| := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _), EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_two, sq_abs]
  simp [polarPt]
  linear_combination r ^ 2 * Real.cos_sq_add_sin_sq ψ

lemma Good.G_polarPt (hs : Good g ρ s) {r : ℝ} (hr : 0 < r) (ψ : ℝ) :
    G g s (polarPt r ψ) = g ψ s := by
  have h := Complex.arg_mul_cos_add_sin_mul_I_coe_angle hr (ψ : Real.Angle)
  rw [Real.Angle.cos_coe, Real.Angle.sin_coe] at h
  rw [hs.G_eq, toC_polarPt, h]
  rfl

lemma Good.isOpen_Out (hs : Good g ρ s) : IsOpen (Out g s) := by
  refine isOpen_iff_mem_nhds.2 fun u hu => ?_
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact absurd hu (by simpa [Out] using (hs.G_pos 0).le)
  exact (hs.continuousAt_G hu0).eventually_lt continuous_norm.continuousAt hu

lemma Good.isOpen_Ins (hs : Good g ρ s) : IsOpen (Ins g s) := by
  obtain ⟨m, hm, hmG⟩ := hs.exists_min
  refine isOpen_iff_mem_nhds.2 fun u hu => ?_
  by_cases hu0 : u = 0
  · subst hu0
    refine mem_of_superset (ball_mem_nhds 0 hm) fun v hv => ?_
    rw [mem_ball_zero_iff] at hv
    exact hv.trans_le (hmG v)
  · exact continuous_norm.continuousAt.eventually_lt (hs.continuousAt_G hu0) hu

lemma Good.zero_mem_Ins (hs : Good g ρ s) : (0 : E 2) ∈ Ins g s := by
  show ‖(0 : E 2)‖ < _
  rw [norm_zero]; exact hs.G_pos 0

lemma Good.Ins_subset_ball (hs : Good g ρ s) : Ins g s ⊆ ball 0 ρ := fun u hu =>
  mem_ball_zero_iff.2 (lt_trans hu (hs.G_lt u))

lemma Good.isCompact_Cl (hs : Good g ρ s) : IsCompact {u : E 2 | ‖u‖ ≤ G g s u} := by
  refine (isCompact_closedBall (0 : E 2) ρ).of_isClosed_subset ?_ fun u hu =>
    mem_closedBall_zero_iff.2 (le_trans hu (hs.G_lt u).le)
  have : {u : E 2 | ‖u‖ ≤ G g s u} = (Out g s)ᶜ := by
    ext u; simp [Out]
  rw [this]; exact hs.isOpen_Out.isClosed_compl

lemma Good.Crv_eq (hs : Good g ρ s) : Crv g s = curve g s := by
  ext u
  constructor
  · intro hu
    refine ⟨Complex.arg (toC u), ?_⟩
    have hu' : ‖u‖ = g (Complex.arg (toC u)) s := hu
    simp only
    rw [← hu']
    exact polarPt_arg u
  · rintro ⟨ψ, rfl⟩
    have hpos := (hs.2.2 ψ).1
    show ‖polarPt (g ψ s) ψ‖ = G g s (polarPt (g ψ s) ψ)
    rw [norm_polarPt, abs_of_pos hpos, hs.G_polarPt hpos]

lemma Good.isPreconnected_Ins (hs : Good g ρ s) : IsPreconnected (Ins g s) := by
  refine (StarConvex.isPathConnected (a := 0) ?_ hs.zero_mem_Ins).isConnected.isPreconnected
  intro v hv a b ha hb hab
  rw [smul_zero, zero_add]
  rcases hb.eq_or_lt with rfl | hb'
  · rw [zero_smul]; exact hs.zero_mem_Ins
  · show ‖b • v‖ < G g s (b • v)
    have hG : G g s (b • v) = G g s v := by
      simp only [G, toC_smul, Complex.arg_real_mul _ hb']
    have hv' : ‖v‖ < G g s v := hv
    rw [hG, norm_smul, Real.norm_of_nonneg hb]
    have hb1 : b ≤ 1 := by linarith
    calc b * ‖v‖ ≤ ‖v‖ := mul_le_of_le_one_left (norm_nonneg v) hb1
      _ < G g s v := hv'

/-- A segment from the inside to a point not inside meets the curve. -/
lemma Good.exists_Crv (hs : Good g ρ s) {u v : E 2} (hu : u ∈ Ins g s) (hv : v ∉ Ins g s) :
    ∃ t ∈ Icc (0 : ℝ) 1, u + t • (v - u) ∈ Crv g s := by
  by_contra hne
  push Not at hne
  have hpc : Continuous fun t : ℝ => u + t • (v - u) := by fun_prop
  have hS := (isPreconnected_Icc (a := (0 : ℝ)) (b := 1)).image _ hpc.continuousOn
  have hsub : (fun t : ℝ => u + t • (v - u)) '' Icc 0 1 ⊆ Ins g s ∪ Out g s := by
    rintro _ ⟨t, ht, rfl⟩
    rcases lt_trichotomy ‖u + t • (v - u)‖ (G g s (u + t • (v - u))) with h | h | h
    · exact Or.inl h
    · exact absurd h (hne t ht)
    · exact Or.inr h
  have hvO : v ∈ Out g s := by
    rcases lt_trichotomy ‖v‖ (G g s v) with h | h | h
    · exact absurd h hv
    · have := hne 1 ⟨zero_le_one, le_rfl⟩
      simp only [one_smul, add_sub_cancel] at this
      exact absurd h this
    · exact h
  obtain ⟨x, -, hxI, hxO⟩ := hS (Ins g s) (Out g s) hs.isOpen_Ins hs.isOpen_Out hsub
    ⟨u, ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩, hu⟩
    ⟨v, ⟨1, ⟨zero_le_one, le_rfl⟩, by simp⟩, hvO⟩
  exact lt_asymm (show ‖x‖ < G g s x from hxI) (show G g s x < ‖x‖ from hxO)

end LemmaWAux
end ABC
