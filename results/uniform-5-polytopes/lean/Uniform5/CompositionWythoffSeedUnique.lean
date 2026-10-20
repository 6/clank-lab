import Uniform5.CompositionLibraryNames

/-! Signed mirror equations determine a seed in the span of the roots.
The four full-dimensional rank-four systems span their actual ambient
space; the A4 equations determine the seed in its sum-zero hyperplane.
Consequently every one of the 75 named Wythoff models has one congruence
type, with no chosen-model agreement premise. -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Equality of the signed mirror data extends from roots to their span. -/
theorem wythoffSeed_inner_eq_on_span {k : ℕ} {r : Fin k → E} {J : Finset (Fin k)}
    {x y : E} (hx : WythoffSeed r J x) (hy : WythoffSeed r J y)
    {z : E} (hz : z ∈ Submodule.span ℝ (Set.range r)) : ⟪z, x - y⟫ = 0 := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, rfl⟩ := hz
    rw [inner_sub_right, hx i, hy i, sub_self]
  | zero => simp
  | add a b ha hb iha ihb => simp only [inner_add_left, iha, ihb, add_zero]
  | smul c a ha ih => simp only [real_inner_smul_left, ih, mul_zero]

theorem wythoffSeed_unique_in_span {k : ℕ} {r : Fin k → E} {J : Finset (Fin k)}
    {x y : E} (hx : WythoffSeed r J x) (hy : WythoffSeed r J y)
    (hxs : x ∈ Submodule.span ℝ (Set.range r))
    (hys : y ∈ Submodule.span ℝ (Set.range r)) : x = y := by
  have hh := wythoffSeed_inner_eq_on_span hx hy (Submodule.sub_mem _ hxs hys)
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hh)

theorem wythoffSeed_unique_of_span_top {k : ℕ} {r : Fin k → E}
    (hspan : Submodule.span ℝ (Set.range r) = ⊤) {J : Finset (Fin k)}
    {x y : E} (hx : WythoffSeed r J x) (hy : WythoffSeed r J y) : x = y :=
  wythoffSeed_unique_in_span hx hy (by rw [hspan]; trivial) (by rw [hspan]; trivial)

theorem rootsB4_annihilator {x : ModelSpace 4} (hx : ∀ i, ⟪rootsB4 i, x⟫ = 0) : x = 0 := by
  have h0 := hx ⟨0, by decide⟩
  have h1 := hx ⟨1, by decide⟩
  have h2 := hx ⟨2, by decide⟩
  have h3 := hx ⟨3, by decide⟩
  norm_num [rootsB4, coordinateVector, inner_sub_left, EuclideanSpace.inner_single_left,
    Fin.isValue, Fin.mk.injEq, Fin.succ] at h0 h1 h2 h3
  change x 0 - x 1 = 0 at h0
  change x 1 - x 2 = 0 at h1
  change x 2 - x 3 = 0 at h2
  change x 3 = 0 at h3
  have hx0 : x 0 = 0 := by linarith
  have hx1 : x 1 = 0 := by linarith
  have hx2 : x 2 = 0 := by linarith
  have hx3 : x 3 = 0 := by linarith
  ext i
  fin_cases i <;> first | exact hx0 | exact hx1 | exact hx2 | exact hx3

theorem rootsD4_annihilator {x : ModelSpace 4} (hx : ∀ i, ⟪rootsD4 i, x⟫ = 0) : x = 0 := by
  have h0 := hx ⟨0, by decide⟩
  have h1 := hx ⟨1, by decide⟩
  have h2 := hx ⟨2, by decide⟩
  have h3 := hx ⟨3, by decide⟩
  norm_num [rootsD4, coordinateVector, inner_sub_left, inner_add_left,
    EuclideanSpace.inner_single_left, Fin.isValue, Fin.mk.injEq, Fin.succ] at h0 h1 h2 h3
  change x 0 - x 1 = 0 at h0
  change x 1 - x 2 = 0 at h1
  change x 2 - x 3 = 0 at h2
  change x 2 + x 3 = 0 at h3
  have hx0 : x 0 = 0 := by linarith
  have hx1 : x 1 = 0 := by linarith
  have hx2 : x 2 = 0 := by linarith
  have hx3 : x 3 = 0 := by linarith
  ext i
  fin_cases i <;> first | exact hx0 | exact hx1 | exact hx2 | exact hx3

theorem rootsF4_annihilator {x : ModelSpace 4} (hx : ∀ i, ⟪rootsF4 i, x⟫ = 0) : x = 0 := by
  have h0 := hx ⟨0, by decide⟩
  have h1 := hx ⟨1, by decide⟩
  have h2 := hx ⟨2, by decide⟩
  have h3 := hx ⟨3, by decide⟩
  norm_num [rootsF4, coordinateVector, inner_sub_left,
    EuclideanSpace.inner_single_left, Fin.isValue, Fin.mk.injEq] at h0 h1 h2
  change ⟪(1 / 2 : ℝ) • (coordinateVector (0 : Fin 4) - coordinateVector 1 -
    coordinateVector 2 - coordinateVector 3), x⟫ = 0 at h3
  simp only [real_inner_smul_left, inner_sub_left] at h3
  norm_num [coordinateVector, EuclideanSpace.inner_single_left] at h3
  change x 1 - x 2 = 0 at h0
  change x 2 - x 3 = 0 at h1
  change x 3 = 0 at h2
  change x 0 - x 1 - x 2 - x 3 = 0 at h3
  have hx0 : x 0 = 0 := by linarith
  have hx1 : x 1 = 0 := by linarith
  have hx2 : x 2 = 0 := by linarith
  have hx3 : x 3 = 0 := by linarith
  ext i
  fin_cases i <;> first | exact hx0 | exact hx1 | exact hx2 | exact hx3

theorem rootsH4_annihilator {x : ModelSpace 4} (hx : ∀ i, ⟪rootsH4 i, x⟫ = 0) : x = 0 := by
  have h0 := hx ⟨0, by decide⟩
  have h1 := hx ⟨1, by decide⟩
  have h2 := hx ⟨2, by decide⟩
  have h3 := hx ⟨3, by decide⟩
  norm_num [rootsH4, coordinateVector, inner_add_left, inner_neg_left,
    real_inner_smul_left, EuclideanSpace.inner_single_left, Fin.isValue, Fin.mk.injEq]
    at h0 h1 h2 h3
  have hx1 : x 1 = 0 := by linarith
  rw [h0, hx1] at h1
  have hg : goldenRatio - 1 ≠ 0 := by
    intro he
    have hh := goldenRatio_sq
    have : goldenRatio = 1 := by linarith
    rw [this] at hh
    norm_num at hh
  have hx2 : x 2 = 0 := by
    apply (mul_eq_zero.mp (show (goldenRatio - 1) * x 2 = 0 by nlinarith)).resolve_left hg
  have hx3 : x (⟨3, by decide⟩ : Fin 4) = 0 := by
    apply (mul_eq_zero.mp (show (goldenRatio - 1) * x (⟨3, by decide⟩ : Fin 4) = 0 by
      rw [hx2] at h3
      nlinarith)).resolve_left hg
  ext i
  fin_cases i <;> first | exact h0 | exact hx1 | exact hx2 | exact hx3

theorem root_span_top_of_annihilator [FiniteDimensional ℝ E] {k : ℕ} (r : Fin k → E)
    (h : ∀ x : E, (∀ i, ⟪r i, x⟫ = 0) → x = 0) :
    Submodule.span ℝ (Set.range r) = ⊤ := by
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro x hx
  rw [Submodule.mem_bot]
  exact h x (fun i => hx (r i) (Submodule.subset_span (Set.mem_range_self i)))

theorem rootsB4_span : Submodule.span ℝ (Set.range rootsB4) = ⊤ :=
  root_span_top_of_annihilator rootsB4 (fun _ => rootsB4_annihilator)
theorem rootsD4_span : Submodule.span ℝ (Set.range rootsD4) = ⊤ :=
  root_span_top_of_annihilator rootsD4 (fun _ => rootsD4_annihilator)
theorem rootsF4_span : Submodule.span ℝ (Set.range rootsF4) = ⊤ :=
  root_span_top_of_annihilator rootsF4 (fun _ => rootsF4_annihilator)
theorem rootsH4_span : Submodule.span ℝ (Set.range rootsH4) = ⊤ :=
  root_span_top_of_annihilator rootsH4 (fun _ => rootsH4_annihilator)

theorem a4_seed_unique {J : Finset (Fin 4)} {x y : ModelSpace 5}
    (hx0 : (∑ i, x i) = 0) (hy0 : (∑ i, y i) = 0)
    (hx : WythoffSeed rootsA4 J x) (hy : WythoffSeed rootsA4 J y) : x = y := by
  have h (i : Fin 4) : x i.castSucc - x i.succ = y i.castSucc - y i.succ := by
    have hh := (hx i).trans (hy i).symm
    simpa [rootsA4, coordinateVector, inner_sub_left, EuclideanSpace.inner_single_left] using hh
  have h0 := h ⟨0, by decide⟩
  have h1 := h ⟨1, by decide⟩
  have h2 := h ⟨2, by decide⟩
  have h3 := h ⟨3, by decide⟩
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hx0 hy0
  change x 0 + (x 1 + (x 2 + (x 3 + x 4))) = 0 at hx0
  change y 0 + (y 1 + (y 2 + (y 3 + y 4))) = 0 at hy0
  change x 0 - x 1 = y 0 - y 1 at h0
  change x 1 - x 2 = y 1 - y 2 at h1
  change x 2 - x 3 = y 2 - y 3 at h2
  change x 3 - x 4 = y 3 - y 4 at h3
  have e0 : x 0 = y 0 := by linarith
  have e1 : x 1 = y 1 := by linarith
  have e2 : x 2 = y 2 := by linarith
  have e3 : x 3 = y 3 := by linarith
  have e4 : x 4 = y 4 := by linarith
  ext i
  fin_cases i <;> first | exact e0 | exact e1 | exact e2 | exact e3 | exact e4

variable {F : Type*} [PseudoMetricSpace F] {G : Type*} [PseudoMetricSpace G]

/-- An individual named Wythoff model represents only one congruence type,
even when its realizations use different ambient dimensions. -/
theorem namedWythoff4Model_unique {d : Fin 5} {m : Fin 15} {P : Set F} {Q : Set G}
    (hP : NamedWythoff4Model d m P) (hQ : NamedWythoff4Model d m Q) : Congruent P Q := by
  fin_cases d
  · obtain ⟨x, hx0, hx, hPx⟩ := hP
    obtain ⟨y, hy0, hy, hQy⟩ := hQ
    have he := a4_seed_unique hx0 hy0 hx hy
    subst y
    exact congruent_trans hPx (congruent_symm hQy)
  · obtain ⟨x, hx, hPx⟩ := hP
    obtain ⟨y, hy, hQy⟩ := hQ
    have he := wythoffSeed_unique_of_span_top rootsB4_span hx hy
    subst y
    exact congruent_trans hPx (congruent_symm hQy)
  · obtain ⟨x, hx, hPx⟩ := hP
    obtain ⟨y, hy, hQy⟩ := hQ
    have he := wythoffSeed_unique_of_span_top rootsD4_span hx hy
    subst y
    exact congruent_trans hPx (congruent_symm hQy)
  · obtain ⟨x, hx, hPx⟩ := hP
    obtain ⟨y, hy, hQy⟩ := hQ
    have he := wythoffSeed_unique_of_span_top rootsF4_span hx hy
    subst y
    exact congruent_trans hPx (congruent_symm hQy)
  · obtain ⟨x, hx, hPx⟩ := hP
    obtain ⟨y, hy, hQy⟩ := hQ
    have he := wythoffSeed_unique_of_span_top rootsH4_span hx hy
    subst y
    exact congruent_trans hPx (congruent_symm hQy)

end Uniform5.Composition
