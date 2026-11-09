import ABC.Flow

/-! Basic facts about orbits of the ABC field. -/

open Set Metric Filter Topology

noncomputable section

namespace ABC

private lemma sq_sin_sub_le (a b : ℝ) : (Real.sin a - Real.sin b) ^ 2 ≤ (a - b) ^ 2 := by
  rw [← sq_abs, ← sq_abs (a - b)]
  exact pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sin_sub_sin_le a b) 2

private lemma sq_cos_sub_le (a b : ℝ) : (Real.cos a - Real.cos b) ^ 2 ≤ (a - b) ^ 2 := by
  rw [← sq_abs, ← sq_abs (a - b)]
  exact pow_le_pow_left₀ (abs_nonneg _) (Real.abs_cos_sub_cos_le a b) 2

private lemma abcField_dist_sq (ξ η : E 3) :
    dist (abcField ξ) (abcField η) ^ 2 ≤ (2 * dist ξ η) ^ 2 := by
  rw [mul_pow, EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq]
  simp only [Fin.sum_univ_three, Real.dist_eq, sq_abs, abcField]
  simp
  have h0 := sq_sin_sub_le (ξ 0) (η 0)
  have h1 := sq_sin_sub_le (ξ 1) (η 1)
  have h2 := sq_sin_sub_le (ξ 2) (η 2)
  have k0 := sq_cos_sub_le (ξ 0) (η 0)
  have k1 := sq_cos_sub_le (ξ 1) (η 1)
  have k2 := sq_cos_sub_le (ξ 2) (η 2)
  nlinarith [sq_nonneg (Real.sin (ξ 2) - Real.sin (η 2) - (Real.cos (ξ 1) - Real.cos (η 1))),
    sq_nonneg (Real.sin (ξ 0) - Real.sin (η 0) - (Real.cos (ξ 2) - Real.cos (η 2))),
    sq_nonneg (Real.sin (ξ 1) - Real.sin (η 1) - (Real.cos (ξ 0) - Real.cos (η 0)))]

theorem abcField_lipschitz : LipschitzWith 3 abcField := by
  refine LipschitzWith.of_dist_le_mul fun ξ η => ?_
  have h := abcField_dist_sq ξ η
  have h0 : 0 ≤ dist (abcField ξ) (abcField η) := dist_nonneg
  have h1 : 0 ≤ dist ξ η := dist_nonneg
  push_cast
  nlinarith

private lemma norm_abcField_le (x : E 3) : ‖abcField x‖ ≤ 4 := by
  have h : ‖abcField x‖ ^ 2 ≤ 4 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_three, abcField]
    nlinarith [Real.sin_sq_le_one (x 0), Real.sin_sq_le_one (x 1), Real.sin_sq_le_one (x 2),
      Real.cos_sq_le_one (x 0), Real.cos_sq_le_one (x 1), Real.cos_sq_le_one (x 2),
      sq_nonneg (Real.sin (x 2) - Real.cos (x 1)), sq_nonneg (Real.sin (x 0) - Real.cos (x 2)),
      sq_nonneg (Real.sin (x 1) - Real.cos (x 0))]
  nlinarith [norm_nonneg (abcField x)]

/-- A solution on `(-(n + 1), n + 1)`, by Picard–Lindelöf. -/
private lemma exists_local (ξ : E 3) (n : ℕ) : ∃ α : ℝ → E 3, α 0 = ξ ∧
    ∀ t ∈ Ioo (-(n + 1 : ℝ)) (n + 1), HasDerivAt α (abcField (α t)) t := by
  have h0 : (0 : ℝ) ∈ Icc (-(n + 1 : ℝ)) (n + 1) := ⟨by linarith, by linarith⟩
  have hpl : IsPicardLindelof (fun _ => abcField) (⟨0, h0⟩ : Icc (-(n + 1 : ℝ)) (n + 1)) ξ
      ⟨4 * (n + 1), by positivity⟩ 0 4 3 :=
    IsPicardLindelof.of_time_independent (fun x _ => norm_abcField_le x)
      abcField_lipschitz.lipschitzOnWith (by simp; rfl)
  obtain ⟨α, hα0, hα⟩ := IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ hpl
  exact ⟨α, hα0, fun t ht =>
    (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩

theorem exists_orbit (ξ : E 3) : ∃ γ, IsOrbit γ ∧ γ 0 = ξ := by
  choose α hα0 hα using exists_local ξ
  have hagree : ∀ n m : ℕ, n ≤ m → EqOn (α n) (α m) (Ioo (-(n + 1 : ℝ)) (n + 1)) := by
    intro n m hnm
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    exact ODE_solution_unique_of_mem_Ioo (v := fun _ => abcField) (s := fun _ => univ) (K := 3)
      (fun _ _ => abcField_lipschitz.lipschitzOnWith) (t₀ := 0)
      ⟨by linarith, by linarith⟩ (fun t ht => ⟨hα n t ht, trivial⟩)
      (fun t ht => ⟨hα m t ⟨by linarith [ht.1], by linarith [ht.2]⟩, trivial⟩)
      ((hα0 n).trans (hα0 m).symm)
  refine ⟨fun t => α ⌈|t|⌉₊ t, fun t => ?_, by simp [hα0]⟩
  have hN : |t| ≤ ⌈|t|⌉₊ := Nat.le_ceil _
  have hmem : Ioo (-(⌈|t|⌉₊ + 1 : ℝ)) (⌈|t|⌉₊ + 1) ∈ 𝓝 t :=
    Ioo_mem_nhds (by linarith [neg_abs_le t]) (by linarith [le_abs_self t])
  have heq : (fun s => α ⌈|s|⌉₊ s) =ᶠ[𝓝 t] α ⌈|t|⌉₊ := by
    filter_upwards [hmem] with s hs
    have hs' : |s| ≤ ⌈|s|⌉₊ := Nat.le_ceil _
    rcases le_total ⌈|s|⌉₊ ⌈|t|⌉₊ with h | h
    · exact hagree _ _ h ⟨by linarith [neg_abs_le s], by linarith [le_abs_self s]⟩
    · exact (hagree _ _ h hs).symm
  exact (hα _ t ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩).congr_of_eventuallyEq heq

theorem orbit_unique {γ₁ γ₂ : ℝ → E 3} (h₁ : IsOrbit γ₁) (h₂ : IsOrbit γ₂) {t₀ : ℝ}
    (h : γ₁ t₀ = γ₂ t₀) : γ₁ = γ₂ :=
  ODE_solution_unique_univ (v := fun _ => abcField) (s := fun _ => univ)
    (fun _ => abcField_lipschitz.lipschitzOnWith) (fun t => ⟨h₁ t, trivial⟩)
    (fun t => ⟨h₂ t, trivial⟩) h

theorem orbit_dist_le {γ₁ γ₂ : ℝ → E 3} (h₁ : IsOrbit γ₁) (h₂ : IsOrbit γ₂) (t : ℝ) :
    dist (γ₁ t) (γ₂ t) ≤ dist (γ₁ 0) (γ₂ 0) * Real.exp (3 * |t|) := by
  rcases le_or_gt 0 t with ht | ht
  · have := dist_le_of_trajectories_ODE (v := fun _ => abcField) (K := 3) (a := 0) (b := t)
      (fun _ => abcField_lipschitz)
      (HasDerivAt.continuousOn fun s _ => h₁ s) (fun s _ => (h₁ s).hasDerivWithinAt)
      (HasDerivAt.continuousOn fun s _ => h₂ s) (fun s _ => (h₂ s).hasDerivWithinAt) le_rfl t
      ⟨ht, le_rfl⟩
    simpa [abs_of_nonneg ht] using this
  · have hr : ∀ γ, IsOrbit γ → ∀ s,
        HasDerivAt (fun s => γ (-s)) (-abcField (γ (-s))) s := fun γ hγ s => by
      convert (hγ (-s)).scomp s (hasDerivAt_neg s) using 1 <;> simp [Function.comp_def]
    have hL : LipschitzWith 3 (fun x => -abcField x) :=
      LipschitzWith.of_dist_le_mul fun x y => by
        rw [dist_neg_neg]; exact abcField_lipschitz.dist_le_mul x y
    have := dist_le_of_trajectories_ODE (v := fun _ x => -abcField x) (K := 3) (a := 0)
      (b := -t) (f := fun s => γ₁ (-s)) (g := fun s => γ₂ (-s)) (fun _ => hL)
      (HasDerivAt.continuousOn fun s _ => hr γ₁ h₁ s)
      (fun s _ => (hr γ₁ h₁ s).hasDerivWithinAt)
      (HasDerivAt.continuousOn fun s _ => hr γ₂ h₂ s)
      (fun s _ => (hr γ₂ h₂ s).hasDerivWithinAt) le_rfl (-t) ⟨by linarith, le_rfl⟩
    simpa [abs_of_neg ht] using this

theorem isOrbit_comp_add {γ : ℝ → E 3} (h : IsOrbit γ) (c : ℝ) :
    IsOrbit (fun t => γ (t + c)) := fun t => by
  convert (h (t + c)).scomp t ((hasDerivAt_id t).add_const c) using 1 <;>
    simp [Function.comp_def]

private lemma abcField_add_lattice (x : E 3) (i : Fin 3) (m : ℤ) :
    abcField (x + (2 * Real.pi * m) • ev i) = abcField x := by
  have hs : ∀ a : ℝ, Real.sin (a + 2 * Real.pi * m) = Real.sin a := fun a => by
    rw [show 2 * Real.pi * m = m * (2 * Real.pi) by ring, Real.sin_add_int_mul_two_pi]
  have hc : ∀ a : ℝ, Real.cos (a + 2 * Real.pi * m) = Real.cos a := fun a => by
    rw [show 2 * Real.pi * m = m * (2 * Real.pi) by ring, Real.cos_add_int_mul_two_pi]
  fin_cases i <;> simp [abcField, hs, hc]

theorem isOrbit_add_lattice {γ : ℝ → E 3} (h : IsOrbit γ) (i : Fin 3) (m : ℤ) :
    IsOrbit (fun t => γ t + (2 * Real.pi * m) • ev i) := fun t => by
  rw [abcField_add_lattice]
  exact (h t).add_const _

end ABC
