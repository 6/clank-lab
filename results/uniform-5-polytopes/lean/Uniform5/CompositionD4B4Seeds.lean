import Uniform5.CompositionD4B4Orbit

/-! Signed seed equations for the seven D4 masks with equal fork bits,
and their B4 counterparts with the terminal bit unringed. -/
noncomputable section
namespace Uniform5.Composition
open scoped RealInnerProductSpace

theorem d4_b4_root_eq {i : Fin 4} (hi : i ≠ 3) : rootsD4 i = rootsB4 i := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact (hi rfl).elim

theorem d4_fork_norm_eq : ‖rootsD4 3‖ = ‖rootsD4 2‖ := by
  change ‖rootsD4 (⟨3, by decide⟩ : Fin 4)‖ = ‖rootsD4 (⟨2, by decide⟩ : Fin 4)‖
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    rootsD4_gram, rootsD4_gram]
  norm_num

theorem d4_fork_inner (x : ModelSpace 4) :
    ⟪rootsD4 3, x⟫ = ⟪rootsD4 2, x⟫ + 2 * x 3 := by
  change ⟪coordinateVector (2 : Fin 4) + coordinateVector 3, x⟫ =
    ⟪coordinateVector (2 : Fin 4) - coordinateVector 3, x⟫ + 2 * x 3
  simp only [inner_add_left, inner_sub_left]
  simp only [coordinateVector, EuclideanSpace.inner_single_left]
  norm_num
  ring

theorem b4_terminal_inner (x : ModelSpace 4) : ⟪rootsB4 3, x⟫ = x 3 := by
  change ⟪coordinateVector (3 : Fin 4), x⟫ = x 3
  simp [coordinateVector, EuclideanSpace.inner_single_left]

theorem d4_seed_fork_zero {J : Finset (Fin 4)} (hJ : 2 ∈ J ↔ 3 ∈ J)
    {x : ModelSpace 4} (hx : WythoffSeed rootsD4 J x) : x 3 = 0 := by
  have h2 := hx 2
  have h3 := hx 3
  rw [d4_fork_inner, d4_fork_norm_eq] at h3
  simp only [← hJ] at h3
  linarith

/-- Equal fork bits are precisely the chamber slice on which D4 and B4
have the same signed seed, after erasing the B4 terminal ring. -/
theorem d4_b4_seed_iff {J : Finset (Fin 4)} (hJ : 2 ∈ J ↔ 3 ∈ J)
    {x : ModelSpace 4} :
    WythoffSeed rootsD4 J x ↔ WythoffSeed rootsB4 (J.erase 3) x := by
  classical
  constructor
  · intro hx i
    have hz := d4_seed_fork_zero hJ hx
    by_cases hi : i = 3
    · subst i
      rw [b4_terminal_inner, hz]
      simp
    · rw [← d4_b4_root_eq hi]
      simpa only [Finset.mem_erase, ne_eq, hi, not_false_eq_true, true_and] using hx i
  · intro hx i
    have hz : x 3 = 0 := by
      have h := hx 3
      simpa only [b4_terminal_inner, Finset.not_mem_erase, if_false] using h
    by_cases hi : i = 3
    · subst i
      rw [d4_fork_inner, hz, mul_zero, add_zero, d4_fork_norm_eq]
      have h := hx 2
      rw [← d4_b4_root_eq (by decide : (2 : Fin 4) ≠ 3)] at h
      simpa [hJ] using h
    · rw [d4_b4_root_eq hi]
      simpa only [Finset.mem_erase, ne_eq, hi, not_false_eq_true, true_and] using hx i

variable {E : Type*} [PseudoMetricSpace E]

theorem d4_b4_named_fork_iff {m n : Fin 15}
    (hfork : 2 ∈ libraryRingSet m ↔ 3 ∈ libraryRingSet m)
    (hmask : (libraryRingSet m).erase 3 = libraryRingSet n) (P : Set E) :
    NamedWythoff4Model 2 m P ↔ NamedWythoff4Model 1 n P := by
  constructor
  · rintro ⟨x, hx, hcongr⟩
    have hz := d4_seed_fork_zero hfork hx
    have hs := (d4_b4_seed_iff hfork).mp hx
    rw [hmask] at hs
    refine ⟨x, hs, ?_⟩
    rwa [d4_b4_hull_eq ⟨3, hz⟩] at hcongr
  · rintro ⟨x, hx, hcongr⟩
    rw [← hmask] at hx
    have hs := (d4_b4_seed_iff hfork).mpr hx
    have hz := d4_seed_fork_zero hfork hs
    refine ⟨x, hs, ?_⟩
    rwa [d4_b4_hull_eq ⟨3, hz⟩]

end Uniform5.Composition
