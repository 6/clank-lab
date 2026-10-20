import Uniform5.CompositionD4Triality

/-! The F4 half-root reflection is D4 triality. On its fixed hyperplane
intersected with a coordinate hyperplane, the B4 and F4 orbit hulls agree. -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace


theorem f4_terminal_inner (x : ModelSpace 4) :
    ⟪rootsF4 3, x⟫ = (x 0 - x 1 - x 2 - x 3) / 2 := by
  change ⟪(1 / 2 : ℝ) • (coordinateVector (0 : Fin 4) - coordinateVector 1 -
    coordinateVector 2 - coordinateVector 3), x⟫ = _
  simp only [real_inner_smul_left, inner_sub_left]
  simp [coordinateVector, EuclideanSpace.inner_single_left]
  ring

theorem f4_terminal_apply (x : ModelSpace 4) :
    mirrorReflection (rootsF4 3) x = d4Triality x := by
  have hn : ‖rootsF4 (⟨3, by decide⟩ : Fin 4)‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, rootsF4_gram]
    norm_num
  have e0 : x (⟨0, by decide⟩ : Fin 4) = x 0 := rfl
  have e1 : x (⟨1, by decide⟩ : Fin 4) = x 1 := rfl
  have e2 : x (⟨2, by decide⟩ : Fin 4) = x 2 := rfl
  have e3 : x (⟨3, by decide⟩ : Fin 4) = x 3 := rfl
  change mirrorReflection (rootsF4 (⟨3, by decide⟩ : Fin 4)) x = d4Triality x
  have hi : ⟪rootsF4 (⟨3, by decide⟩ : Fin 4), x⟫ =
      (x 0 - x 1 - x 2 - x 3) / 2 := f4_terminal_inner x
  rw [mirrorReflection_formula, hn, hi]
  ext j
  fin_cases j <;>
    norm_num [d4Triality, d4TrialityLinear, rootsF4, coordinateVector,
      EuclideanSpace.single_apply, PiLp.sub_apply, PiLp.smul_apply,
      Fin.isValue, Fin.mk.injEq, Fin.succ] <;>
    simp only [Fin.ext_iff] <;> norm_num [Fin.instOfNat, Fin.ofNat'] <;>
    simp only [e0, e1, e2, e3] <;> ring

theorem f4_reflection_coordinates (i j : Fin 4) (x : ModelSpace 4) :
    mirrorReflection (rootsF4 i) x j =
      !![x (⟨0, by decide⟩ : Fin 4), x (⟨2, by decide⟩ : Fin 4), x (⟨1, by decide⟩ : Fin 4), x (⟨3, by decide⟩ : Fin 4);
         x (⟨0, by decide⟩ : Fin 4), x (⟨1, by decide⟩ : Fin 4), x (⟨3, by decide⟩ : Fin 4), x (⟨2, by decide⟩ : Fin 4);
         x (⟨0, by decide⟩ : Fin 4), x (⟨1, by decide⟩ : Fin 4), x (⟨2, by decide⟩ : Fin 4), -x (⟨3, by decide⟩ : Fin 4);
         (x (⟨0, by decide⟩ : Fin 4) + x (⟨1, by decide⟩ : Fin 4) + x (⟨2, by decide⟩ : Fin 4) + x (⟨3, by decide⟩ : Fin 4)) / 2,
         (x (⟨0, by decide⟩ : Fin 4) + x (⟨1, by decide⟩ : Fin 4) - x (⟨2, by decide⟩ : Fin 4) - x (⟨3, by decide⟩ : Fin 4)) / 2,
         (x (⟨0, by decide⟩ : Fin 4) - x (⟨1, by decide⟩ : Fin 4) + x (⟨2, by decide⟩ : Fin 4) - x (⟨3, by decide⟩ : Fin 4)) / 2,
         (x (⟨0, by decide⟩ : Fin 4) - x (⟨1, by decide⟩ : Fin 4) - x (⟨2, by decide⟩ : Fin 4) + x (⟨3, by decide⟩ : Fin 4)) / 2] i j := by
  fin_cases i
  · exact b4_reflection_coordinates (⟨1, by decide⟩ : Fin 4) j x
  · exact b4_reflection_coordinates (⟨2, by decide⟩ : Fin 4) j x
  · exact b4_reflection_coordinates (⟨3, by decide⟩ : Fin 4) j x
  · change mirrorReflection (rootsF4 3) x j = _
    rw [f4_terminal_apply]
    fin_cases j <;> rfl

theorem b4_generator_is_f4_word (i : Fin 4) (x : ModelSpace 4) :
    ∃ w : List (Fin 4), reflectionWord rootsF4 w x = mirrorReflection (rootsB4 i) x := by
  have hF (y : ModelSpace 4) : mirrorReflection (rootsF4 (⟨3, by decide⟩ : Fin 4)) y =
      d4Triality y := f4_terminal_apply y
  have hmid (y : ModelSpace 4) :
      mirrorReflection (rootsF4 (⟨2, by decide⟩ : Fin 4))
        (mirrorReflection (rootsF4 (⟨1, by decide⟩ : Fin 4))
          (mirrorReflection (rootsF4 (⟨2, by decide⟩ : Fin 4)) y)) =
      mirrorReflection (rootsD4 (⟨3, by decide⟩ : Fin 4)) y := by
    ext j
    fin_cases j <;> norm_num [f4_reflection_coordinates, d4_reflection_coordinates]
  fin_cases i
  · refine ⟨[(⟨3, by decide⟩ : Fin 4), ⟨2, by decide⟩, ⟨1, by decide⟩,
      ⟨2, by decide⟩, ⟨3, by decide⟩], ?_⟩
    simp only [reflectionWord, hF, hmid]
    rw [mirrorReflection_isometry]
    have hr : d4Triality (rootsD4 (⟨3, by decide⟩ : Fin 4)) =
        rootsB4 (⟨0, by decide⟩ : Fin 4) := by
      simpa only [Equiv.swap_apply_right] using d4Triality_roots (⟨3, by decide⟩ : Fin 4)
    have hinv : d4Triality (d4Triality x) = x := d4TrialityLinear_involutive x
    rw [hr, hinv]
  · refine ⟨[(⟨0, by decide⟩ : Fin 4)], ?_⟩
    simp only [reflectionWord,
      show rootsF4 (⟨0, by decide⟩ : Fin 4) = rootsB4 (⟨1, by decide⟩ : Fin 4) from rfl]
  · refine ⟨[(⟨1, by decide⟩ : Fin 4)], ?_⟩
    simp only [reflectionWord,
      show rootsF4 (⟨1, by decide⟩ : Fin 4) = rootsB4 (⟨2, by decide⟩ : Fin 4) from rfl]
  · refine ⟨[(⟨2, by decide⟩ : Fin 4)], ?_⟩
    simp only [reflectionWord,
      show rootsF4 (⟨2, by decide⟩ : Fin 4) = rootsB4 (⟨3, by decide⟩ : Fin 4) from rfl]

theorem b4_orbit_subset_f4 (x : ModelSpace 4) :
    reflectionOrbit rootsB4 x ⊆ reflectionOrbit rootsF4 x := by
  apply reflectionOrbit_subset_of_invariant
  · exact ⟨[], rfl⟩
  · intro i y hy
    obtain ⟨w, hw⟩ := b4_generator_is_f4_word i y
    rw [← hw]
    exact reflectionOrbit_word_closed rootsF4 hy w

/-- Triality fixing the seed makes the additional F4 generator preserve
its D4 orbit, which equals the B4 orbit because one coordinate vanishes. -/
theorem b4_f4_orbit_eq {x : ModelSpace 4} (hz : x 3 = 0) (ht : d4Triality x = x) :
    reflectionOrbit rootsB4 x = reflectionOrbit rootsF4 x := by
  apply Set.Subset.antisymm (b4_orbit_subset_f4 x)
  have himage : d4Triality '' reflectionOrbit rootsB4 x = reflectionOrbit rootsB4 x := by
    rw [← d4_b4_orbit_eq ⟨3, hz⟩]
    have hr (i : Fin 4) : d4Triality (rootsD4 i) =
        (1 : ℝ) • rootsD4 (Equiv.swap (0 : Fin 4) 3 i) := by simpa using d4Triality_roots i
    rw [reflectionOrbit_conjugacy rootsD4 rootsD4 d4Triality (Equiv.swap 0 3)
      (fun _ => 1) (fun _ => one_ne_zero) hr, ht]
  apply reflectionOrbit_subset_of_invariant
  · exact ⟨[], rfl⟩
  · intro i y hy
    fin_cases i
    · exact reflectionOrbit_word_closed rootsB4 hy [(⟨1, by decide⟩ : Fin 4)]
    · exact reflectionOrbit_word_closed rootsB4 hy [(⟨2, by decide⟩ : Fin 4)]
    · exact reflectionOrbit_word_closed rootsB4 hy [(⟨3, by decide⟩ : Fin 4)]
    · change mirrorReflection (rootsF4 3) y ∈ _
      rw [f4_terminal_apply]
      rw [← himage]
      exact ⟨y, hy, rfl⟩

theorem b4_f4_hull_eq {x : ModelSpace 4} (hz : x 3 = 0) (ht : d4Triality x = x) :
    WythoffHull rootsB4 x = WythoffHull rootsF4 x := by
  unfold WythoffHull
  rw [b4_f4_orbit_eq hz ht]

end Uniform5.Composition
