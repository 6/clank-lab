import Uniform5.CompositionWythoffConjugacy

/-! Exact reflection-word comparison of the D4 and B4 orbits on coordinate
hyperplanes. Every simulation below is an actual coordinate identity. -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem reflectionWord_append {k : ℕ} (r : Fin k → E) (u v : List (Fin k)) (x : E) :
    reflectionWord r (u ++ v) x = reflectionWord r u (reflectionWord r v x) := by
  induction u with
  | nil => rfl
  | cons i u ih => simp only [List.cons_append, reflectionWord, ih]

theorem reflectionOrbit_word_closed {k : ℕ} (r : Fin k → E) {x y : E}
    (hy : y ∈ reflectionOrbit r x) (w : List (Fin k)) :
    reflectionWord r w y ∈ reflectionOrbit r x := by
  obtain ⟨v, rfl⟩ := hy
  exact ⟨w ++ v, reflectionWord_append r w v x⟩

theorem reflectionOrbit_subset_of_invariant {k : ℕ} (r : Fin k → E) {x : E} {S : Set E}
    (hx : x ∈ S) (hS : ∀ i y, y ∈ S → mirrorReflection (r i) y ∈ S) :
    reflectionOrbit r x ⊆ S := by
  rintro y ⟨w, rfl⟩
  induction w with
  | nil => exact hx
  | cons i w ih => exact hS i _ ih

theorem b4_reflection_coordinates (i j : Fin 4) (x : ModelSpace 4) :
    mirrorReflection (rootsB4 i) x j =
      !![x (⟨1, by decide⟩ : Fin 4), x (⟨0, by decide⟩ : Fin 4), x (⟨2, by decide⟩ : Fin 4), x (⟨3, by decide⟩ : Fin 4);
         x (⟨0, by decide⟩ : Fin 4), x (⟨2, by decide⟩ : Fin 4), x (⟨1, by decide⟩ : Fin 4), x (⟨3, by decide⟩ : Fin 4);
         x (⟨0, by decide⟩ : Fin 4), x (⟨1, by decide⟩ : Fin 4), x (⟨3, by decide⟩ : Fin 4), x (⟨2, by decide⟩ : Fin 4);
         x (⟨0, by decide⟩ : Fin 4), x (⟨1, by decide⟩ : Fin 4), x (⟨2, by decide⟩ : Fin 4), -x (⟨3, by decide⟩ : Fin 4)] i j := by
  have e0 : x (⟨0, by decide⟩ : Fin 4) = x 0 := rfl
  have e1 : x (⟨1, by decide⟩ : Fin 4) = x 1 := rfl
  have e2 : x (⟨2, by decide⟩ : Fin 4) = x 2 := rfl
  have e3 : x (⟨3, by decide⟩ : Fin 4) = x 3 := rfl
  rw [mirrorReflection_formula, ← real_inner_self_eq_norm_sq, rootsB4_gram]
  fin_cases i <;> fin_cases j <;>
    norm_num [rootsB4, coordinateVector, inner_sub_left,
      EuclideanSpace.inner_single_left, EuclideanSpace.single_apply,
      Fin.isValue, Fin.mk.injEq, Fin.succ, PiLp.sub_apply, PiLp.smul_apply] <;>
    simp only [Fin.ext_iff] <;>
    simp only [e0, e1, e2, e3] <;> ring

theorem d4_reflection_coordinates (i j : Fin 4) (x : ModelSpace 4) :
    mirrorReflection (rootsD4 i) x j =
      !![x (⟨1, by decide⟩ : Fin 4), x (⟨0, by decide⟩ : Fin 4), x (⟨2, by decide⟩ : Fin 4), x (⟨3, by decide⟩ : Fin 4);
         x (⟨0, by decide⟩ : Fin 4), x (⟨2, by decide⟩ : Fin 4), x (⟨1, by decide⟩ : Fin 4), x (⟨3, by decide⟩ : Fin 4);
         x (⟨0, by decide⟩ : Fin 4), x (⟨1, by decide⟩ : Fin 4), x (⟨3, by decide⟩ : Fin 4), x (⟨2, by decide⟩ : Fin 4);
         x (⟨0, by decide⟩ : Fin 4), x (⟨1, by decide⟩ : Fin 4), -x (⟨3, by decide⟩ : Fin 4), -x (⟨2, by decide⟩ : Fin 4)] i j := by
  have e0 : x (⟨0, by decide⟩ : Fin 4) = x 0 := rfl
  have e1 : x (⟨1, by decide⟩ : Fin 4) = x 1 := rfl
  have e2 : x (⟨2, by decide⟩ : Fin 4) = x 2 := rfl
  have e3 : x (⟨3, by decide⟩ : Fin 4) = x 3 := rfl
  rw [mirrorReflection_formula, ← real_inner_self_eq_norm_sq, rootsD4_gram]
  fin_cases i <;> fin_cases j <;>
    norm_num [rootsD4, coordinateVector, inner_sub_left, inner_add_left,
      EuclideanSpace.inner_single_left, EuclideanSpace.single_apply,
      Fin.isValue, Fin.mk.injEq, Fin.succ, PiLp.sub_apply, PiLp.smul_apply] <;>
    simp only [Fin.ext_iff] <;> norm_num [Fin.instOfNat, Fin.ofNat'] <;>
    simp only [e0, e1, e2, e3] <;> ring

/-- Every D4 generator is a short B4 reflection word. -/
theorem d4_generator_is_b4_word (i : Fin 4) (x : ModelSpace 4) :
    ∃ w : List (Fin 4), reflectionWord rootsB4 w x = mirrorReflection (rootsD4 i) x := by
  fin_cases i
  · refine ⟨[(⟨0, by decide⟩ : Fin 4)], ?_⟩
    ext j
    fin_cases j <;> norm_num [reflectionWord, b4_reflection_coordinates, d4_reflection_coordinates]
  · refine ⟨[(⟨1, by decide⟩ : Fin 4)], ?_⟩
    ext j
    fin_cases j <;> norm_num [reflectionWord, b4_reflection_coordinates, d4_reflection_coordinates]
  · refine ⟨[(⟨2, by decide⟩ : Fin 4)], ?_⟩
    ext j
    fin_cases j <;> norm_num [reflectionWord, b4_reflection_coordinates, d4_reflection_coordinates]
  · refine ⟨[(⟨3, by decide⟩ : Fin 4), (⟨2, by decide⟩ : Fin 4), (⟨3, by decide⟩ : Fin 4)], ?_⟩
    ext j
    fin_cases j <;> norm_num [reflectionWord, b4_reflection_coordinates, d4_reflection_coordinates]

theorem d4_orbit_subset_b4 (x : ModelSpace 4) :
    reflectionOrbit rootsD4 x ⊆ reflectionOrbit rootsB4 x := by
  apply reflectionOrbit_subset_of_invariant
  · exact ⟨[], rfl⟩
  · intro i y hy
    obtain ⟨w, hw⟩ := d4_generator_is_b4_word i y
    rw [← hw]
    exact reflectionOrbit_word_closed rootsB4 hy w

/-- A zero coordinate is preserved by each D4 signed transposition. -/
theorem d4_reflection_has_zero (i : Fin 4) {x : ModelSpace 4} (hx : ∃ j, x j = 0) :
    ∃ j, mirrorReflection (rootsD4 i) x j = 0 := by
  obtain ⟨j, hj⟩ := hx
  fin_cases i <;> fin_cases j <;>
    first
    | exact ⟨(⟨0, by decide⟩ : Fin 4), by simpa [d4_reflection_coordinates] using hj⟩
    | exact ⟨(⟨1, by decide⟩ : Fin 4), by simpa [d4_reflection_coordinates] using hj⟩
    | exact ⟨(⟨2, by decide⟩ : Fin 4), by simpa [d4_reflection_coordinates] using hj⟩
    | exact ⟨(⟨3, by decide⟩ : Fin 4), by simpa [d4_reflection_coordinates] using hj⟩

/-- On a coordinate hyperplane, a single sign change can be implemented
by an even sign change, because the other sign is attached to zero. -/
theorem b4_terminal_is_d4_word {x : ModelSpace 4} (hx : ∃ j, x j = 0) :
    ∃ w : List (Fin 4), reflectionWord rootsD4 w x = mirrorReflection (rootsB4 (⟨3, by decide⟩ : Fin 4)) x := by
  obtain ⟨j, hj⟩ := hx
  fin_cases j
  · change x 0 = 0 at hj
    refine ⟨[(⟨0, by decide⟩ : Fin 4), (⟨1, by decide⟩ : Fin 4), (⟨2, by decide⟩ : Fin 4), (⟨3, by decide⟩ : Fin 4), (⟨1, by decide⟩ : Fin 4), (⟨0, by decide⟩ : Fin 4)], ?_⟩
    ext k
    fin_cases k <;> simp [reflectionWord, d4_reflection_coordinates, b4_reflection_coordinates, hj]
  · change x 1 = 0 at hj
    refine ⟨[(⟨1, by decide⟩ : Fin 4), (⟨2, by decide⟩ : Fin 4), (⟨3, by decide⟩ : Fin 4), (⟨1, by decide⟩ : Fin 4)], ?_⟩
    ext k
    fin_cases k <;> simp [reflectionWord, d4_reflection_coordinates, b4_reflection_coordinates, hj]
  · change x 2 = 0 at hj
    refine ⟨[(⟨2, by decide⟩ : Fin 4), (⟨3, by decide⟩ : Fin 4)], ?_⟩
    ext k
    fin_cases k <;> simp [reflectionWord, d4_reflection_coordinates, b4_reflection_coordinates, hj]
  · change x 3 = 0 at hj
    refine ⟨[], ?_⟩
    ext k
    fin_cases k <;> simp [reflectionWord, b4_reflection_coordinates, hj]

/-- Every B4 generator can be simulated at a point with a zero coordinate. -/
theorem b4_generator_is_d4_word (i : Fin 4) {x : ModelSpace 4} (hx : ∃ j, x j = 0) :
    ∃ w : List (Fin 4), reflectionWord rootsD4 w x = mirrorReflection (rootsB4 i) x := by
  fin_cases i
  · refine ⟨[(⟨0, by decide⟩ : Fin 4)], ?_⟩
    ext j
    fin_cases j <;> norm_num [reflectionWord, b4_reflection_coordinates, d4_reflection_coordinates]
  · refine ⟨[(⟨1, by decide⟩ : Fin 4)], ?_⟩
    ext j
    fin_cases j <;> norm_num [reflectionWord, b4_reflection_coordinates, d4_reflection_coordinates]
  · refine ⟨[(⟨2, by decide⟩ : Fin 4)], ?_⟩
    ext j
    fin_cases j <;> norm_num [reflectionWord, b4_reflection_coordinates, d4_reflection_coordinates]
  · exact b4_terminal_is_d4_word hx

/-- The two actual reflection orbits coincide on every coordinate hyperplane. -/
theorem d4_b4_orbit_eq {x : ModelSpace 4} (hx : ∃ j, x j = 0) :
    reflectionOrbit rootsD4 x = reflectionOrbit rootsB4 x := by
  apply Set.Subset.antisymm (d4_orbit_subset_b4 x)
  have hz : reflectionOrbit rootsD4 x ⊆ {y | ∃ j, y j = 0} :=
    reflectionOrbit_subset_of_invariant rootsD4 hx (fun i _ hy => d4_reflection_has_zero i hy)
  apply reflectionOrbit_subset_of_invariant
  · exact ⟨[], rfl⟩
  · intro i y hy
    obtain ⟨w, hw⟩ := b4_generator_is_d4_word i (hz hy)
    rw [← hw]
    exact reflectionOrbit_word_closed rootsD4 hy w

theorem d4_b4_hull_eq {x : ModelSpace 4} (hx : ∃ j, x j = 0) :
    WythoffHull rootsD4 x = WythoffHull rootsB4 x := by
  unfold WythoffHull
  rw [d4_b4_orbit_eq hx]

end Uniform5.Composition
