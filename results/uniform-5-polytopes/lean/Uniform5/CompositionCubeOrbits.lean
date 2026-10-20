import Uniform5.CompositionD4B4Orbit
import Uniform5.CompositionFacetModelUnique

/-! Exact B3/B4 cube orbits from adjacent exchanges and coordinate sign flips. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical
open scoped RealInnerProductSpace

noncomputable def halfCubeCorners (n : ℕ) : Set (Space n) :=
  {x | ∀ i, x i = -(1 / 2 : ℝ) ∨ x i = 1 / 2}

/-- Coordinate flips generate every half-coordinate corner; preservation
of the corner predicate supplies the reverse orbit inclusion. -/
theorem reflectionOrbit_halfCube {n k : ℕ} (r : Fin k → Space n)
    (hpres : ∀ i x, x ∈ halfCubeCorners n → mirrorReflection (r i) x ∈ halfCubeCorners n)
    (hflip : ∀ i : Fin n, ∃ w : List (Fin k), ∀ x : Space n, ∀ j,
      reflectionWord r w x j = if j = i then -x j else x j) :
    reflectionOrbit r (fun _ => (1 / 2 : ℝ)) = halfCubeCorners n := by
  apply Subset.antisymm
  · exact reflectionOrbit_subset_of_invariant r (fun _ => Or.inr rfl) hpres
  · have hgenerate (s : Finset (Fin n)) :
        ∃ y ∈ reflectionOrbit r (fun _ => (1 / 2 : ℝ)),
          ∀ j, y j = if j ∈ s then -(1 / 2 : ℝ) else 1 / 2 := by
      induction s using Finset.induction_on with
      | empty =>
        refine ⟨fun _ => (1 / 2 : ℝ), ⟨[], rfl⟩, ?_⟩
        simp
      | @insert i s hi ih =>
        obtain ⟨y, hy, he⟩ := ih
        obtain ⟨w, hw⟩ := hflip i
        refine ⟨reflectionWord r w y, reflectionOrbit_word_closed r hy w, ?_⟩
        intro j
        rw [hw, he]
        by_cases hji : j = i
        · subst j; simp [hi]
        · simp [hji, Finset.mem_insert]
    intro x hx
    obtain ⟨y, hy, he⟩ := hgenerate (Finset.univ.filter (fun j => x j = -(1 / 2 : ℝ)))
    have hxy : y = x := by
      ext j
      rw [he]
      rcases hx j with h | h <;> norm_num [h]
    rwa [hxy] at hy


theorem b3_reflection_coordinates (i j : Fin 3) (x : ModelSpace 3) :
    mirrorReflection (rootsB3 i) x j =
      !![x (⟨1, by decide⟩ : Fin 3), x (⟨0, by decide⟩ : Fin 3), x (⟨2, by decide⟩ : Fin 3); x (⟨0, by decide⟩ : Fin 3), x (⟨2, by decide⟩ : Fin 3), x (⟨1, by decide⟩ : Fin 3); x (⟨0, by decide⟩ : Fin 3), x (⟨1, by decide⟩ : Fin 3), -x (⟨2, by decide⟩ : Fin 3)] i j := by
  have e0 : x (⟨0, by decide⟩ : Fin 3) = x 0 := rfl
  have e1 : x (⟨1, by decide⟩ : Fin 3) = x 1 := rfl
  have e2 : x (⟨2, by decide⟩ : Fin 3) = x 2 := rfl
  rw [mirrorReflection_formula, ← real_inner_self_eq_norm_sq, rootsB3_gram]
  fin_cases i <;> fin_cases j <;>
    norm_num [rootsB3, coordinateVector, inner_sub_left,
      EuclideanSpace.inner_single_left, EuclideanSpace.single_apply,
      Fin.isValue, Fin.mk.injEq, Fin.succ, PiLp.sub_apply, PiLp.smul_apply] <;>
    simp only [e0, e1, e2] <;> ring

noncomputable def b3SignFlipWord : Fin 3 → List (Fin 3) :=
  ![[(⟨0, by decide⟩ : Fin 3), (⟨1, by decide⟩ : Fin 3), (⟨2, by decide⟩ : Fin 3), (⟨1, by decide⟩ : Fin 3), (⟨0, by decide⟩ : Fin 3)], [(⟨1, by decide⟩ : Fin 3), (⟨2, by decide⟩ : Fin 3), (⟨1, by decide⟩ : Fin 3)], [(⟨2, by decide⟩ : Fin 3)]]

noncomputable def b4SignFlipWord : Fin 4 → List (Fin 4) :=
  ![[(⟨0, by decide⟩ : Fin 4), (⟨1, by decide⟩ : Fin 4), (⟨2, by decide⟩ : Fin 4), (⟨3, by decide⟩ : Fin 4), (⟨2, by decide⟩ : Fin 4), (⟨1, by decide⟩ : Fin 4), (⟨0, by decide⟩ : Fin 4)], [(⟨1, by decide⟩ : Fin 4), (⟨2, by decide⟩ : Fin 4), (⟨3, by decide⟩ : Fin 4), (⟨2, by decide⟩ : Fin 4), (⟨1, by decide⟩ : Fin 4)], [(⟨2, by decide⟩ : Fin 4), (⟨3, by decide⟩ : Fin 4), (⟨2, by decide⟩ : Fin 4)], [(⟨3, by decide⟩ : Fin 4)]]

theorem b3SignFlipWord_coordinates (i j : Fin 3) (x : Space 3) :
    reflectionWord rootsB3 (b3SignFlipWord i) x j = if j = i then -x j else x j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [b3SignFlipWord, reflectionWord, b3_reflection_coordinates]

theorem b4SignFlipWord_coordinates (i j : Fin 4) (x : Space 4) :
    reflectionWord rootsB4 (b4SignFlipWord i) x j = if j = i then -x j else x j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [b4SignFlipWord, reflectionWord, b4_reflection_coordinates]

theorem b3_reflection_halfCube (i : Fin 3) (x : Space 3) (hx : x ∈ halfCubeCorners 3) :
    mirrorReflection (rootsB3 i) x ∈ halfCubeCorners 3 := by
  have hn (j : Fin 3) : -x j = -(1 / 2 : ℝ) ∨ -x j = 1 / 2 := by
    rcases hx j with h | h <;> rw [h] <;> norm_num
  intro j
  rw [b3_reflection_coordinates]
  fin_cases i <;> fin_cases j <;> norm_num <;>
    first | exact hx (⟨0, by decide⟩ : Fin 3) | exact hx (⟨1, by decide⟩ : Fin 3) | exact hx (⟨2, by decide⟩ : Fin 3) | simpa only [neg_inj] using hn (⟨2, by decide⟩ : Fin 3)

theorem b4_reflection_halfCube (i : Fin 4) (x : Space 4) (hx : x ∈ halfCubeCorners 4) :
    mirrorReflection (rootsB4 i) x ∈ halfCubeCorners 4 := by
  have hn (j : Fin 4) : -x j = -(1 / 2 : ℝ) ∨ -x j = 1 / 2 := by
    rcases hx j with h | h <;> rw [h] <;> norm_num
  intro j
  rw [b4_reflection_coordinates]
  fin_cases i <;> fin_cases j <;> norm_num <;>
    first | exact hx (⟨0, by decide⟩ : Fin 4) | exact hx (⟨1, by decide⟩ : Fin 4) | exact hx (⟨2, by decide⟩ : Fin 4) | exact hx (⟨3, by decide⟩ : Fin 4) | simpa only [neg_inj] using hn (⟨3, by decide⟩ : Fin 4)

theorem cubeCorner3_orbit : reflectionOrbit rootsB3 cubeCorner3 = halfCubeCorners 3 :=
  reflectionOrbit_halfCube rootsB3 b3_reflection_halfCube
    (fun i => ⟨b3SignFlipWord i, fun x j => b3SignFlipWord_coordinates i j x⟩)

theorem cubeCorner4_orbit : reflectionOrbit rootsB4 cubeCorner4 = halfCubeCorners 4 :=
  reflectionOrbit_halfCube rootsB4 b4_reflection_halfCube
    (fun i => ⟨b4SignFlipWord i, fun x j => b4SignFlipWord_coordinates i j x⟩)

end Uniform5.Composition
