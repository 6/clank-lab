import Uniform5.CompositionTypeIFanVertexSet

/-! Literal five- and six-point labels for the actual three- and
four-slot Type I fans. The index enumeration is checked in the kernel. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem finRotate_three_enumeration {m : ℕ} (hm : m = 3) (j i : Fin m) :
    i = j ∨ i = finRotate m j ∨ i = finRotate m (finRotate m j) := by
  subst m
  revert j i
  decide

theorem finRotate_three_closed {m : ℕ} (hm : m = 3) (j : Fin m) :
    finRotate m (finRotate m (finRotate m j)) = j := by
  subst m
  revert j
  decide

theorem finRotate_four_enumeration {m : ℕ} (hm : m = 4) (j i : Fin m) :
    i = j ∨ i = finRotate m j ∨ i = finRotate m (finRotate m j) ∨
      i = finRotate m (finRotate m (finRotate m j)) := by
  subst m
  revert j i
  decide

theorem finRotate_four_closed {m : ℕ} (hm : m = 4) (j : Fin m) :
    finRotate m (finRotate m (finRotate m (finRotate m j))) = j := by
  subst m
  revert j
  decide

namespace TypeIFanChart
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIFanChart D v n)

noncomputable def pairedFiveLabels (j : Fin D.length) : Fin 5 ↪ Space 5 := by
  have h01 := (finRotate_ne_and_twice_ne D.length_ge j).1
  have h02 := (finRotate_ne_and_twice_ne D.length_ge j).2
  have h12 := (finRotate_ne_and_twice_ne D.length_ge (finRotate D.length j)).1
  refine ⟨![T.a, T.b, T.lateral j, T.lateral (finRotate D.length j),
    T.lateral (finRotate D.length (finRotate D.length j))], ?_⟩
  intro i k h
  fin_cases i <;> fin_cases k
  all_goals
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons] at h
    first
      | rfl
      | exact (T.ab_ne h).elim
      | exact (T.ab_ne h.symm).elim
      | exact (T.lateral_ne_a _ h).elim
      | exact (T.lateral_ne_a _ h.symm).elim
      | exact (T.lateral_ne_b _ h).elim
      | exact (T.lateral_ne_b _ h.symm).elim
      | exact (h01 (T.lateral_injective h)).elim
      | exact (h01 (T.lateral_injective h).symm).elim
      | exact (h02 (T.lateral_injective h)).elim
      | exact (h02 (T.lateral_injective h).symm).elim
      | exact (h12 (T.lateral_injective h)).elim
      | exact (h12 (T.lateral_injective h).symm).elim


noncomputable def pairedSixLabels (hlen : D.length = 4) (j : Fin D.length) : Fin 6 ↪ Space 5 := by
  have h01 := (finRotate_ne_and_twice_ne D.length_ge j).1
  have h02 := (finRotate_ne_and_twice_ne D.length_ge j).2
  have h12 := (finRotate_ne_and_twice_ne D.length_ge (finRotate D.length j)).1
  have h13 := (finRotate_ne_and_twice_ne D.length_ge (finRotate D.length j)).2
  have h23 := (finRotate_ne_and_twice_ne D.length_ge (finRotate D.length (finRotate D.length j))).1
  have h03 : finRotate D.length (finRotate D.length (finRotate D.length j)) ≠ j := by
    intro he
    have hh := congrArg (finRotate D.length) he
    rw [finRotate_four_closed hlen] at hh
    exact h01 hh.symm
  refine ⟨![T.a, T.b, T.lateral j, T.lateral (finRotate D.length j),
    T.lateral (finRotate D.length (finRotate D.length j)),
    T.lateral (finRotate D.length (finRotate D.length (finRotate D.length j)))], ?_⟩
  intro i k h
  fin_cases i <;> fin_cases k
  all_goals
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons] at h
    first
      | rfl
      | exact (T.ab_ne h).elim
      | exact (T.ab_ne h.symm).elim
      | exact (T.lateral_ne_a _ h).elim
      | exact (T.lateral_ne_a _ h.symm).elim
      | exact (T.lateral_ne_b _ h).elim
      | exact (T.lateral_ne_b _ h.symm).elim
      | exact (h01 (T.lateral_injective h)).elim
      | exact (h01 (T.lateral_injective h).symm).elim
      | exact (h02 (T.lateral_injective h)).elim
      | exact (h02 (T.lateral_injective h).symm).elim
      | exact (h12 (T.lateral_injective h)).elim
      | exact (h12 (T.lateral_injective h).symm).elim
      | exact (h03 (T.lateral_injective h)).elim
      | exact (h03 (T.lateral_injective h).symm).elim
      | exact (h13 (T.lateral_injective h)).elim
      | exact (h13 (T.lateral_injective h).symm).elim
      | exact (h23 (T.lateral_injective h)).elim
      | exact (h23 (T.lateral_injective h).symm).elim


theorem pairedFiveLabels_mem_fan (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hvG : v ∈ G.extremePoints ℝ) (j : Fin D.length) (i : Fin 5) :
    T.pairedFiveLabels j i ∈ actualPolygonFanVertices hP D v := by
  rw [T.mem_fan_vertices hP hG hvG]
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨j, rfl⟩)
  · exact Or.inr (Or.inr ⟨finRotate D.length j, rfl⟩)
  · exact Or.inr (Or.inr ⟨finRotate D.length (finRotate D.length j), rfl⟩)

theorem pairedSixLabels_mem_fan (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hvG : v ∈ G.extremePoints ℝ) (hlen : D.length = 4) (j : Fin D.length) (i : Fin 6) :
    T.pairedSixLabels hlen j i ∈ actualPolygonFanVertices hP D v := by
  rw [T.mem_fan_vertices hP hG hvG]
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨j, rfl⟩)
  · exact Or.inr (Or.inr ⟨finRotate D.length j, rfl⟩)
  · exact Or.inr (Or.inr ⟨finRotate D.length (finRotate D.length j), rfl⟩)
  · exact Or.inr (Or.inr ⟨finRotate D.length (finRotate D.length (finRotate D.length j)), rfl⟩)

end TypeIFanChart
end Uniform5.Composition
