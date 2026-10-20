import Uniform5.CompositionTypeIIIFanNeighbors

/-! The seven actual Type III fan vertices are distinct and exhaustive. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem finRotate_four_lateral_indices {m : ℕ} (hm : m = 4) (a : Fin m) :
    finRotate m a ≠ (finRotate m).symm a ∧
    finRotate m a ≠ finRotate m (finRotate m a) ∧
    (finRotate m).symm a ≠ finRotate m (finRotate m a) := by
  subst m
  revert a
  decide

namespace TypeIIIActualFanData
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
  (T : TypeIIIActualFanData D v n)

noncomputable def points : Fin 7 → Space 5 :=
  ![T.base.a, T.base.b, T.base.x, T.base.y,
    T.lateral (finRotate D.length T.anti),
    T.lateral ((finRotate D.length).symm T.anti),
    T.lateral (finRotate D.length (finRotate D.length T.anti))]

theorem points_injective (hG : PolygonFace P G n) (hn : 3 ≤ n) :
    Function.Injective T.points := by
  have hc : 0 < CaseB.chord n := CaseB.case_chord_pos (by exact_mod_cast hn)
  have hab : T.base.a ≠ T.base.b := by
    intro h; have hh := T.base.chord_ab; rw [h, dist_self] at hh; linarith
  have hax : T.base.a ≠ T.base.x := by
    intro h; have hh := T.base.side_ax; rw [h, dist_self] at hh; norm_num at hh
  have hay : T.base.a ≠ T.base.y := by
    intro h; have hh := T.base.diagonal_ay; rw [h, dist_self] at hh; nlinarith
  have hbx : T.base.b ≠ T.base.x := by
    intro h; have hh := T.base.diagonal_bx; rw [h, dist_self] at hh; nlinarith
  have hby : T.base.b ≠ T.base.y := by
    intro h; have hh := T.base.side_by; rw [h, dist_self] at hh; norm_num at hh
  have hxy : T.base.x ≠ T.base.y := by
    intro h; have hh := T.base.side_xy; rw [h, dist_self] at hh; norm_num at hh
  have hlat (t : Fin D.length) (ht : t ≠ T.anti) :
      T.lateral t ≠ T.base.a ∧ T.lateral t ≠ T.base.b ∧
      T.lateral t ≠ T.base.x ∧ T.lateral t ≠ T.base.y := by
    have haG := ((T.base.polygon_neighbors _).mpr (Or.inl rfl)).2.1.1
    have hbG := ((T.base.polygon_neighbors _).mpr (Or.inr rfl)).2.1.1
    have hxC := ((T.base.neighbors _).mpr (Or.inr (Or.inr (Or.inl rfl)))).2.1.1
    have hyC := ((T.base.neighbors _).mpr (Or.inr (Or.inr (Or.inr rfl)))).2.1.1
    refine ⟨fun he => T.lateral_outside t ht (he.symm ▸ haG),
      fun he => T.lateral_outside t ht (he.symm ▸ hbG), ?_, ?_⟩
    · exact D.cell_lateral_points_injective hG ht (T.lateral_mem t ht) hxC
        (T.lateral_outside t ht)
    · exact D.cell_lateral_points_injective hG ht (T.lateral_mem t ht) hyC
        (T.lateral_outside t ht)
  have ht₁ := (finRotate_ne_and_twice_ne D.length_ge T.anti).1
  have ht₂ := D.predecessor_ne T.anti
  have ht₃ := (finRotate_ne_and_twice_ne D.length_ge T.anti).2
  obtain ⟨h1a, h1b, h1x, h1y⟩ := hlat _ ht₁
  obtain ⟨h2a, h2b, h2x, h2y⟩ := hlat _ ht₂
  obtain ⟨h3a, h3b, h3x, h3y⟩ := hlat _ ht₃
  obtain ⟨h12, h13, h23⟩ := finRotate_four_lateral_indices T.length_four T.anti
  have hz12 := D.cell_lateral_points_injective hG h12
    (T.lateral_mem _ ht₁) (T.lateral_mem _ ht₂) (T.lateral_outside _ ht₁)
  have hz13 := D.cell_lateral_points_injective hG h13
    (T.lateral_mem _ ht₁) (T.lateral_mem _ ht₃) (T.lateral_outside _ ht₁)
  have hz23 := D.cell_lateral_points_injective hG h23
    (T.lateral_mem _ ht₂) (T.lateral_mem _ ht₃) (T.lateral_outside _ ht₂)
  apply List.nodup_ofFn.mp
  change ([T.base.a, T.base.b, T.base.x, T.base.y,
    T.lateral (finRotate D.length T.anti),
    T.lateral ((finRotate D.length).symm T.anti),
    T.lateral (finRotate D.length (finRotate D.length T.anti))] : List (Space 5)).Nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, not_or, and_true, hab, hax, hay, hbx, hby, hxy,
    h1a.symm, h1b.symm, h1x.symm, h1y.symm,
    h2a.symm, h2b.symm, h2x.symm, h2y.symm,
    h3a.symm, h3b.symm, h3x.symm, h3y.symm, hz12, hz13, hz23]

theorem points_range
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hv : v ∈ G.extremePoints ℝ) (hu : UniqueLargeFaceAt P v G) :
    Set.range T.points = (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ := by
  obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius hP.1
  rw [finitePolytope_unit_vertexFigure_extremePoints (uniform_finitePolytope hP.1)
    (hG.1.2.extremePoints_subset_extremePoints hv) _ (intrinsicRadius P) hs hP.2]
  ext w
  change w ∈ Set.range T.points ↔ Edge P v w
  rw [T.parent_neighbors classification3D classification4D N S hLIB hS1 hB2 hP hG hn hv hu]
  simp [points, Set.mem_range, Fin.exists_fin_succ, eq_comm]
  tauto

end TypeIIIActualFanData
end Uniform5.Composition
