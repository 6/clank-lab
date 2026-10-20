import Uniform5.CompositionTypeIICoherentNeighbors

/-! The six actual Type II fan vertices are distinct and exhaustive. -/
noncomputable section
namespace Uniform5.Composition
open Set

namespace TypeIIActualFanData
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
  (T : TypeIIActualFanData D v n)

noncomputable def points : Fin 6 → Space 5 :=
  ![T.base.a, T.base.b, T.base.x, T.base.y,
    T.lateral (finRotate D.length T.anti),
    T.lateral ((finRotate D.length).symm T.anti)]

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
  obtain ⟨h1a, h1b, h1x, h1y⟩ := hlat _ ht₁
  obtain ⟨h2a, h2b, h2x, h2y⟩ := hlat _ ht₂
  have h12 := (finRotate_three_orbit T.length_three T.anti).1
  have hz12 := D.cell_lateral_points_injective hG h12
    (T.lateral_mem _ ht₁) (T.lateral_mem _ ht₂) (T.lateral_outside _ ht₁)
  apply List.nodup_ofFn.mp
  change ([T.base.a, T.base.b, T.base.x, T.base.y,
    T.lateral (finRotate D.length T.anti),
    T.lateral ((finRotate D.length).symm T.anti)] : List (Space 5)).Nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, not_or, and_true, hab, hax, hay, hbx, hby, hxy,
    h1a.symm, h1b.symm, h1x.symm, h1y.symm,
    h2a.symm, h2b.symm, h2x.symm, h2y.symm, hz12]

theorem points_range_fan_neighbors (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hv : v ∈ G.extremePoints ℝ) :
    Set.range T.points = {w | ∃ j : Fin D.length, Edge (D.facet j) v w} := by
  ext w
  change w ∈ Set.range T.points ↔ ∃ j : Fin D.length, Edge (D.facet j) v w
  rw [T.fan_neighbors hP hG hn hv]
  simp [points, Set.mem_range, Fin.exists_fin_succ, eq_comm]
  tauto

end TypeIIActualFanData
end Uniform5.Composition
