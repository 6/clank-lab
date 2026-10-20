import Uniform5.CompositionPyramidFullGraph

/-! A square-pyramid chart has only its distinguished polygon edge
longer than square-root two. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem AntiprismPrismNeighborChart.long_edge_endpoints
    {K C G : Set E} {v u w : E} {n : ℕ}
    (D : AntiprismPrismNeighborChart K C G v n)
    (hK : UnitUniform 4 K) (hC : Facet K C) (hn : 3 ≤ n)
    (he : Edge (vertexFigure K v
      (vertexCentroid (vertices K (uniform_finitePolytope hK.1)))) u w)
    (hlong : Real.sqrt 2 < dist u w) :
    (u = D.base.a ∧ w = D.base.b) ∨ (u = D.base.b ∧ w = D.base.a) := by
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hax : dist D.base.a D.base.x ≤ Real.sqrt 2 := D.base.side_ax.le.trans h1
  have hby : dist D.base.b D.base.y ≤ Real.sqrt 2 := D.base.side_by.le.trans h1
  have hxy : dist D.base.x D.base.y ≤ Real.sqrt 2 := D.base.side_xy.le.trans h1
  have haz := D.apex_a.le
  have hbz := D.apex_b.le
  have hxz := D.apex_x.le
  have hyz := D.apex_y.le
  rcases (D.figure_edges hK hC hn u w).mp he with
    ⟨rfl, hw⟩ | ⟨rfl, hw⟩ | ⟨rfl, hw⟩ | ⟨rfl, hw⟩ | ⟨rfl, hw⟩
  · rcases hw with rfl | rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact (not_lt_of_ge hax hlong).elim
    · exact (not_lt_of_ge haz hlong).elim
  · rcases hw with rfl | rfl | rfl
    · exact Or.inr ⟨rfl, rfl⟩
    · exact (not_lt_of_ge hby hlong).elim
    · exact (not_lt_of_ge hbz hlong).elim
  · rcases hw with rfl | rfl | rfl
    · exact (not_lt_of_ge (by simpa only [dist_comm] using hax) hlong).elim
    · exact (not_lt_of_ge hxy hlong).elim
    · exact (not_lt_of_ge hxz hlong).elim
  · rcases hw with rfl | rfl | rfl
    · exact (not_lt_of_ge (by simpa only [dist_comm] using hby) hlong).elim
    · exact (not_lt_of_ge (by simpa only [dist_comm] using hxy) hlong).elim
    · exact (not_lt_of_ge hyz hlong).elim
  · rcases hw with rfl | rfl | rfl | rfl
    · exact (not_lt_of_ge (by simpa only [dist_comm] using haz) hlong).elim
    · exact (not_lt_of_ge (by simpa only [dist_comm] using hbz) hlong).elim
    · exact (not_lt_of_ge (by simpa only [dist_comm] using hxz) hlong).elim
    · exact (not_lt_of_ge (by simpa only [dist_comm] using hyz) hlong).elim

end Uniform5.Composition
