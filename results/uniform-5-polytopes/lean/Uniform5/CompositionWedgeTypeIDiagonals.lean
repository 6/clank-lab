import Uniform5.CompositionWedgeTypeIRealization

/-! The exempt lateral diagonals in W are ruled out as parent edges by
actual planar incidence, independently of the computed distance tests. -/
noncomputable section
namespace Uniform5.Composition.Wedge.TypeIShape
open Set
variable {n : Parameter} {c : List Parameter} (S : TypeIShape n c)

theorem diagonal_not_edge {Q : Set (Space 5)} (hQ : Convex ℝ Q)
    (hpoints : Set.range S.x ⊆ Q)
    (hcycle : ∀ i, Edge Q (S.x i) (S.x (finRotate c.length i)))
    {p q : Space 5} (hd : S.diagonal p q) : ¬ Edge Q p q := by
  obtain ⟨i, j, _, hnext, hprev, rfl, rfl⟩ := hd
  let r := (finRotate c.length).symm i
  have hri : finRotate c.length r = i := (finRotate c.length).apply_symm_apply i
  let C := convexHull ℝ (Set.range S.x)
  have hfinite : FinitePolytope C := by
    refine ⟨Finset.univ.image S.x, ?_, ?_⟩
    · exact ⟨S.x i, Finset.mem_image.mpr ⟨i, by simp, rfl⟩⟩
    · simp [C]
  have hsub : C ⊆ Q := convexHull_min hpoints hQ
  have hmem (k : Fin c.length) : S.x k ∈ C := subset_convexHull ℝ _ (mem_range_self k)
  have hp : Edge Q (S.x i) (S.x r) := by
    have he := chart_edge_symm (hcycle r)
    simpa only [hri] using he
  have hdistinct : S.x r ≠ S.x (finRotate c.length i) := by
    intro he
    have hh := S.injective he
    apply (finRotate_ne_and_twice_ne S.length_ge r).2
    rw [hri, ← hh]
  apply finitePolytope_planar_subhull_diagonal_not_edge hfinite S.planar hsub
    (hmem i) (hmem r) (hmem _) (hmem j) hp (hcycle i) hdistinct
  · intro he
    exact hprev ((congrArg (finRotate c.length) (S.injective he)).trans hri)
  · intro he
    exact hnext (S.injective he).symm

end Uniform5.Composition.Wedge.TypeIShape
namespace Uniform5.Composition.TypeIFanChart
open Set
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIFanChart D v n)
variable {c : List Wedge.Parameter} {q : Fin D.length → ℕ}

theorem wedgeShape_cycle_edge (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 3 ≤ n) (hn4 : n ≠ 4) (hvG : v ∈ G.extremePoints ℝ)
    (hlen : D.length ≤ 5) (hq : ∀ i, 3 ≤ q i)
    (hmodel : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    (hcell : ∀ i : Fin D.length, Congruent (D.cell i) (polygonPrismModel n))
    (L : CyclicLabels (D := D) c q) (i : Fin c.length) :
    let S := T.wedgeShape hP hG hn hn4 hvG hlen hq hmodel hcell L
    Edge (vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1))))
      (S.x i) (S.x (finRotate c.length i)) := by
  change Edge _ (T.lateral (L.vertex i)) (T.lateral (L.vertex (finRotate c.length i)))
  apply T.parent_figure_edge hP hG hvG (L.facet i)
  · rcases L.incidence i with ⟨ha, _⟩ | ⟨_, ha⟩ <;> simp [ha]
  · rcases L.incidence i with ⟨_, hb⟩ | ⟨hb, _⟩ <;> simp [hb]
  · intro he
    exact (finRotate_ne_and_twice_ne (by rw [labels_length L]; exact D.length_ge) i).1
      (L.vertex.injective (T.lateral_injective he)).symm

theorem wedgeShape_diagonal_not_edge (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 3 ≤ n) (hn4 : n ≠ 4) (hvG : v ∈ G.extremePoints ℝ)
    (hlen : D.length ≤ 5) (hq : ∀ i, 3 ≤ q i)
    (hmodel : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    (hcell : ∀ i : Fin D.length, Congruent (D.cell i) (polygonPrismModel n))
    (L : CyclicLabels (D := D) c q) {p r : Space 5}
    (hd : (T.wedgeShape hP hG hn hn4 hvG hlen hq hmodel hcell L).diagonal p r) :
    ¬ Edge (vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) p r := by
  have hvP := hG.1.2.extremePoints_subset_extremePoints hvG
  obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius hP.1
  have hQ := finitePolytope_vertexFigure_of_positiveDimension
    (uniform_finitePolytope hP.1) hvP _ (intrinsicRadius P) hs hP.2
    (by rw [uniform_dimension hP.1]; norm_num)
  apply Wedge.TypeIShape.diagonal_not_edge _ (finitePolytope_convex hQ) _
    (T.wedgeShape_cycle_edge hP hG hn hn4 hvG hlen hq hmodel hcell L) hd
  rintro x ⟨i, rfl⟩
  exact (T.wedgeShape_cycle_edge hP hG hn hn4 hvG hlen hq hmodel hcell L i).1.1

end Uniform5.Composition.TypeIFanChart
