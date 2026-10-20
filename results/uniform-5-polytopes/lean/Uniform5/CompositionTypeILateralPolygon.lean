import Uniform5.CompositionTypeIFanRays
import Uniform5.CompositionTypeIFanEdges
import Uniform5.CompositionPlanarSubhullEdges

/-! The actual Type I lateral vertices form a genuine planar polygon.
The plane is derived from the transverse space and common axial height;
its cycle edges are inherited from actual tetrahedral figure facets. -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem affineDimension_ge_two_of_three_extreme {C : Set E} {a b c : E}
    (ha : a ∈ C.extremePoints ℝ) (hb : b ∈ C.extremePoints ℝ)
    (hc : c ∈ C.extremePoints ℝ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    2 ≤ affineDimension C := by
  have hai : AffineIndependent ℝ ![a,b,c] :=
    affineIndependent_iff_not_collinear_set.mpr (fun h => by
      rcases collinear_extreme_triple ha hb hc h with h | h | h
      · exact hab h
      · exact hac h
      · exact hbc h)
  have hd := (affineIndependent_iff_finrank_vectorSpan_eq ℝ ![a,b,c]
    (show Fintype.card (Fin 3) = 2 + 1 by decide)).mp hai
  have hsub : Set.range ![a,b,c] ⊆ C := by
    rintro x ⟨i, rfl⟩
    fin_cases i
    · exact ha.1
    · exact hb.1
    · exact hc.1
  have hm := Submodule.finrank_mono (vectorSpan_mono ℝ hsub)
  rw [hd] at hm
  unfold affineDimension Uniform5.affineDimension
  rw [direction_affineSpan]
  exact hm

namespace TypeIFanChart
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIFanChart D v n)

def lateralHull : Set (Space 5) := convexHull ℝ (Set.range T.lateral)

theorem lateralHull_finite : FinitePolytope T.lateralHull := by
  let i : Fin D.length := ⟨0, by have := D.length_ge; omega⟩
  refine ⟨Finset.univ.image T.lateral, ⟨T.lateral i, Finset.mem_image.mpr ⟨i, by simp, rfl⟩⟩, ?_⟩
  simp [lateralHull]

theorem lateral_parent_extreme (hP : UnitUniform 5 P) (i : Fin D.length) :
    T.lateral i ∈ P.extremePoints ℝ := by
  have he := (T.cell_neighbors i (T.lateral i)).mpr (Or.inr (Or.inr rfl))
  exact (D.cell_face i).2.extremePoints_subset_extremePoints he.2.1

theorem lateralHull_subset (hP : UnitUniform 5 P) : T.lateralHull ⊆ P := by
  apply convexHull_min _ (finitePolytope_convex (uniform_finitePolytope hP.1))
  rintro x ⟨i, rfl⟩
  exact (T.lateral_parent_extreme hP i).1

theorem lateralHull_extremePoints (hP : UnitUniform 5 P) :
    T.lateralHull.extremePoints ℝ = Set.range T.lateral := by
  apply Subset.antisymm extremePoints_convexHull_subset
  rintro x ⟨i, rfl⟩
  refine ⟨subset_convexHull ℝ _ (mem_range_self i), ?_⟩
  intro a ha b hb hab
  exact (T.lateral_parent_extreme hP i).2
    (T.lateralHull_subset hP ha) (T.lateralHull_subset hP hb) hab

/-- The two-dimensional affine hull is forced by the actual cell-ray
normal space and the common nonzero axial height. -/
theorem lateralHull_dimension (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 3 ≤ n) (hn4 : n ≠ 4) (hvG : v ∈ G.extremePoints ℝ)
    (q : Fin D.length → ℕ) (hq : ∀ i, 3 ≤ q i)
    (hmodel : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    (hcell : ∀ i : Fin D.length, Congruent (D.cell i) (polygonPrismModel n)) :
    affineDimension T.lateralHull = 2 := by
  let S := (affineSpan ℝ G).directionᗮ
  let W := polygonParentOffset hP hG
  let i₀ : Fin D.length := ⟨0, by have := D.length_ge; omega⟩
  have hr (i : Fin D.length) := T.lateral_eq_normalizedCellRay hP hG hn hn4 hvG
    i (hq i) (hmodel i) (hcell i)
  have hS (i : Fin D.length) : T.lateral i - v ∈ S := by
    rw [hr i]
    exact (D.normalizedCellRay_mem_orthogonal hP hG i).2
  have hW : W ∈ S := (D.normalizedCellRay_mem_orthogonal hP hG i₀).1
  have hh (i : Fin D.length) : ⟪T.lateral i - v, W⟫ = 1 / 2 := by
    rw [hr i]
    exact (D.prism_normalizedCellRay hP hG i (hcell i)).2
  have hWne : W ≠ 0 := by
    intro he
    have hi := hh i₀
    rw [he, inner_zero_right] at hi
    norm_num at hi
  let K := vectorSpan ℝ (Set.range T.lateral)
  have hKS : K ≤ S := by
    dsimp [K]
    rw [vectorSpan_eq_span_vsub_set_right ℝ (mem_range_self i₀)]
    apply Submodule.span_le.mpr
    rintro z ⟨x, ⟨i, rfl⟩, rfl⟩
    have hs := S.sub_mem (hS i) (hS i₀)
    simpa only [vsub_eq_sub, sub_sub_sub_cancel_right] using hs
  have hzero : ∀ z ∈ K, ⟪z, W⟫ = 0 := by
    have hker : K ≤ LinearMap.ker (innerSL ℝ W).toLinearMap := by
      dsimp [K]
      rw [vectorSpan_eq_span_vsub_set_right ℝ (mem_range_self i₀)]
      apply Submodule.span_le.mpr
      rintro z ⟨x, ⟨i, rfl⟩, rfl⟩
      change ⟪W, T.lateral i - T.lateral i₀⟫ = 0
      rw [real_inner_comm, show T.lateral i - T.lateral i₀ =
        (T.lateral i - v) - (T.lateral i₀ - v) by abel,
        inner_sub_left, hh i, hh i₀, sub_self]
    intro z hz
    exact (real_inner_comm _ _).trans (hker hz)
  have hlt : K < S := lt_of_le_of_ne hKS (by
    intro he
    have hh := hzero W (he.symm ▸ hW)
    rw [inner_self_eq_zero] at hh
    exact hWne hh)
  have hdim := Submodule.finrank_lt_finrank_of_lt hlt
  have hSd : Module.finrank ℝ S = 3 := ActualPolygonCycle.polygon_normal_finrank hG
  have hupper : affineDimension T.lateralHull ≤ 2 := by
    change Module.finrank ℝ (affineSpan ℝ (convexHull ℝ (Set.range T.lateral))).direction ≤ 2
    rw [affineSpan_convexHull, direction_affineSpan]
    change Module.finrank ℝ K ≤ 2
    omega
  let i₁ : Fin D.length := ⟨1, by have := D.length_ge; omega⟩
  let i₂ : Fin D.length := ⟨2, by have := D.length_ge; omega⟩
  have hex (i : Fin D.length) : T.lateral i ∈ T.lateralHull.extremePoints ℝ := by
    rw [T.lateralHull_extremePoints hP]
    exact mem_range_self i
  have hlower := affineDimension_ge_two_of_three_extreme (hex i₀) (hex i₁) (hex i₂)
    (fun he => by have hh := congrArg Fin.val (T.lateral_injective he); norm_num [i₀, i₁] at hh)
    (fun he => by have hh := congrArg Fin.val (T.lateral_injective he); norm_num [i₀, i₂] at hh)
    (fun he => by have hh := congrArg Fin.val (T.lateral_injective he); norm_num [i₁, i₂] at hh)
  omega

theorem lateralHull_subset_figure (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hvG : v ∈ G.extremePoints ℝ) :
    T.lateralHull ⊆ vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) := by
  have hvP := hG.1.2.extremePoints_subset_extremePoints hvG
  obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius hP.1
  have hQ := finitePolytope_vertexFigure_of_positiveDimension
    (uniform_finitePolytope hP.1) hvP _ (intrinsicRadius P) hs hP.2
    (by rw [uniform_dimension hP.1]; norm_num)
  apply convexHull_min _ (finitePolytope_convex hQ)
  rintro x ⟨i, rfl⟩
  exact (T.parent_figure_edge hP hG hvG i (by simp) (by simp)
    (T.lateral_ne_a i)).1.1

/-- Consecutive lateral pairs are actual edges of the lateral polygon. -/
theorem lateralHull_cycle_edge (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hvG : v ∈ G.extremePoints ℝ) (i : Fin D.length) :
    Edge T.lateralHull (T.lateral i) (T.lateral (finRotate D.length i)) := by
  have he := T.parent_figure_edge hP hG hvG i
    (show T.lateral i ∈ ({T.a,T.b,T.lateral i,T.lateral (finRotate D.length i)} : Set (Space 5)) by simp)
    (show T.lateral (finRotate D.length i) ∈
      ({T.a,T.b,T.lateral i,T.lateral (finRotate D.length i)} : Set (Space 5)) by simp)
    (fun he => (finRotate_ne_and_twice_ne D.length_ge i).1 (T.lateral_injective he).symm)
  exact edge_restrict_convex_subset (convex_convexHull ℝ _)
    (T.lateralHull_subset_figure hP hG hvG)
    (subset_convexHull ℝ _ (mem_range_self i))
    (subset_convexHull ℝ _ (mem_range_self (finRotate D.length i))) he

/-- A nonconsecutive lateral pair is not an edge of the actual vertex
figure. Planar neighbor exhaustion replaces a chosen crossing witness. -/
theorem lateral_diagonal_not_parent_edge (hP : UnitUniform 5 P)
    (hG : PolygonFace P G n) (hvG : v ∈ G.extremePoints ℝ)
    (hd : affineDimension T.lateralHull = 2) (i j : Fin D.length)
    (hn : finRotate D.length i ≠ j) (hp : finRotate D.length j ≠ i) :
    ¬ Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) (T.lateral i) (T.lateral j) := by
  let r := (finRotate D.length).symm i
  have hri : finRotate D.length r = i := (finRotate D.length).apply_symm_apply i
  have hnext : Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))))
      (T.lateral i) (T.lateral (finRotate D.length i)) :=
    T.parent_figure_edge hP hG hvG i (by simp) (by simp)
      (fun he => (finRotate_ne_and_twice_ne D.length_ge i).1 (T.lateral_injective he).symm)
  have hprev : Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) (T.lateral i) (T.lateral r) := by
    apply chart_edge_symm
    exact T.parent_figure_edge hP hG hvG r (by simp) (by simp [hri])
      (fun he => (finRotate_ne_and_twice_ne D.length_ge r).1
        (hri.trans (T.lateral_injective he).symm))
  have hdistinct : T.lateral r ≠ T.lateral (finRotate D.length i) := by
    intro he
    have hh := T.lateral_injective he
    apply (finRotate_ne_and_twice_ne D.length_ge r).2
    rw [hri, ← hh]
  apply finitePolytope_planar_subhull_diagonal_not_edge T.lateralHull_finite hd
    (T.lateralHull_subset_figure hP hG hvG)
    (subset_convexHull ℝ _ (mem_range_self i))
    (subset_convexHull ℝ _ (mem_range_self r))
    (subset_convexHull ℝ _ (mem_range_self (finRotate D.length i)))
    (subset_convexHull ℝ _ (mem_range_self j)) hprev hnext hdistinct
  · intro he
    exact hp ((congrArg (finRotate D.length) (T.lateral_injective he)).trans hri)
  · intro he
    exact hn (T.lateral_injective he).symm

end TypeIFanChart
end Uniform5.Composition
