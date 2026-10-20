import Uniform5.CompositionWedgeInput
import Uniform5.CompositionTwoFanCover
import Uniform5.CompositionPolygonFanMembership

/-! At most two long figure-edge pairs imply coverage by two actual large
polygon faces. Endpoints identify whole polygon faces by planar incidence. -/
noncomputable section
namespace Uniform5.Composition
open Set

private theorem polygon_eq_of_neighbor_pair {P G H : Set (Space 5)} {n m : ℕ}
    (hG : PolygonFace P G n) (hH : PolygonFace P H m)
    {v a b x y : Space 5} (ha : Edge G v a) (hb : Edge G v b)
    (hx : Edge H v x) (hy : Edge H v y) (hxy : x ≠ y)
    (hp : Wedge.pair a b x y) : H = G := by
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact polygonFace_eq_of_common_neighbor_pair hH hG hx hy ha hb hxy
  · exact polygonFace_eq_of_common_neighbor_pair hH hG hx hy hb ha hxy

private theorem pair_same {a b c d x y : Space 5}
    (h : Wedge.pair a b c d) (h' : Wedge.pair a b x y) : Wedge.pair c d x y := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h'
  · exact h'.symm

/-- No third large polygon can hide behind one of the two protected pairs. -/
theorem twoLargeFacesCoverAt_of_two_long_pairs
    {P G H : Set (Space 5)} (hP : UnitUniform 5 P) {n m : ℕ}
    (hG : PolygonFace P G n) (hH : PolygonFace P H m) (hm : 17 ≤ m)
    {v : Space 5} (hvG : v ∈ G.extremePoints ℝ) (hvH : v ∈ H.extremePoints ℝ)
    (hne : G ≠ H) {a b c d : Space 5} (ha : Edge G v a) (hb : Edge G v b)
    (hbound : ∀ x y, Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y →
      CaseB.chord 17 ≤ dist x y → Wedge.pair a b x y ∨ Wedge.pair c d x y) :
    TwoLargeFacesCoverAt P v G H := by
  have hv := hG.1.2.extremePoints_subset_extremePoints hvG
  obtain ⟨x, y, hxy, hvx, hvy, _⟩ := unitUniform5_polygon_vertexFigure_edge hP hv hH hvH.1
  have hlong : CaseB.chord 17 ≤ dist x y := by
    rw [polygonFace_neighbor_chord hP hH hvx hvy hxy.2.2.1]
    exact CaseB.chord_mono (by norm_num) (by exact_mod_cast hm)
  have hsecond : Wedge.pair c d x y := by
    rcases hbound x y hxy hlong with h | h
    · exact (hne (polygon_eq_of_neighbor_pair hG hH ha hb hvx hvy hxy.2.2.1 h).symm).elim
    · exact h
  intro F k hF hk hvF
  obtain ⟨x', y', hxy', hvx', hvy', _⟩ := unitUniform5_polygon_vertexFigure_edge hP hv hF hvF.1
  have hl : CaseB.chord 17 ≤ dist x' y' := by
    rw [polygonFace_neighbor_chord hP hF hvx' hvy' hxy'.2.2.1]
    exact CaseB.chord_mono (by norm_num) (by exact_mod_cast hk)
  rcases hbound x' y' hxy' hl with h | h
  · exact Or.inl (polygon_eq_of_neighbor_pair hG hF ha hb hvx' hvy' hxy'.2.2.1 h)
  · exact Or.inr (polygon_eq_of_neighbor_pair hH hF hvx hvy hvx' hvy'
      hxy'.2.2.1 (pair_same hsecond h))

/-- The partner edge's endpoints lying in an actual facet put the entire
second polygon in that facet. -/
theorem partner_polygon_subset_of_long_pairs
    {P G H K : Set (Space 5)} (hP : UnitUniform 5 P) {n m : ℕ}
    (hG : PolygonFace P G n) (hH : PolygonFace P H m) (hm : 17 ≤ m)
    {v : Space 5} (hvG : v ∈ G.extremePoints ℝ) (hvH : v ∈ H.extremePoints ℝ)
    (hne : G ≠ H) {a b c d : Space 5} (ha : Edge G v a) (hb : Edge G v b)
    (hK : IsConvexFace P K) (hvK : v ∈ K) (hcK : c ∈ K) (hdK : d ∈ K)
    (hbound : ∀ x y, Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y →
      CaseB.chord 17 ≤ dist x y → Wedge.pair a b x y ∨ Wedge.pair c d x y) : H ⊆ K := by
  have hv := hG.1.2.extremePoints_subset_extremePoints hvG
  obtain ⟨x, y, hxy, hvx, hvy, _⟩ := unitUniform5_polygon_vertexFigure_edge hP hv hH hvH.1
  have hl : CaseB.chord 17 ≤ dist x y := by
    rw [polygonFace_neighbor_chord hP hH hvx hvy hxy.2.2.1]
    exact CaseB.chord_mono (by norm_num) (by exact_mod_cast hm)
  have hsecond : Wedge.pair c d x y := by
    rcases hbound x y hxy hl with h | h
    · exact (hne (polygon_eq_of_neighbor_pair hG hH ha hb hvx hvy hxy.2.2.1 h).symm).elim
    · exact h
  apply planar_face_subset_of_three_vertices hH.1 hK hH.2.1
    hvH hvx.2.1 hvy.2.1 hvx.2.2.1 hvy.2.2.1 hxy.2.2.1 hvK
  · rcases hsecond with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  · rcases hsecond with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption

end Uniform5.Composition
