import Uniform5.CompositionPlanarNeighbors
import Uniform5.CompositionUniformFaces

/-! Edge lists of actual planar and pyramidal figure charts. These use
convex incidence and the proved separation lemma, not a diagram premise. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem chart_edge_symm {P : Set E} {v w : E} (h : Edge P v w) : Edge P w v :=
  ⟨h.2.1, h.1, h.2.2.1.symm, by simpa only [segment_symm] using h.2.2.2⟩

/-- A unit pair in a convex subset of a unit-uniform polytope is an
actual exposed edge when its endpoints are original extreme vertices. -/
theorem unitUniform_convex_subset_unit_pair_edge {P Q : Set E} {n : ℕ}
    (hP : UnitUniform (n + 3) P) (hQ : Convex ℝ Q) (hQP : Q ⊆ P)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q)
    (hxP : x ∈ P.extremePoints ℝ) (hyP : y ∈ P.extremePoints ℝ)
    (hxy : dist x y = 1) : Edge Q x y := by
  have he := (unitUniform_edge_iff_dist_one hP hxP hyP).mpr hxy
  refine ⟨?_, ?_, he.2.2.1, he.2.2.2.mono hQP (hQ.segment_subset hx hy)⟩
  · exact ⟨hx, fun a ha b hb hab => hxP.2 (hQP ha) (hQP hb) hab⟩
  · exact ⟨hy, fun a ha b hb hab => hyP.2 (hQP ha) (hQP hb) hab⟩

/-- Four known cycle edges exhaust a planar quadrilateral chart. No
diagonal is separately declared absent. -/
theorem planar_quadrilateral_chart_neighbors {Q : Set E} (hQ : FinitePolytope Q)
    (hd : affineDimension Q = 2) {a b x y : E}
    (hab : Edge Q a b) (hax : Edge Q a x) (hxy : Edge Q x y) (hby : Edge Q b y)
    (hbx : b ≠ x) (hay : a ≠ y) :
    (∀ z, Edge Q a z ↔ z = b ∨ z = x) ∧
    (∀ z, Edge Q b z ↔ z = a ∨ z = y) ∧
    (∀ z, Edge Q x z ↔ z = a ∨ z = y) ∧
    (∀ z, Edge Q y z ↔ z = b ∨ z = x) := by
  exact ⟨finitePolytope_planar_neighbors hQ hd hab hax hbx,
    finitePolytope_planar_neighbors hQ hd (chart_edge_symm hab) hby hay,
    finitePolytope_planar_neighbors hQ hd (chart_edge_symm hax) hxy hay,
    finitePolytope_planar_neighbors hQ hd (chart_edge_symm hby) (chart_edge_symm hxy) hbx⟩

/-- In a three-polytope with a quadrilateral base and one remaining
vertex, minimum degree forces each base vertex to be joined to that
remaining vertex. This supplies actual pyramid edges from the vertex
list, the actual base face, and its already proved planar edge list. -/
theorem pyramid_apex_edge_of_base_neighbors {Q B : Set E}
    (hQ : FinitePolytope Q) (hd : affineDimension Q = 3)
    (hB : IsConvexFace Q B) {v a b z : E}
    (hv : v ∈ B.extremePoints ℝ)
    (hbase : ∀ w, Edge B v w → w = a ∨ w = b)
    (hvertices : ∀ w ∈ Q.extremePoints ℝ, w ∈ B ∨ w = z) : Edge Q v z := by
  classical
  by_contra hz
  have hvQ := hB.2.extremePoints_subset_extremePoints hv
  have hlower := finitePolytope_neighbour_card_lower hQ hvQ (by rw [hd]; norm_num)
  have hsub : geometricNeighbours Q hQ v ⊆ {a, b} := by
    intro w hw
    have he := (mem_geometricNeighbours Q hQ v w).mp hw
    rcases hvertices w he.2.1 with hwB | rfl
    · have hb := (edge_face_iff hQ hB hv.1 hwB).mp he
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hbase w hb
    · exact False.elim (hz he)
  have hu := Finset.card_le_card hsub
  have hp : ({a, b} : Finset E).card ≤ 2 := by
    rcases (Finset.card_pair_eq_one_or_two (a := a) (b := b)) with h | h <;> omega
  rw [hd] at hlower
  omega

/-- Three successive edges and the complete four-vertex list determine
the fourth edge of a planar convex quadrilateral. -/
theorem planar_quadrilateral_close_path {Q : Set E} (hQ : FinitePolytope Q)
    (hd : affineDimension Q = 2) {a b x y : E}
    (hvertices : Q.extremePoints ℝ = {a, b, x, y})
    (hax : Edge Q a x) (hxy : Edge Q x y) (hby : Edge Q b y)
    (hab : a ≠ b) (hbx : b ≠ x) : Edge Q a b := by
  classical
  have hy := finitePolytope_planar_neighbors hQ hd (chart_edge_symm hxy)
    (chart_edge_symm hby) hbx.symm
  by_contra hn
  have hlo := finitePolytope_neighbour_card_lower hQ hax.1 (by rw [hd]; norm_num)
  have hsub : geometricNeighbours Q hQ a ⊆ {x} := by
    intro z hz
    have he := (mem_geometricNeighbours Q hQ a z).mp hz
    have hv := he.2.1
    rw [hvertices] at hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact (he.2.2.1 rfl).elim
    · exact (hn he).elim
    · simp
    · rcases (hy a).mp (chart_edge_symm he) with heq | heq
      · exact (hax.2.2.1 heq).elim
      · exact (hab heq).elim
  have hhi := Finset.card_le_card hsub
  rw [Finset.card_singleton] at hhi
  rw [hd] at hlo
  omega

/-- A three-dimensional polytope with four vertices has every possible
edge. Minimum degree suffices, independently of any metric chart. -/
theorem tetrahedron_edge_of_four_vertices {Q : Set E}
    (hQ : FinitePolytope Q) (hd : affineDimension Q = 3)
    {a b c d : E} (hvertices : Q.extremePoints ℝ = {a, b, c, d})
    (ha : a ∈ Q.extremePoints ℝ) (hab : a ≠ b) : Edge Q a b := by
  classical
  by_contra hn
  have hlo := finitePolytope_neighbour_card_lower hQ ha (by rw [hd]; norm_num)
  have hsub : geometricNeighbours Q hQ a ⊆ {c, d} := by
    intro z hz
    have he := (mem_geometricNeighbours Q hQ a z).mp hz
    have hv := he.2.1
    rw [hvertices] at hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact (he.2.2.1 rfl).elim
    · exact (hn he).elim
    · simp
    · simp
  have hhi := Finset.card_le_card hsub
  have hp : ({c, d} : Finset E).card ≤ 2 := by
    rcases (Finset.card_pair_eq_one_or_two (a := c) (b := d)) with h | h <;> omega
  rw [hd] at hlo
  omega

/-- The complete graph description of a genuine four-vertex
three-polytope follows from its dimension and vertex list. -/
theorem tetrahedron_complete_graph {Q : Set E}
    (hQ : FinitePolytope Q) (hd : affineDimension Q = 3)
    {a b c d : E} (hvertices : Q.extremePoints ℝ = {a, b, c, d})
    {u w : E} (hu : u ∈ Q.extremePoints ℝ) (hw : w ∈ Q.extremePoints ℝ) :
    Edge Q u w ↔ u ≠ w := by
  constructor
  · exact fun he => he.2.2.1
  · intro hne
    have hu' := hvertices ▸ hu
    have hw' := hvertices ▸ hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu' hw'
    rcases hu' with rfl | rfl | rfl | rfl <;>
      rcases hw' with rfl | rfl | rfl | rfl
    all_goals first
      | exact (hne rfl).elim
      | apply tetrahedron_edge_of_four_vertices hQ hd (c := a) (d := b) _ hu hne
        all_goals rw [hvertices] <;> ext z <;> simp only [mem_insert_iff, mem_singleton_iff] <;> tauto
      | apply tetrahedron_edge_of_four_vertices hQ hd (c := a) (d := c) _ hu hne
        all_goals rw [hvertices] <;> ext z <;> simp only [mem_insert_iff, mem_singleton_iff] <;> tauto
      | apply tetrahedron_edge_of_four_vertices hQ hd (c := a) (d := d) _ hu hne
        all_goals rw [hvertices] <;> ext z <;> simp only [mem_insert_iff, mem_singleton_iff] <;> tauto
      | apply tetrahedron_edge_of_four_vertices hQ hd (c := b) (d := c) _ hu hne
        all_goals rw [hvertices] <;> ext z <;> simp only [mem_insert_iff, mem_singleton_iff] <;> tauto
      | apply tetrahedron_edge_of_four_vertices hQ hd (c := b) (d := d) _ hu hne
        all_goals rw [hvertices] <;> ext z <;> simp only [mem_insert_iff, mem_singleton_iff] <;> tauto
      | apply tetrahedron_edge_of_four_vertices hQ hd (c := c) (d := d) _ hu hne
        all_goals rw [hvertices] <;> ext z <;> simp only [mem_insert_iff, mem_singleton_iff] <;> tauto

/-- An actual quadrilateral-based pyramid has precisely its base edges
and the apex edges. The apex edges are derived from minimum degree. -/
theorem pyramid_base_vertex_neighbors {Q B : Set E}
    (hQ : FinitePolytope Q) (hd : affineDimension Q = 3)
    (hB : IsConvexFace Q B) {v a b z : E}
    (hv : v ∈ B.extremePoints ℝ)
    (hbase : ∀ w, Edge B v w ↔ w = a ∨ w = b)
    (hvertices : ∀ w ∈ Q.extremePoints ℝ, w ∈ B ∨ w = z) :
    ∀ w, Edge Q v w ↔ w = a ∨ w = b ∨ w = z := by
  have hz := pyramid_apex_edge_of_base_neighbors hQ hd hB hv
    (fun w hw => (hbase w).mp hw) hvertices
  intro w
  constructor
  · intro he
    rcases hvertices w he.2.1 with hw | rfl
    · have hb := (hbase w).mp ((edge_face_iff hQ hB hv.1 hw).mp he)
      rcases hb with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · have he := (hbase w).mpr (Or.inl rfl)
      exact (edge_face_iff hQ hB hv.1 he.2.1.1).mpr he
    · have he := (hbase w).mpr (Or.inr rfl)
      exact (edge_face_iff hQ hB hv.1 he.2.1.1).mpr he
    · exact hz

end Uniform5.Composition
