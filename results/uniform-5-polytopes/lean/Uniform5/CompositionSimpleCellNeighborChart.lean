import Uniform5.CompositionSimpleFacetNeighborCover

/-! A cell at a simple four-dimensional vertex has exactly one neighbor
beyond any two prescribed distinct neighbors in that cell. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem finitePolytope_simpleFacet_third_neighbor {K C : Set E} {v a b : E}
    (hK : FinitePolytope K) (hd : affineDimension K = 4)
    (hv : v ∈ K.extremePoints ℝ)
    (hfour : (geometricNeighbours K hK v).card = 4)
    (hC : Facet K C) (ha : Edge C v a) (hb : Edge C v b) (hab : a ≠ b) :
    ∃ z, z ≠ a ∧ z ≠ b ∧ ∀ w, Edge C v w ↔ w = a ∨ w = b ∨ w = z := by
  classical
  let F : FacesAt K v := ⟨⟨C, hC.1⟩, ha.1.1⟩
  let N : Finset E := (neighboursIn K hK v F).image Subtype.val
  have hmem (w : E) : w ∈ N ↔ Edge C v w := by
    constructor
    · rintro hw
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
      have huC := (mem_neighboursIn K hK v F u).mp hu
      exact (edge_face_iff hK hC.1 ha.1.1 huC).mp
        ((mem_geometricNeighbours K hK v u).mp u.property)
    · intro he
      have heK := (edge_face_iff hK hC.1 he.1.1 he.2.1.1).mpr he
      let u : geometricNeighbours K hK v := ⟨w, (mem_geometricNeighbours K hK v w).mpr heK⟩
      exact Finset.mem_image.mpr ⟨u, (mem_neighboursIn K hK v F u).mpr he.2.1.1, rfl⟩
  have hcard : N.card = 3 := by
    dsimp only [N]
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
    exact (finitePolytope_simpleVertex_facet_iff_three hK hd hv hfour F).mp hC
  have haN : a ∈ N := (hmem a).mpr ha
  have hbN : b ∈ N.erase a := Finset.mem_erase.mpr ⟨hab.symm, (hmem b).mpr hb⟩
  have hc : ((N.erase a).erase b).card = 1 := by
    rw [Finset.card_erase_of_mem hbN, Finset.card_erase_of_mem haN, hcard]
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hc
  have hzmem : z ∈ (N.erase a).erase b := by rw [hz]; simp
  have hza : z ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hzmem).2).1
  have hzb : z ≠ b := (Finset.mem_erase.mp hzmem).1
  have he : N = {a, b, z} := by
    calc
      N = insert a (N.erase a) := (Finset.insert_erase haN).symm
      _ = insert a (insert b ((N.erase a).erase b)) := by rw [Finset.insert_erase hbN]
      _ = {a, b, z} := by rw [hz]
  refine ⟨z, hza, hzb, ?_⟩
  intro w
  rw [← hmem, he]
  simp

/-- The two actual triangular cell figures at a simple vertex exhaust
the containing facet figure, with their common two vertices identified. -/
theorem finitePolytope_simpleVertex_two_triangle_neighbors {K A B : Set E}
    {v a b z w : E} (hK : FinitePolytope K) (hd : affineDimension K = 4)
    (hv : v ∈ K.extremePoints ℝ) (hfour : (geometricNeighbours K hK v).card = 4)
    (hA : Facet K A) (hB : Facet K B) (hne : A ≠ B)
    (hAN : ∀ t, Edge A v t ↔ t = a ∨ t = b ∨ t = z)
    (hBN : ∀ t, Edge B v t ↔ t = a ∨ t = b ∨ t = w) :
    ∀ t, Edge K v t ↔ t = a ∨ t = b ∨ t = z ∨ t = w := by
  have hva := ((hAN a).mpr (Or.inl rfl)).1.1
  have hvb := ((hBN a).mpr (Or.inl rfl)).1.1
  intro t
  constructor
  · intro he
    rcases finitePolytope_simpleVertex_two_facets_cover hK hd hv hfour hA hB hva hvb hne he with ht | ht
    · have hh := (hAN t).mp ((edge_face_iff hK hA.1 hva ht).mp he)
      tauto
    · have hh := (hBN t).mp ((edge_face_iff hK hB.1 hvb ht).mp he)
      tauto
  · intro ht
    have liftA (s : E) (hs : s = a ∨ s = b ∨ s = z) : Edge K v s := by
      have he := (hAN s).mpr hs
      exact (edge_face_iff hK hA.1 he.1.1 he.2.1.1).mpr he
    have liftB (s : E) (hs : s = a ∨ s = b ∨ s = w) : Edge K v s := by
      have he := (hBN s).mpr hs
      exact (edge_face_iff hK hB.1 he.1.1 he.2.1.1).mpr he
    rcases ht with ht | ht | ht | ht
    · exact liftA t (Or.inl ht)
    · exact liftA t (Or.inr (Or.inl ht))
    · exact liftA t (Or.inr (Or.inr ht))
    · exact liftB t (Or.inr (Or.inr ht))

end Uniform5.Composition
