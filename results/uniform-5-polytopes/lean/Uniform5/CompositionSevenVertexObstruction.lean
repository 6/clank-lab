import Uniform5.CompositionFacetSystemGeneral

/-! The existing seven-vertex Case B obstruction applies to the actual
graph of any four-dimensional finite polytope, after an exact labeling. -/
noncomputable section
namespace Uniform5.CaseB.FacetSystem
open Finset
variable {V W F : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

noncomputable def reindex (G : FacetSystem V F) (e : W ≃ V) : FacetSystem W F where
  edge v w := G.edge (e v) (e w)
  edge_symm := G.edge_symm
  edge_irrefl v := G.edge_irrefl (e v)
  vertices f := (G.vertices f).map e.symm.toEmbedding

@[simp] theorem reindex_mem_vertices (G : FacetSystem V F) (e : W ≃ V)
    (f : F) (v : W) : v ∈ (G.reindex e).vertices f ↔ e v ∈ G.vertices f := by
  simp [reindex]

theorem reindex_neighbours (G : FacetSystem V F) (e : W ≃ V) (v : W) :
    (G.reindex e).neighbours v = (G.neighbours (e v)).map e.symm.toEmbedding := by
  ext w
  simp [mem_neighbours, reindex]

theorem reindex_facetNeighbours (G : FacetSystem V F) (e : W ≃ V) (f : F) (v : W) :
    (G.reindex e).facetNeighbours f v =
      (G.facetNeighbours f (e v)).map e.symm.toEmbedding := by
  ext w
  simp [mem_facetNeighbours, reindex_mem_vertices, reindex]

theorem Laws.reindex {G : FacetSystem V F} (L : G.Laws) (e : W ≃ V) :
    (G.reindex e).Laws := by
  refine ⟨?_, ?_, ?_⟩
  · intro f v hv
    rw [reindex_facetNeighbours, card_map]
    exact L.min_degree f (e v) ((reindex_mem_vertices G e f v).mp hv)
  · intro f v hv hd
    rw [reindex_neighbours, card_map] at hd
    rw [reindex_facetNeighbours, card_map]
    exact L.simple_degree f (e v) ((reindex_mem_vertices G e f v).mp hv) hd
  · intro v hd s hs hcard
    rw [reindex_neighbours, card_map] at hd
    have hs' : s.map e.toEmbedding ⊆ G.neighbours (e v) := by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := mem_map.mp hz
      exact (mem_neighbours G).mpr ((mem_neighbours (G.reindex e)).mp (hs hw))
    obtain ⟨f, hv, he⟩ := L.three_subset (e v) hd (s.map e.toEmbedding) hs'
      (by simpa using hcard)
    refine ⟨f, (reindex_mem_vertices G e f v).mpr hv, ?_⟩
    rw [reindex_facetNeighbours, he, map_map]
    simp

end Uniform5.CaseB.FacetSystem

namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A literal labeling of all actual vertices and their actual edges by
the type-III single-fan graph contradicts the general convex incidence laws. -/
theorem finitePolytope_seven_vertex_graph_impossible {V : Set E}
    (hV : FinitePolytope V) (hd : affineDimension V = 4)
    (p : Fin 7 → E) (hp : Function.Injective p)
    (hvertices : Set.range p = V.extremePoints ℝ)
    (hgraph : ∀ i j, Edge V (p i) (p j) ↔ j ∈ CaseB.s1iiiNeighbours i) : False := by
  classical
  let e : Fin 7 ≃ vertices V hV := Equiv.ofBijective
    (fun i => ⟨p i, (mem_vertices hV _).mpr (hvertices ▸ mem_range_self i)⟩) (by
      constructor
      · intro i j h
        exact hp (congrArg Subtype.val h)
      · intro x
        obtain ⟨i, hi⟩ := hvertices.symm ▸ (mem_vertices hV x).mp x.property
        exact ⟨i, Subtype.ext hi⟩)
  let G := actualFacetSystem V hV
  apply CaseB.s1_type_iii_impossible (G.reindex e)
    ((actualFacetSystem_general_laws hV hd).reindex e)
  intro i
  ext j
  rw [CaseB.FacetSystem.mem_neighbours]
  change Edge V (p i) (p j) ↔ j ∈ CaseB.s1iiiNeighbours i
  exact hgraph i j

end Uniform5.Composition
