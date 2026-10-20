import Uniform5.Faces
import Mathlib.Tactic

/-!
# Finite incidence core of the Case B case analyses

These are conditional combinatorial results, not geometric classifications.
`FacetSystem` records the induced edge graph on each facet. `FacetSystem.Laws`
records minimum facet degree and the generic degree-four vertex principle.
The latter is supplied by the simplex face-lattice results in `Faces.lean`;
an adapter below states the necessary realization data explicitly.

The finite graphs, fan vertex sets, and (where used) metric tests must still
be constructed from the geometric fans. No case-specific facet existence,
case exclusion, or product classification is an input to these proofs.
-/

noncomputable section
namespace Uniform5.CaseB

open Finset

/-- Vertices of a four-polytope vertex figure, its edges, and its facets.
The edge graph of a facet is the induced graph, as justified geometrically
by `segment_face_iff`, `edge_restrict`, and `edge_of_face` in `Faces.lean`.
Constructing this finite interface from a polytope is a separate obligation. -/
structure FacetSystem (V F : Type*) [Fintype V] [DecidableEq V] where
  edge : V → V → Prop
  edge_symm : ∀ {u v}, edge u v → edge v u
  edge_irrefl : ∀ v, ¬ edge v v
  vertices : F → Finset V

namespace FacetSystem
variable {V F : Type*} [Fintype V] [DecidableEq V] (G : FacetSystem V F)

noncomputable def neighbours (v : V) : Finset V := by
  classical
  exact univ.filter (G.edge v)

noncomputable def facetNeighbours (f : F) (v : V) : Finset V := G.neighbours v ∩ G.vertices f

@[simp] theorem mem_neighbours {v w : V} : w ∈ G.neighbours v ↔ G.edge v w := by
  classical
  simp [neighbours]

@[simp] theorem mem_facetNeighbours {f : F} {v w : V} :
    w ∈ G.facetNeighbours f v ↔ G.edge v w ∧ w ∈ G.vertices f := by
  simp [facetNeighbours]

/-- The three generic consequences of three-dimensional facets and simple
vertices. In particular no named facet of a Case B configuration is assumed. -/
structure Laws : Prop where
  min_degree : ∀ f v, v ∈ G.vertices f → 3 ≤ (G.facetNeighbours f v).card
  simple_degree : ∀ f v, v ∈ G.vertices f → (G.neighbours v).card = 4 →
    (G.facetNeighbours f v).card = 3
  three_subset : ∀ v, (G.neighbours v).card = 4 → ∀ s : Finset V,
    s ⊆ G.neighbours v → s.card = 3 →
    ∃ f, v ∈ G.vertices f ∧ G.facetNeighbours f v = s

/-- Realization of the generic three-subset principle from the existing
simplex face-lattice theorem. The order isomorphism supplies existence;
`realize` only identifies abstract coatoms with actual facets. -/
theorem three_subset_of_face_lattice
    {Face Edge : Type*} [PartialOrder Face] [OrderTop Face]
    [Fintype Edge] [DecidableEq Edge]
    (v : V) (edgesIn : Face → Finset Edge)
    (figure : Uniform5.VertexFigureSimplexFaceLattice edgesIn)
    (four : Fintype.card Edge = 4)
    (label : Edge ↪ V)
    (realize : ∀ Q, IsCoatom Q →
      ∃ f, v ∈ G.vertices f ∧ G.facetNeighbours f v = (edgesIn Q).map label)
    (s : Finset Edge) (hs : s.card = 3) :
    ∃ f, v ∈ G.vertices f ∧ G.facetNeighbours f v = s.map label := by
  obtain ⟨Q, hQ, _⟩ := Uniform5.simple_vertex_unique_facet edgesIn figure four s hs
  obtain ⟨f, hv, hf⟩ := realize Q hQ.1
  exact ⟨f, hv, by simpa [hQ.2] using hf⟩

/-- The other half of the simple-vertex principle, from the same lattice. -/
theorem facet_degree_of_face_lattice
    {Face Edge : Type*} [PartialOrder Face] [OrderTop Face]
    [Fintype Edge] [DecidableEq Edge]
    (edgesIn : Face → Finset Edge)
    (figure : Uniform5.VertexFigureSimplexFaceLattice edgesIn)
    (four : Fintype.card Edge = 4) (label : Edge ↪ V)
    (f : F) (v : V) (Q : Face) (hQ : IsCoatom Q)
    (incidence : G.facetNeighbours f v = (edgesIn Q).map label) :
    (G.facetNeighbours f v).card = 3 := by
  rw [incidence, card_map]
  exact (Uniform5.simple_vertex_facet_iff_three_edges edgesIn figure four Q).mp hQ

/-- If a facet uses a known triple at a simple vertex, it uses no fourth
neighbour. This is how the paper excludes `a` or `b` from a forced facet. -/
theorem facetNeighbours_eq_of_triple (L : G.Laws) {f : F} {v : V}
    (hv : v ∈ G.vertices f) (hd : (G.neighbours v).card = 4)
    {s : Finset V} (hs : s.card = 3) (hsub : s ⊆ G.facetNeighbours f v) :
    G.facetNeighbours f v = s := by
  exact (eq_of_subset_of_card_le hsub (by rw [L.simple_degree f v hv hd, hs])).symm

/-- The simple-vertex step used repeatedly in the paired theorem. A facet
containing the two partner endpoints belongs to their fan, by definition
of fan incidence. Thus a four-valent vertex with both endpoints among a
triple cannot lie outside that fan. -/
theorem forced_into_fan (L : G.Laws) (S : Finset V) (c d z : V)
    (fan : ∀ f, c ∈ G.vertices f → d ∈ G.vertices f → G.vertices f ⊆ S)
    (off_degree : z ∉ S → (G.neighbours z).card = 4)
    (s : Finset V) (hs : s.card = 3) (hc : c ∈ s) (hd : d ∈ s)
    (hedges : z ∉ S → s ⊆ G.neighbours z) : z ∈ S := by
  by_contra hz
  obtain ⟨f, hv, hf⟩ := L.three_subset z (off_degree hz) s (hedges hz) hs
  have hmem : ∀ t ∈ s, t ∈ G.vertices f := by
    intro t ht
    exact (G.mem_facetNeighbours.mp (hf.symm ▸ ht)).2
  exact hz (fan f (hmem c hc) (hmem d hd) hv)

end FacetSystem

/-- Labels for the seven distinct vertices in the single-fan type (iii):
`0=a, 1=b, 2=x, 3=y, 4=z₁, 5=z₂, 6=w`. The table is exactly the
union of the two pyramid and two tetrahedron edge lists in the paper. -/
noncomputable def s1iiiNeighbours (v : Fin 7) : Finset (Fin 7) :=
  match v.val with
  | 0 => {1, 2, 4, 5, 6}
  | 1 => {0, 3, 4, 5, 6}
  | 2 => {0, 3, 4, 5}
  | 3 => {1, 2, 4, 5}
  | 4 => {0, 1, 2, 3, 6}
  | 5 => {0, 1, 2, 3, 6}
  | _ => {0, 1, 4, 5}

/-- The type-(iii) single-fan graph cannot be the graph of a vertex figure.
A facet at `x` is obtained from the generic three-subset principle. Its
vertices exclude `a,b,w`; minimum degree at `z₁` then contradicts the
missing edge `z₁z₂`. No ridge-specific second-facet premise is required. -/
theorem s1_type_iii_impossible {F : Type*} (G : FacetSystem (Fin 7) F)
    (L : G.Laws) (graph : ∀ v, G.neighbours v = s1iiiNeighbours v) : False := by
  have deg (v : Fin 7) (h : v = 2 ∨ v = 3 ∨ v = 6) :
      (G.neighbours v).card = 4 := by
    rcases h with rfl | rfl | rfl <;> rw [graph] <;> decide
  have triple : ({3, 4, 5} : Finset (Fin 7)) ⊆ G.neighbours 2 := by
    rw [graph]; decide
  obtain ⟨f, hx, hfx⟩ := L.three_subset 2 (deg 2 (by simp)) {3, 4, 5} triple (by decide)
  have hy : 3 ∈ G.vertices f := (G.mem_facetNeighbours.mp (hfx.symm ▸ (show (3 : Fin 7) ∈ ({3, 4, 5} : Finset (Fin 7)) from by simp))).2
  have hz₁ : 4 ∈ G.vertices f := (G.mem_facetNeighbours.mp (hfx.symm ▸ (show (4 : Fin 7) ∈ ({3, 4, 5} : Finset (Fin 7)) from by simp))).2
  have hz₂ : 5 ∈ G.vertices f := (G.mem_facetNeighbours.mp (hfx.symm ▸ (show (5 : Fin 7) ∈ ({3, 4, 5} : Finset (Fin 7)) from by simp))).2
  have ha : 0 ∉ G.vertices f := by
    intro h
    have he : G.edge 2 0 := G.mem_neighbours.mp (by rw [graph]; decide)
    have hm := hfx ▸ (G.mem_facetNeighbours.mpr ⟨he, h⟩)
    exact (by decide : (0 : Fin 7) ∉ ({3, 4, 5} : Finset (Fin 7))) hm
  have hfy : G.facetNeighbours f 3 = {2, 4, 5} := by
    apply G.facetNeighbours_eq_of_triple L hy (deg 3 (by simp)) (by decide)
    intro t ht
    apply G.mem_facetNeighbours.mpr
    constructor
    · apply G.mem_neighbours.mp
      rw [graph]
      simp only [s1iiiNeighbours, mem_insert, mem_singleton] at ht ⊢
      tauto
    · simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl <;> assumption
  have hb : 1 ∉ G.vertices f := by
    intro h
    have he : G.edge 3 1 := G.mem_neighbours.mp (by rw [graph]; decide)
    have hm := hfy ▸ (G.mem_facetNeighbours.mpr ⟨he, h⟩)
    exact (by decide : (1 : Fin 7) ∉ ({2, 4, 5} : Finset (Fin 7))) hm
  have hw : 6 ∉ G.vertices f := by
    intro h
    have bound : G.facetNeighbours f 6 ⊆ ({4, 5} : Finset (Fin 7)) := by
      intro t ht
      have hm := G.mem_facetNeighbours.mp ht
      have hn := G.mem_neighbours.mpr hm.1
      rw [graph] at hn
      have ht' : t = 0 ∨ t = 1 ∨ t = 4 ∨ t = 5 := by
        simpa [s1iiiNeighbours] using hn
      rcases ht' with rfl | rfl | rfl | rfl
      · exact False.elim (ha hm.2)
      · exact False.elim (hb hm.2)
      · simp
      · simp
    have hle := card_le_card bound
    have hmin := L.min_degree f 6 h
    have htwo : ({4, 5} : Finset (Fin 7)).card = 2 := by decide
    omega
  have bound : G.facetNeighbours f 4 ⊆ ({2, 3} : Finset (Fin 7)) := by
    intro t ht
    have hm := G.mem_facetNeighbours.mp ht
    have hn := G.mem_neighbours.mpr hm.1
    rw [graph] at hn
    have ht' : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 6 := by
      simpa [s1iiiNeighbours] using hn
    rcases ht' with rfl | rfl | rfl | rfl | rfl
    · exact False.elim (ha hm.2)
    · exact False.elim (hb hm.2)
    · simp
    · simp
    · exact False.elim (hw hm.2)
  have hle := card_le_card bound
  have hmin := L.min_degree f 4 hz₁
  have htwo : ({2, 3} : Finset (Fin 7)).card = 2 := by decide
  omega


section Paired
variable {V F : Type*} [Fintype V] [DecidableEq V]
variable (G : FacetSystem V F) (L : G.Laws)
include L

/-- A type-(i) three-cycle extra vertex is forced into the partner fan.
The labels are `a,b,c,d,z`. Only the edge list *outside* that fan is needed. -/
theorem paired_k3_vertex_in_partner (p : Fin 5 ↪ V) (S : Finset V)
    (fan : ∀ f, p 2 ∈ G.vertices f → p 3 ∈ G.vertices f → G.vertices f ⊆ S)
    (off : p 4 ∉ S → G.neighbours (p 4) = {p 0, p 1, p 2, p 3}) : p 4 ∈ S := by
  classical
  apply G.forced_into_fan L S (p 2) (p 3) (p 4) fan
    (fun hz => by rw [off hz]; simp) {p 0, p 2, p 3} (by simp) (by simp) (by simp)
  intro hz
  rw [off hz]
  intro t ht
  simp only [mem_insert, mem_singleton] at ht ⊢
  tauto

/-- The two type-(i) four-cycle extra vertices cannot both be outside the
partner fan. Labels: `a,b,c,d,u=x₃,v=x₄`. This proves the incidence step
shared by the (i)/(i), k=4 exclusion and the mixed k=4 alternative. -/
theorem paired_k4_escape (p : Fin 6 ↪ V) (S : Finset V)
    (fan : ∀ f, p 2 ∈ G.vertices f → p 3 ∈ G.vertices f → G.vertices f ⊆ S)
    (off_u : p 4 ∉ S → G.neighbours (p 4) = {p 0, p 1, p 3, p 5})
    (off_v : p 5 ∉ S → G.neighbours (p 5) = {p 0, p 1, p 4, p 2}) :
    p 4 ∈ S ∨ p 5 ∈ S := by
  classical
  by_contra h
  have hu : p 4 ∉ S := fun hu => h (Or.inl hu)
  have hv : p 5 ∉ S := fun hv => h (Or.inr hv)
  have du : (G.neighbours (p 4)).card = 4 := by rw [off_u hu]; simp
  have sub : ({p 0, p 3, p 5} : Finset V) ⊆ G.neighbours (p 4) := by
    rw [off_u hu]
    intro t ht
    simp only [mem_insert, mem_singleton] at ht ⊢
    tauto
  obtain ⟨f, huf, hf⟩ := L.three_subset (p 4) du {p 0, p 3, p 5} sub (by simp)
  have inc : ∀ t ∈ ({p 0, p 3, p 5} : Finset V), t ∈ G.vertices f := by
    intro t ht
    exact (G.mem_facetNeighbours.mp (hf.symm ▸ ht)).2
  have haf := inc (p 0) (by simp)
  have hdf := inc (p 3) (by simp)
  have hvf := inc (p 5) (by simp)
  have hbf : p 1 ∉ G.vertices f := by
    intro hb
    have he : G.edge (p 4) (p 1) := G.mem_neighbours.mp (by rw [off_u hu]; simp)
    have hm := hf ▸ G.mem_facetNeighbours.mpr ⟨he, hb⟩
    simp at hm
  have hcf : p 2 ∈ G.vertices f := by
    by_contra hc
    have bound : G.facetNeighbours f (p 5) ⊆ ({p 0, p 4} : Finset V) := by
      intro t ht
      have hm := G.mem_facetNeighbours.mp ht
      have hn := G.mem_neighbours.mpr hm.1
      rw [off_v hv] at hn
      simp only [mem_insert, mem_singleton] at hn ⊢
      rcases hn with rfl | rfl | rfl | rfl <;> simp_all
    have hle := card_le_card bound
    have hmin := L.min_degree f (p 5) hvf
    have htwo : ({p 0, p 4} : Finset V).card = 2 := by simp
    omega
  exact hu (fan f hcf hdf huf)

/-- The metric form of the (i)/(i), k=4 exclusion. `D` can be Euclidean
distance: unit sides have value 1, whereas all non-endpoint vertices of
the partner type-(i) fan have distance `sqrt 2` to both endpoints. -/
theorem paired_i_i_k4_impossible (p : Fin 6 ↪ V) (S : Finset V)
    (fan : ∀ f, p 2 ∈ G.vertices f → p 3 ∈ G.vertices f → G.vertices f ⊆ S)
    (off_u : p 4 ∉ S → G.neighbours (p 4) = {p 0, p 1, p 3, p 5})
    (off_v : p 5 ∉ S → G.neighbours (p 5) = {p 0, p 1, p 4, p 2})
    (D : V → V → ℝ)
    (partner_metric : ∀ z ∈ S, z ≠ p 2 → z ≠ p 3 →
      D z (p 2) = Real.sqrt 2 ∧ D z (p 3) = Real.sqrt 2)
    (unit_u : D (p 4) (p 3) = 1) (unit_v : D (p 5) (p 2) = 1) : False := by
  have hu : p 4 ∉ S := by
    intro h
    have hm := (partner_metric (p 4) h (by simp) (by simp)).2
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hv : p 5 ∉ S := by
    intro h
    have hm := (partner_metric (p 5) h (by simp) (by simp)).1
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact (paired_k4_escape G L p S fan off_u off_v).elim hu hv

/-- The mixed (i)/(ii), k=3 exclusion. The only metric input beyond the
chord lengths of the first fan is the exact non-chord test for a diagonal
of the antiprism trapezoid. The proof forces `z` into the partner fan,
then identifies it with one of the two trapezoid vertices. -/
theorem paired_i_ii_k3_impossible (p : Fin 5 ↪ V) (x' y' : V)
    (fan : ∀ f, p 2 ∈ G.vertices f → p 3 ∈ G.vertices f →
      G.vertices f ⊆ {p 0, p 1, p 2, p 3, x', y'})
    (off : p 4 ∉ ({p 0, p 1, p 2, p 3, x', y'} : Finset V) →
      G.neighbours (p 4) = {p 0, p 1, p 2, p 3})
    (D : V → V → ℝ) (chord : ℕ → ℝ) (q₂ q₃ : ℕ)
    (hq₂ : 3 ≤ q₂) (hq₃ : 3 ≤ q₃) (δ : ℝ)
    (zc : D (p 4) (p 2) = chord q₃) (zd : D (p 4) (p 3) = chord q₂)
    (xc : D x' (p 2) = δ) (yd : D y' (p 3) = δ)
    (nonchord : ∀ q, 3 ≤ q → δ ≠ chord q) : False := by
  classical
  have hz := paired_k3_vertex_in_partner G L p {p 0, p 1, p 2, p 3, x', y'} fan off
  have hxy : p 4 = x' ∨ p 4 = y' := by simpa using hz
  rcases hxy with hx | hy
  · exact nonchord q₃ hq₃ (xc.symm.trans (hx ▸ zc))
  · exact nonchord q₂ hq₂ (yd.symm.trans (hy ▸ zd))

/-- The (ii)/(ii) exclusion. Labels `a,b,c,d,x`; the witness triple
`{a,c,d}` is available outside the partner fan just as in the k=3 case.
The two possible partner-fan distances from `c` are 1 and `δ`, whereas
`x` has distance `sqrt 2` from the apex `c` of the first fan. -/
theorem paired_ii_ii_impossible (p : Fin 5 ↪ V) (x' y' : V)
    (fan : ∀ f, p 2 ∈ G.vertices f → p 3 ∈ G.vertices f →
      G.vertices f ⊆ {p 0, p 1, p 2, p 3, x', y'})
    (off : p 4 ∉ ({p 0, p 1, p 2, p 3, x', y'} : Finset V) →
      ∃ t, ({p 0, t, p 2, p 3} : Finset V).card = 4 ∧
        G.neighbours (p 4) = {p 0, t, p 2, p 3})
    (D : V → V → ℝ) (δ : ℝ) (xc : D (p 4) (p 2) = Real.sqrt 2)
    (x'c : D x' (p 2) = 1) (y'c : D y' (p 2) = δ) (diag_ne : δ ≠ Real.sqrt 2) : False := by
  classical
  let S : Finset V := {p 0, p 1, p 2, p 3, x', y'}
  have hz : p 4 ∈ S := by
    apply G.forced_into_fan L S (p 2) (p 3) (p 4) fan
      (fun h => by obtain ⟨t, hc, he⟩ := off h; rw [he]; exact hc)
      {p 0, p 2, p 3} (by simp) (by simp) (by simp)
    intro h
    obtain ⟨t, _, he⟩ := off h
    rw [he]
    intro z hz
    simp only [mem_insert, mem_singleton] at hz ⊢
    tauto
  have hxy : p 4 = x' ∨ p 4 = y' := by simpa [S] using hz
  rcases hxy with hx | hy
  · have := x'c.symm.trans (hx ▸ xc)
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  · exact diag_ne (y'c.symm.trans (hy ▸ xc))

end Paired

/-- Generic face-intersection input: two distinct facets meet in a proper
face, which is contained in a ridge of either facet. The ridge vertex sets
are explicit; the mixed proof below uses the five ridges of a pyramid. -/
structure FacetBoundary {V F : Type*} [Fintype V] [DecidableEq V]
    (G : FacetSystem V F) where
  ridges : F → Finset (Finset V)
  intersection : ∀ f g, f ≠ g → ∃ r ∈ ridges f,
    G.vertices f ∩ G.vertices g ⊆ r

/-- A pyramid with quadrilateral base in cyclic order `c,d,u,t`.
Every proper face is contained in one of these five ridges. -/
noncomputable def pyramidRidges {V : Type*} [DecidableEq V] (a c d u t : V) : Finset (Finset V) :=
  {{c, d, u, t}, {a, c, d}, {a, d, u}, {a, u, t}, {a, t, c}}

/-- An apex and opposite base vertices cannot belong to a proper pyramid
face. This is derived by checking the concrete five-ridge list, rather
than assumed as the Case B intersection conclusion. -/
theorem pyramid_opposite_vertices_force_facet
    {V F : Type*} [Fintype V] [DecidableEq V]
    (G : FacetSystem V F) (B : FacetBoundary G) (p : Fin 5 ↪ V) (f g : F)
    (vertices : G.vertices f = {p 0, p 1, p 2, p 3, p 4})
    (ridges : B.ridges f = pyramidRidges (p 0) (p 1) (p 2) (p 3) (p 4))
    (ha : p 0 ∈ G.vertices g) (hc : p 1 ∈ G.vertices g)
    (hu : p 3 ∈ G.vertices g) : f = g := by
  classical
  by_contra hne
  obtain ⟨r, hr, hsub⟩ := B.intersection f g hne
  have ha' : p 0 ∈ r := hsub (by simp [vertices, ha])
  have hc' : p 1 ∈ r := hsub (by simp [vertices, hc])
  have hu' : p 3 ∈ r := hsub (by simp [vertices, hu])
  rw [ridges] at hr
  simp only [pyramidRidges, mem_insert, mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simp at ha'
  · simp at hu'
  · simp at hc'
  · simp at hc'
  · simp at hu'


/-- The same finite boundary check for the other pair of opposite base
vertices. Both checks are needed to avoid a symmetry assumption in mixed k4. -/
theorem pyramid_other_opposite_vertices_force_facet
    {V F : Type*} [Fintype V] [DecidableEq V]
    (G : FacetSystem V F) (B : FacetBoundary G) (p : Fin 5 ↪ V) (f g : F)
    (vertices : G.vertices f = {p 0, p 1, p 2, p 3, p 4})
    (ridges : B.ridges f = pyramidRidges (p 0) (p 1) (p 2) (p 3) (p 4))
    (ha : p 0 ∈ G.vertices g) (hd : p 2 ∈ G.vertices g)
    (ht : p 4 ∈ G.vertices g) : f = g := by
  classical
  by_contra hne
  obtain ⟨r, hr, hsub⟩ := B.intersection f g hne
  have ha' : p 0 ∈ r := hsub (by simp [vertices, ha])
  have hd' : p 2 ∈ r := hsub (by simp [vertices, hd])
  have ht' : p 4 ∈ r := hsub (by simp [vertices, ht])
  rw [ridges] at hr
  simp only [pyramidRidges, mem_insert, mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simp at ha'
  · simp at ht'
  · simp at ht'
  · simp at hd'
  · simp at hd'

/-- The mixed k4 local conclusion: both extra type-(i) vertices are exactly
the two remaining trapezoid vertices of the partner type-(ii) fan.

`p` labels `a,b,c,d,u,v`; `q` labels the pyramid's `a,c,d,y',x'`.
The diagonal tests are local metric assumptions. The escape lemma first
forces at least one extra vertex into the partner fan. If the other were
outside, its three-subset facet would meet the pyramid in an apex and
opposite base vertices. The concrete boundary check forces equality with
the pyramid and gives the contradiction. No case-specific forced facet or
intersection equality is assumed. -/
theorem paired_mixed_k4_completion
    {V F : Type*} [Fintype V] [DecidableEq V]
    (G : FacetSystem V F) (L : G.Laws) (B : FacetBoundary G)
    (p : Fin 6 ↪ V) (q : Fin 5 ↪ V)
    (qa : q 0 = p 0) (qc : q 1 = p 2) (qd : q 2 = p 3)
    (P : F) (vertices : G.vertices P = {q 0, q 1, q 2, q 3, q 4})
    (ridges : B.ridges P = pyramidRidges (q 0) (q 1) (q 2) (q 3) (q 4))
    (fan : ∀ f, p 2 ∈ G.vertices f → p 3 ∈ G.vertices f →
      G.vertices f ⊆ {p 0, p 1, p 2, p 3, q 3, q 4})
    (off_u : p 4 ∉ ({p 0, p 1, p 2, p 3, q 3, q 4} : Finset V) →
      G.neighbours (p 4) = {p 0, p 1, p 3, p 5})
    (off_v : p 5 ∉ ({p 0, p 1, p 2, p 3, q 3, q 4} : Finset V) →
      G.neighbours (p 5) = {p 0, p 1, p 4, p 2})
    (D : V → V → ℝ) (δ : ℝ) (diag_ne : δ ≠ 1)
    (ud : D (p 4) (p 3) = 1) (vc : D (p 5) (p 2) = 1)
    (xd : D (q 4) (p 3) = δ) (yc : D (q 3) (p 2) = δ) :
    p 4 = q 3 ∧ p 5 = q 4 := by
  classical
  let S : Finset V := {p 0, p 1, p 2, p 3, q 3, q 4}
  have id_u : p 4 ∈ S → p 4 = q 3 := by
    intro h
    have h' : p 4 = q 3 ∨ p 4 = q 4 := by simpa [S] using h
    rcases h' with hy | hx
    · exact hy
    · exact False.elim (diag_ne (xd.symm.trans (hx ▸ ud)))
  have id_v : p 5 ∈ S → p 5 = q 4 := by
    intro h
    have h' : p 5 = q 3 ∨ p 5 = q 4 := by simpa [S] using h
    rcases h' with hy | hx
    · exact False.elim (diag_ne (yc.symm.trans (hy ▸ vc)))
    · exact hx
  have Psub : G.vertices P ⊆ S := by
    rw [vertices, qa, qc, qd]
    intro t ht
    simp only [S, mem_insert, mem_singleton] at ht ⊢
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> simp
  rcases paired_k4_escape G L p S fan off_u off_v with hu | hv
  · have uid := id_u hu
    have hv : p 5 ∈ S := by
      by_contra hv
      have degree : (G.neighbours (p 5)).card = 4 := by rw [off_v hv]; simp
      have sub : ({p 0, p 4, p 2} : Finset V) ⊆ G.neighbours (p 5) := by
        rw [off_v hv]
        intro t ht
        simp only [mem_insert, mem_singleton] at ht ⊢
        rcases ht with rfl | rfl | rfl <;> simp
      obtain ⟨f, hvf, hf⟩ := L.three_subset (p 5) degree {p 0, p 4, p 2} sub (by simp)
      have inc : ∀ t ∈ ({p 0, p 4, p 2} : Finset V), t ∈ G.vertices f := by
        intro t ht
        exact (G.mem_facetNeighbours.mp (hf.symm ▸ ht)).2
      have eq := pyramid_opposite_vertices_force_facet G B q P f vertices ridges
        (by rw [qa]; exact inc (p 0) (by simp))
        (by rw [qc]; exact inc (p 2) (by simp))
        (by rw [← uid]; exact inc (p 4) (by simp))
      exact hv (Psub (eq.symm ▸ hvf))
    exact ⟨uid, id_v hv⟩
  · have vid := id_v hv
    have hu : p 4 ∈ S := by
      by_contra hu
      have degree : (G.neighbours (p 4)).card = 4 := by rw [off_u hu]; simp
      have sub : ({p 0, p 3, p 5} : Finset V) ⊆ G.neighbours (p 4) := by
        rw [off_u hu]
        intro t ht
        simp only [mem_insert, mem_singleton] at ht ⊢
        rcases ht with rfl | rfl | rfl <;> simp
      obtain ⟨f, huf, hf⟩ := L.three_subset (p 4) degree {p 0, p 3, p 5} sub (by simp)
      have inc : ∀ t ∈ ({p 0, p 3, p 5} : Finset V), t ∈ G.vertices f := by
        intro t ht
        exact (G.mem_facetNeighbours.mp (hf.symm ▸ ht)).2
      have eq := pyramid_other_opposite_vertices_force_facet G B q P f vertices ridges
        (by rw [qa]; exact inc (p 0) (by simp))
        (by rw [qd]; exact inc (p 3) (by simp))
        (by rw [← vid]; exact inc (p 5) (by simp))
      exact hu (Psub (eq.symm ▸ huf))
    exact ⟨id_u hu, vid⟩


/-- In the surviving paired (i)/(i), k=3 case, the third vertex of the
first fan is the third vertex of the second. The equality is forced by
incidence, rather than assumed in the description of the two fans. -/
theorem paired_i_i_k3_same_third_vertex
    {V F : Type*} [Fintype V] [DecidableEq V]
    (G : FacetSystem V F) (L : G.Laws) (p : Fin 5 ↪ V) (z' : V)
    (fan : ∀ f, p 2 ∈ G.vertices f → p 3 ∈ G.vertices f →
      G.vertices f ⊆ {p 0, p 1, p 2, p 3, z'})
    (off : p 4 ∉ ({p 0, p 1, p 2, p 3, z'} : Finset V) →
      G.neighbours (p 4) = {p 0, p 1, p 2, p 3}) : p 4 = z' := by
  have hz := paired_k3_vertex_in_partner G L p {p 0, p 1, p 2, p 3, z'} fan off
  simpa using hz

/-- The surviving paired (i)/(i), k=3 parameters are both 4, conditional
only on the local distance/chord identities. `chord_four` is an
exact metric input, not a classification of fans or polytopes. -/
theorem paired_i_i_k3_parameters
    {V F : Type*} [Fintype V] [DecidableEq V]
    (G : FacetSystem V F) (L : G.Laws) (p : Fin 5 ↪ V) (S : Finset V)
    (fan : ∀ f, p 2 ∈ G.vertices f → p 3 ∈ G.vertices f → G.vertices f ⊆ S)
    (off : p 4 ∉ S → G.neighbours (p 4) = {p 0, p 1, p 2, p 3})
    (D : V → V → ℝ) (chord : ℕ → ℝ) (q₂ q₃ : ℕ)
    (hq₂ : 3 ≤ q₂) (hq₃ : 3 ≤ q₃)
    (partner_metric : ∀ z ∈ S, z ≠ p 2 → z ≠ p 3 →
      D z (p 2) = Real.sqrt 2 ∧ D z (p 3) = Real.sqrt 2)
    (zc : D (p 4) (p 2) = chord q₃) (zd : D (p 4) (p 3) = chord q₂)
    (chord_four : ∀ q, 3 ≤ q → (chord q = Real.sqrt 2 ↔ q = 4)) : q₂ = 4 ∧ q₃ = 4 := by
  have hz := paired_k3_vertex_in_partner G L p S fan off
  have hm := partner_metric (p 4) hz (by simp) (by simp)
  exact ⟨(chord_four q₂ hq₂).mp (zd.symm.trans hm.2),
    (chord_four q₃ hq₃).mp (zc.symm.trans hm.1)⟩

/-- Translation of a point set, for the graph propagation core of the
single-fan product and paired cell-partition arguments. -/
noncomputable def translateSet {E : Type*} [AddCommGroup E] (τ : E) (S : Set E) : Set E :=
  (fun x => τ + x) '' S

@[simp] theorem translateSet_zero {E : Type*} [AddCommGroup E] (S : Set E) :
    translateSet 0 S = S := by
  simp [translateSet]

@[simp] theorem translateSet_add {E : Type*} [AddCommGroup E]
    (τ σ : E) (S : Set E) :
    translateSet τ (translateSet σ S) = translateSet (τ + σ) S := by
  ext x
  simp only [translateSet, Set.mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, add_assoc τ σ z⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨σ + z, ⟨z, hz, rfl⟩, (add_assoc τ σ z).symm⟩

/-- Local actual-cell translations along a connected vertex graph imply
that all cells are translates of the root cell by vectors in the same
additive subgroup (the orthogonal complement in the paper). This proves
transport only; the local translations, graph connectivity, dimension,
convex product identity, and uniformity must be supplied geometrically. -/
theorem connected_cell_translate
    {V E : Type*} [AddCommGroup E] (adj : V → V → Prop)
    (C : V → Set E) (H : AddSubgroup E) (r : V)
    (connected : ∀ t, Relation.ReflTransGen adj r t)
    (step : ∀ x y, adj x y → ∃ τ ∈ H, C y = translateSet τ (C x)) :
    ∀ t, ∃ τ ∈ H, C t = translateSet τ (C r) := by
  intro t
  induction connected t with
  | refl => exact ⟨0, H.zero_mem, (translateSet_zero (C r)).symm⟩
  | @tail x y _ hxy ih =>
    obtain ⟨σ, hσ, hx⟩ := ih
    obtain ⟨τ, hτ, hy⟩ := step x y hxy
    refine ⟨τ + σ, H.add_mem hτ hσ, ?_⟩
    rw [hy, hx, translateSet_add]


/-- Generic reconstruction of the vertex-figure graph from its covering
fan facets and their individual edge lists. Both endpoints must belong
to the covering facet; the local-list equivalence incorporates both
restriction and lifting of face edges. -/
theorem neighbours_of_covering_fan
    {V F ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
    (G : FacetSystem V F) (fan : ι → F) (N : ι → V → Finset V)
    (cover : ∀ v w, G.edge v w →
      ∃ i, v ∈ G.vertices (fan i) ∧ w ∈ G.vertices (fan i))
    (lists : ∀ i v w, G.edge v w ∧ v ∈ G.vertices (fan i) ∧
      w ∈ G.vertices (fan i) ↔ w ∈ N i v) (v : V) :
    G.neighbours v = univ.biUnion (fun i => N i v) := by
  classical
  ext w
  simp only [G.mem_neighbours, mem_biUnion, mem_univ, true_and]
  constructor
  · intro he
    obtain ⟨i, hv, hw⟩ := cover v w he
    exact ⟨i, (lists i v w).mp ⟨he, hv, hw⟩⟩
  · rintro ⟨i, hi⟩
    exact ((lists i v w).mpr hi).1

/-- Edge list of a pyramid over the quadrilateral cycle `a-b-y-x-a`,
with apex `z`. Labels agree with `s1iiiNeighbours`. -/
noncomputable def s1iiiPyramidNeighbours (z v : Fin 7) : Finset (Fin 7) :=
  if v = z then {0, 1, 2, 3}
  else if v = 0 then {1, 2, z}
  else if v = 1 then {0, 3, z}
  else if v = 2 then {0, 3, z}
  else if v = 3 then {1, 2, z}
  else ∅

/-- A tetrahedron contributes all pairs of distinct vertices. -/
noncomputable def tetrahedronNeighbours {V : Type*} [DecidableEq V] (T : Finset V) (v : V) : Finset V :=
  if v ∈ T then T.erase v else ∅

/-- The four actual facet edge lists of the single type-(iii) fan. -/
noncomputable def s1iiiFacetNeighbours (i : Fin 4) (v : Fin 7) : Finset (Fin 7) :=
  match i.val with
  | 0 => s1iiiPyramidNeighbours 4 v
  | 1 => s1iiiPyramidNeighbours 5 v
  | 2 => tetrahedronNeighbours {0, 1, 4, 6} v
  | _ => tetrahedronNeighbours {0, 1, 5, 6} v

/-- Kernel-checked finite union of the four concrete edge lists. -/
theorem s1iii_facet_lists_union (v : Fin 7) :
    (univ : Finset (Fin 4)).biUnion (fun i => s1iiiFacetNeighbours i v) =
      s1iiiNeighbours v := by
  fin_cases v <;> decide

/-- Single-fan type (iii) is impossible directly from covering fan
incidence and the concrete pyramid/tetrahedron edge lists. In particular
the global graph, missing `z₁z₂` edge, and simple-vertex degrees are derived
from these lists; none is a separate exclusion assumption. -/
theorem s1_type_iii_impossible_of_fan {F : Type*}
    (G : FacetSystem (Fin 7) F) (L : G.Laws) (fan : Fin 4 → F)
    (cover : ∀ v w, G.edge v w →
      ∃ i, v ∈ G.vertices (fan i) ∧ w ∈ G.vertices (fan i))
    (lists : ∀ i v w, G.edge v w ∧ v ∈ G.vertices (fan i) ∧
      w ∈ G.vertices (fan i) ↔ w ∈ s1iiiFacetNeighbours i v) : False := by
  apply s1_type_iii_impossible G L
  intro v
  exact (neighbours_of_covering_fan G fan s1iiiFacetNeighbours cover lists v).trans
    (s1iii_facet_lists_union v)


/-- Off the second fan, the first fan's concrete edge lists give the whole
neighbourhood. This is the generic justification for the `off` hypotheses
in the paired results. The second-fan alternative records only vertex
incidence; no valence or desired Case B exclusion is hidden in it. -/
theorem neighbours_outside_second_fan
    {V F ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
    (G : FacetSystem V F) (fan : ι → F) (N : ι → V → Finset V) (S : Finset V)
    (cover : ∀ v w, G.edge v w →
      (∃ i, v ∈ G.vertices (fan i) ∧ w ∈ G.vertices (fan i)) ∨ v ∈ S)
    (lists : ∀ i v w, G.edge v w ∧ v ∈ G.vertices (fan i) ∧
      w ∈ G.vertices (fan i) ↔ w ∈ N i v) (v : V) (hv : v ∉ S) :
    G.neighbours v = univ.biUnion (fun i => N i v) := by
  classical
  ext w
  simp only [G.mem_neighbours, mem_biUnion, mem_univ, true_and]
  constructor
  · intro he
    rcases cover v w he with ⟨i, hvi, hwi⟩ | hvs
    · exact ⟨i, (lists i v w).mp ⟨he, hvi, hwi⟩⟩
    · exact False.elim (hv hvs)
  · rintro ⟨i, hi⟩
    exact ((lists i v w).mpr hi).1

end Uniform5.CaseB
