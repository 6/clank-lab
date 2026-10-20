import Uniform5.CompositionNeighborCandidates
import Uniform5.CompositionRadiusTransport

/-! Local-to-global propagation with the actual circumcenter fixed. The
independent stage-three computation checks center-fixing congruences; actual
polytope symmetries preserve the centroid, so these suffice for propagation. -/
noncomputable section
namespace Uniform5.Composition
open Set

noncomputable def polytopeCenter (P : UnitUniform5) : Space 5 :=
  vertexCentroid (vertices P.val (uniform_finitePolytope P.property.1))

theorem polytopeCenter_image (g : Space 5 ≃ᵃⁱ[ℝ] Space 5) (P : UnitUniform5) :
    polytopeCenter (P.image g) = g (polytopeCenter P) :=
  (embedding_vertexCentroid g.toAffineIsometry (uniform_finitePolytope P.property.1)).symm

theorem polytopeCenter_symmetry (P : UnitUniform5)
    (g : Space 5 ≃ᵃⁱ[ℝ] Space 5) (hg : g '' P.val = P.val) :
    g (polytopeCenter P) = polytopeCenter P := by
  rw [← polytopeCenter_image, show P.image g = P from UnitUniform5.ext hg]

abbrev CenteredUnitUniform5 (c : Space 5) := {P : UnitUniform5 // polytopeCenter P = c}

noncomputable def centeredImage {c : Space 5} (g : Space 5 ≃ᵃⁱ[ℝ] Space 5)
    (hc : g c = c) (P : CenteredUnitUniform5 c) : CenteredUnitUniform5 c :=
  ⟨P.val.image g, by rw [polytopeCenter_image, P.property, hc]⟩

noncomputable def centeredImageEquiv {c : Space 5} (g : Space 5 ≃ᵃⁱ[ℝ] Space 5)
    (hc : g c = c) : CenteredUnitUniform5 c ≃ CenteredUnitUniform5 c where
  toFun := centeredImage g hc
  invFun := centeredImage g.symm (by apply g.injective; simpa using hc.symm)
  left_inv P := Subtype.ext (UnitUniform5.image_symm g P.val)
  right_inv P := Subtype.ext (by
    apply UnitUniform5.ext
    exact affineIsometry_image_symm_image g P.val.val)

noncomputable def centeredGeometricStarSystem (c : Space 5) :
    StarSystem (Space 5) (Set (Set (Space 5))) (CenteredUnitUniform5 c) where
  vertices P := P.val.val.extremePoints ℝ
  finite_vertices P := geometricStarSystem.finite_vertices P.val
  star P := facetStar P.val.val
  adjacent P := Edge P.val.val
  adjacent_mem h := ⟨h.1, h.2.1⟩
  neighbours := geometricStarSystem.neighbours
  connected := geometricStarSystem.connected
  ext h := Subtype.ext (UnitUniform5.ext_vertices h)

noncomputable def centeredGeometricStarTransport {c : Space 5}
    (g : Space 5 ≃ᵃⁱ[ℝ] Space 5) (hc : g c = c) :
    StarTransport (centeredGeometricStarSystem c) where
  point := g.toEquiv
  stars := facetSetImageEquiv g
  model := centeredImageEquiv g hc
  vertices P x := UnitUniform5.image_mem_vertices g P.val x
  star P x := facetStar_image g P.val.val x
  adjacent P x y := edge_image_iff g P.val.val x y

theorem centeredGeometricStarSystem_transitive (c r : Space 5)
    (P : CenteredUnitUniform5 c) (hr : r ∈ P.val.val.extremePoints ℝ)
    (x : Space 5) (hx : x ∈ P.val.val.extremePoints ℝ) :
    ∃ t : StarTransport (centeredGeometricStarSystem c),
      t.model P = P ∧ t.point r = x := by
  obtain ⟨g, hg, hgr⟩ := uniform_vertexTransitive P.val.property.1 r hr x hx
  have hc : g c = c := by
    rw [← P.property]
    exact polytopeCenter_symmetry P.val g hg
  exact ⟨centeredGeometricStarTransport g hc,
    Subtype.ext (UnitUniform5.ext hg), hgr⟩

/-- The actual symmetry is a center-fixing member of the retained geometric
candidate set, with the actual star at the new vertex as its image. -/
theorem actual_centered_neighbor_candidate {c : Space 5} (P : CenteredUnitUniform5 c)
    {r w : Space 5} (he : Edge P.val.val r w) :
    ∃ g ∈ neighborStarCandidates r w (facetStar P.val.val r), g c = c ∧
      facetSetImage g (facetStar P.val.val r) = facetStar P.val.val w := by
  obtain ⟨g, hg, hgr⟩ := uniform_vertexTransitive P.val.property.1 r he.1 w he.2.1
  refine ⟨g, symmetry_mem_neighborStarCandidates P.val.property he g hg hgr, ?_, ?_⟩
  · rw [← P.property]
    exact polytopeCenter_symmetry P.val g hg
  · rw [← facetStar_image, hg, hgr]

/-- Exact center-fixing candidate checks imply equality of the actual stars
at every root neighbor, in precisely the domain used by the checker. -/
theorem centered_neighbor_candidates_force (c r : Space 5) (S : Set (Set (Space 5)))
    (checked : ∀ w, starNeighbor r w S →
      ∀ g ∈ neighborStarCandidates r w S, g c = c →
      ∀ h ∈ neighborStarCandidates r w S, h c = c →
        facetSetImage g S = facetSetImage h S)
    (A B : CenteredUnitUniform5 c) (hsA : facetStar A.val.val r = S)
    (hsB : facetStar B.val.val r = S) {w : Space 5} (he : Edge A.val.val r w) :
    facetStar A.val.val w = facetStar B.val.val w := by
  have heB : Edge B.val.val r w := (facetStar_determines_edges
    (uniform_finitePolytope A.val.property.1) (uniform_finitePolytope B.val.property.1)
    (by rw [uniform_dimension A.val.property.1]; norm_num)
    (by rw [uniform_dimension B.val.property.1]; norm_num) (hsA.trans hsB.symm) w).mp he
  obtain ⟨g, hg, hgc, hgs⟩ := actual_centered_neighbor_candidate A he
  obtain ⟨h, hh, hhc, hhs⟩ := actual_centered_neighbor_candidate B heB
  rw [hsA] at hg hgs
  rw [hsB] at hh hhs
  have hw : starNeighbor r w S := hsA ▸ (edge_iff_starNeighbor A.val.property).mp he
  exact hgs.symm.trans ((checked w hw g hg hgc h hh hhc).trans hhs)

/-- The center-fixing checks suffice for global equality: all transports
used in propagation preserve the actual circumcenter. -/
theorem centered_neighbor_candidates_global (c r : Space 5) (S : Set (Set (Space 5)))
    (checked : ∀ w, starNeighbor r w S →
      ∀ g ∈ neighborStarCandidates r w S, g c = c →
      ∀ h ∈ neighborStarCandidates r w S, h c = c →
        facetSetImage g S = facetSetImage h S)
    {A B : CenteredUnitUniform5 c} (hrA : r ∈ A.val.val.extremePoints ℝ)
    (hrB : r ∈ B.val.val.extremePoints ℝ)
    (hsA : facetStar A.val.val r = S) (hsB : facetStar B.val.val r = S) : A = B := by
  apply (centeredGeometricStarSystem c).local_uniqueness_global r S
    (centeredGeometricStarSystem_transitive c r) ?_ hrA hrB hsA hsB
  intro C D _ _ hC hD w he
  exact centered_neighbor_candidates_force c r S checked C D hC hD he

end Uniform5.Composition
