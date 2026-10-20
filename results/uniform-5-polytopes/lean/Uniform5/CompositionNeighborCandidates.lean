import Uniform5.CompositionStars
import Uniform5.CompositionFamilies

/-! Actual symmetries occur among the geometric candidates used in the
local-uniqueness checks. Compatibility retains every facet already known
through the new vertex. These lemmas supply the geometric implication from
a candidate check to local forcing; they do not assert that the check passes. -/

noncomputable section
namespace Uniform5.Composition
open Set

/-- The root neighbors determined by an actual facet star. -/
noncomputable def starNeighbor (r w : Space 5) (S : Set (Set (Space 5))) : Prop :=
  ∃ F ∈ S, Edge F r w

/-- The star's neighbor predicate is exactly adjacency in the actual polytope. -/
theorem edge_iff_starNeighbor {P : Set (Space 5)} (hP : UnitUniform 5 P)
    {r w : Space 5} : Edge P r w ↔ starNeighbor r w (facetStar P r) := by
  constructor
  · intro he
    obtain ⟨F, hF, hrF, hwF⟩ := edge_mem_facet (uniform_finitePolytope hP.1) he
      (by rw [uniform_dimension hP.1]; norm_num)
    exact ⟨F, ⟨hF, hrF⟩,
      (edge_face_iff (uniform_finitePolytope hP.1) hF.1 hrF hwF).mp he⟩
  · rintro ⟨F, hF, he⟩
    exact (edge_face_iff (uniform_finitePolytope hP.1) hF.1.1
      he.1.1 he.2.1.1).mpr he

/-- The exact geometric candidate set before any numerical exclusion. A
candidate sends one star facet to a known facet through the new vertex,
and its moved star contains every such known facet. -/
noncomputable def neighborStarCandidates (r w : Space 5)
    (S : Set (Set (Space 5))) : Set (Space 5 ≃ᵃⁱ[ℝ] Space 5) :=
  {g | g r = w ∧
    (∃ F ∈ S, ∃ A ∈ S, w ∈ A ∧ g '' F = A) ∧
    ∀ A ∈ S, w ∈ A → A ∈ facetSetImage g S}

/-- Any fixed known facet through the new vertex can be used as the
anchor. Thus choosing the paper's first such facet loses no candidate. -/
theorem neighborStarCandidates_iff_fixed_facet {r w : Space 5}
    {S : Set (Set (Space 5))} {A : Set (Space 5)} (hA : A ∈ S) (hwA : w ∈ A)
    (g : Space 5 ≃ᵃⁱ[ℝ] Space 5) :
    g ∈ neighborStarCandidates r w S ↔
      g r = w ∧ (∃ F ∈ S, g '' F = A) ∧
        ∀ B ∈ S, w ∈ B → B ∈ facetSetImage g S := by
  constructor
  · intro h
    exact ⟨h.1, h.2.2 A hA hwA, h.2.2⟩
  · rintro ⟨hr, ⟨F, hF, hFA⟩, hc⟩
    exact ⟨hr, ⟨F, hF, A, hA, hwA, hFA⟩, hc⟩

/-- A genuine symmetry taking the root to a neighbor survives the exact
candidate conditions. The shared facet is obtained from the actual edge. -/
theorem symmetry_mem_neighborStarCandidates {P : Set (Space 5)}
    (hP : UnitUniform 5 P) {r w : Space 5} (he : Edge P r w)
    (g : Space 5 ≃ᵃⁱ[ℝ] Space 5) (hg : g '' P = P) (hgr : g r = w) :
    g ∈ neighborStarCandidates r w (facetStar P r) := by
  have hs : facetSetImage g (facetStar P r) = facetStar P w := by
    rw [← facetStar_image, hg, hgr]
  refine ⟨hgr, ?_, ?_⟩
  · obtain ⟨A, hA, hrA, hwA⟩ := edge_mem_facet (uniform_finitePolytope hP.1) he
      (by rw [uniform_dimension hP.1]; norm_num)
    have hAimage : A ∈ facetSetImage g (facetStar P r) := by
      rw [hs]
      exact ⟨hA, hwA⟩
    obtain ⟨F, hF, hFA⟩ := hAimage
    exact ⟨F, hF, A, ⟨hA, hrA⟩, hwA, hFA⟩
  · intro A hA hwA
    rw [hs]
    exact ⟨hA.1, hwA⟩

/-- The true star at a neighbor is the image of a retained geometric
candidate; vertex transitivity supplies that candidate. -/
theorem actual_neighbor_star_candidate {P : Set (Space 5)} (hP : UnitUniform 5 P)
    {r w : Space 5} (he : Edge P r w) :
    ∃ g ∈ neighborStarCandidates r w (facetStar P r),
      facetSetImage g (facetStar P r) = facetStar P w := by
  obtain ⟨g, hg, hgr⟩ := uniform_vertexTransitive hP.1 r he.1 w he.2.1
  refine ⟨g, symmetry_mem_neighborStarCandidates hP he g hg hgr, ?_⟩
  rw [← facetStar_image, hg, hgr]

/-- Equality of all retained candidate stars gives precisely the local
forcing premise of geometric propagation. No assumption about graph or
facet incidence is needed. -/
theorem neighbor_candidates_force (r : Space 5) (S : Set (Set (Space 5)))
    (checked : ∀ w, starNeighbor r w S → ∀ g ∈ neighborStarCandidates r w S,
      ∀ h ∈ neighborStarCandidates r w S, facetSetImage g S = facetSetImage h S)
    (A B : UnitUniform5) (hsA : facetStar A.val r = S)
    (hsB : facetStar B.val r = S) {w : Space 5} (he : Edge A.val r w) :
    facetStar A.val w = facetStar B.val w := by
  have heB : Edge B.val r w := (facetStar_determines_edges
    (uniform_finitePolytope A.property.1) (uniform_finitePolytope B.property.1)
    (by rw [uniform_dimension A.property.1]; norm_num)
    (by rw [uniform_dimension B.property.1]; norm_num) (hsA.trans hsB.symm) w).mp he
  obtain ⟨g, hg, hgs⟩ := actual_neighbor_star_candidate A.property he
  obtain ⟨h, hh, hhs⟩ := actual_neighbor_star_candidate B.property heB
  rw [hsA] at hg hgs
  rw [hsB] at hh hhs
  have hw : starNeighbor r w S := hsA ▸ (edge_iff_starNeighbor A.property).mp he
  exact hgs.symm.trans ((checked w hw g hg h hh).trans hhs)

/-- The local candidate check composes with the already proved actual
polytope propagation theorem. The numerical/encoding check itself remains
an explicit premise of this intermediate lemma. -/
theorem neighbor_candidates_global (r : Space 5) (S : Set (Set (Space 5)))
    (checked : ∀ w, starNeighbor r w S → ∀ g ∈ neighborStarCandidates r w S,
      ∀ h ∈ neighborStarCandidates r w S, facetSetImage g S = facetSetImage h S)
    {A B : UnitUniform5} (hrA : r ∈ A.val.extremePoints ℝ)
    (hrB : r ∈ B.val.extremePoints ℝ)
    (hsA : facetStar A.val r = S) (hsB : facetStar B.val r = S) : A = B := by
  apply geometric_local_uniqueness_global r S ?_ hrA hrB hsA hsB
  intro C D _ _ hC hD w he
  exact neighbor_candidates_force r S checked C D hC hD he

end Uniform5.Composition
