import Uniform5.CompositionFaceOrbits
import Uniform5.CompositionCycleFilter

/-!
# The closure-filter witness on actual faces

The cycles here are indexed by actual polygon faces. A side is a facet and
one of its polygon faces, interpreted up to the actual symmetry group of
that facet. Every required orbit has a representative at the chosen vertex,
so these actual incidences form an internally supported set.

This proves the geometric support argument of `lem:filter`. The remaining
library bridge must identify these occurrences with the sides of the
ordered transverse cycles and place their root intervals in one class.
-/

noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def ActualPolygon (P : Set E) := {F : Set E // ∃ k, PolygonFace P F k}
noncomputable def ActualFacet (P : Set E) := {K : Set E // Facet P K}
noncomputable def ActualPolygonSide (P : Set E) := Σ K : ActualFacet P, ActualPolygon K.val

/-- Incidence up to a genuine facet symmetry; no computed equivalence or
arbitrary label equality is substituted for the orbit relation. -/
noncomputable def actualPolygonIncidence (P : Set E) :
    CycleFilter.Incidence (ActualPolygon P) (ActualPolygonSide P) (ActualFacet P) where
  sides G := {s | ∃ g : E ≃ᵃⁱ[ℝ] E, g '' s.1.val = s.1.val ∧ g '' s.2.val = G.val}
  facet s := s.1
  required K := {s | s.1 = K}

noncomputable def polygonsAtVertex (P : Set E) (v : E) : Set (ActualPolygon P) :=
  {G | v ∈ G.val.extremePoints ℝ}

/-- All actual polygon incidences at a vertex are internally supported.
The witness comes from vertex-transitivity of the incident facet, not from
assuming that the filter happens to retain the polygon. -/
theorem actual_polygons_supported {n : ℕ} {P : Set E}
    (hP : UnitUniform (n + 4) P) (v : E) :
    (actualPolygonIncidence P).Supported (polygonsAtVertex P v) := by
  rintro G hv s ⟨g, hg, hgG⟩ r hr
  change v ∈ G.val.extremePoints ℝ at hv
  change r.1 = s.1 at hr
  have hvP : v ∈ P.extremePoints ℝ := by
    obtain ⟨k, hk⟩ := G.property
    exact (face_extremePoints_eq hk.1 ▸ hv).2
  have hvK : v ∈ s.1.val := by
    have hvG : v ∈ G.val := extremePoints_subset hv
    rw [← hgG] at hvG
    obtain ⟨w, hw, rfl⟩ := hvG
    have hwK : w ∈ s.1.val := by
      obtain ⟨k, hk⟩ := s.2.property
      exact hk.1.2.1 hw
    rw [← hg]
    exact ⟨w, hwK, rfl⟩
  have hvr : v ∈ r.1.val.extremePoints ℝ := by
    rw [hr, face_extremePoints_eq s.1.property.1]
    exact ⟨hvK, hvP⟩
  obtain ⟨k, hk⟩ := r.2.property
  obtain ⟨f, hf, _, hfP, hfv⟩ := unitUniform_facet_polygon_orbit hP r.1.property hk hvr
  let G' : ActualPolygon P := ⟨f '' r.2.val, k, hfP⟩
  exact ⟨G', hfv, f, hf, rfl⟩

/-- Therefore every input set of actual polygons that contains all polygons
at the vertex retains all of them, after every round and at termination. -/
theorem actual_polygons_survive {n : ℕ} {P : Set E}
    (hP : UnitUniform (n + 4) P) (v : E) (S : Finset (ActualPolygon P))
    (hS : polygonsAtVertex P v ⊆ (S : Set (ActualPolygon P))) :
    polygonsAtVertex P v ⊆ ((actualPolygonIncidence P).survivors S : Set (ActualPolygon P)) :=
  (actualPolygonIncidence P).supported_subset_survivors (actual_polygons_supported hP v) hS

end Uniform5.Composition
