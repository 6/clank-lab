import Uniform5.CompositionProductEdges
import Uniform5.CompositionCaseBProductSlices

/-! The actual edge star of a unit interval endpoint. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- Each interval vertex has exactly one actual neighbor at unit distance. -/
theorem unitInterval_neighbor {v : Space 1} (hv : v ∈ unitInterval.extremePoints ℝ) :
    ∃ w, w ∈ unitInterval.extremePoints ℝ ∧ dist v w = 1 ∧
      (∀ z, Edge unitInterval v z ↔ z = w) := by
  obtain ⟨a, b, hab, hseg, hext⟩ := finitePolytope_dim_one_segment
    unitInterval_finitePolytope unitInterval_affineDimension
  have hea : a ∈ unitInterval.extremePoints ℝ := by rw [hext]; simp
  have heb : b ∈ unitInterval.extremePoints ℝ := by rw [hext]; simp
  have he : Edge unitInterval a b :=
    ⟨hea, heb, hab, by rw [← hseg]; exact IsExposed.refl unitInterval⟩
  have he' : Edge unitInterval b a :=
    ⟨heb, hea, hab.symm, by rw [segment_symm]; exact he.2.2.2⟩
  rw [hext] at hv
  rcases hv with rfl | hv
  · refine ⟨b, heb, unitUniform_interval.2 _ _ he, ?_⟩
    intro z
    constructor
    · intro hz
      have hm := hz.2.1
      rw [hext] at hm
      rcases hm with rfl | hm
      · exact (hz.2.2.1 rfl).elim
      · exact hm
    · rintro rfl; exact he
  · have hv' : v = b := hv
    subst v
    refine ⟨a, hea, unitUniform_interval.2 _ _ he', ?_⟩
    intro z
    constructor
    · intro hz
      have hm := hz.2.1
      rw [hext] at hm
      rcases hm with hm | hm
      · exact hm
      · exact (hz.2.2.1 (show b = z from hm.symm)).elim
    · rintro rfl; exact he'

end Uniform5.Composition
