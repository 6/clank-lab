import Uniform5.CompositionPolygonChords
import Uniform5.CaseBMetric

/-! Exactly two actual edge neighbors at each regular-polygon vertex. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- The two polygon neighbors are constructed and exhaustive, including
for triangles. The chord and both unit sides are proved exact. -/
theorem unitPolygon_neighbor_pair {n : ℕ} (hn : 3 ≤ n) {v : Plane}
    (hv : v ∈ (unitPolygon n).extremePoints ℝ) :
    ∃ a b : Plane, a ≠ b ∧ Edge (unitPolygon n) v a ∧ Edge (unitPolygon n) v b ∧
      (∀ z, Edge (unitPolygon n) v z ↔ z = a ∨ z = b) ∧
      dist v a = 1 ∧ dist v b = 1 ∧ dist a b = CaseB.chord n := by
  letI : NeZero n := ⟨by omega⟩
  let r := unitPolygonRadius n
  let p₀ := polygonPoint n r ⟨0, by omega⟩
  let p₁ := polygonPoint n r ⟨1, by omega⟩
  let p₂ := polygonPoint n r ⟨2, by omega⟩
  have hr := unitPolygonRadius_pos hn
  have h01 : Edge (unitPolygon n) p₁ p₀ := by
    have he := polygon_first_edge n r hn hr
    exact ⟨he.2.1, he.1, he.2.2.1.symm, by simpa only [segment_symm] using he.2.2.2⟩
  have h12 : Edge (unitPolygon n) p₁ p₂ := by
    have he := polygon_consecutive_edge r hn hr (⟨1, by omega⟩ : Fin n)
    have hi : (⟨1, by omega⟩ : Fin n) + 1 = ⟨2, by omega⟩ := by
      apply Fin.ext
      simp [Fin.val_add, Nat.mod_eq_of_lt (show 2 < n by omega)]
    rw [hi] at he
    exact he
  have h02 : p₀ ≠ p₂ := by
    intro he
    have h := congrArg Fin.val (polygonPoint_injective n r hn hr he)
    norm_num at h
  obtain ⟨g, hg, hgv⟩ := polygon_vertexTransitive r (by omega) p₁ h01.1 v hv
  change g '' unitPolygon n = unitPolygon n at hg
  have he₀ : Edge (unitPolygon n) v (g p₀) := by
    have he := edge_image g h01
    rwa [hg, hgv] at he
  have he₂ : Edge (unitPolygon n) v (g p₂) := by
    have he := edge_image g h12
    rwa [hg, hgv] at he
  have hne : g p₀ ≠ g p₂ := fun h => h02 (g.injective h)
  refine ⟨g p₀, g p₂, hne, he₀, he₂, ?_,
    unitEdges_unitPolygon hn _ _ he₀, unitEdges_unitPolygon hn _ _ he₂,
    unitPolygon_neighbor_chord hn he₀ he₂ hne⟩
  intro z
  constructor
  · intro he
    have hg' : g.symm '' unitPolygon n = unitPolygon n := by
      conv_lhs => rw [← hg]
      exact affineIsometry_symm_image_image g _
    have he' := edge_image g.symm he
    rw [hg', ← hgv, g.symm_apply_apply] at he'
    have hz := edge_of_two_spanning_edges h01 h12 h02
      (polygon_second_neighbors_span n r hn hr) he'
    rcases hz with hz | hz
    · exact Or.inl (by simpa using congrArg g hz)
    · exact Or.inr (by simpa using congrArg g hz)
  · rintro (rfl | rfl) <;> assumption

end Uniform5.Composition
