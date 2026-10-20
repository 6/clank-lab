import Uniform5.CompositionActualWedgeCover

/-! Transport the exact W assertion to an actual positioned fan. Both the
supporting halfspaces and the exempt pairs move by the same isometry. -/
noncomputable section
namespace Uniform5.CaseB
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Literal image of a W chart under an ambient affine isometry. -/
def WFanGeometry.map (F : WFanGeometry E) (g : E ≃ᵃⁱ[ℝ] E) : WFanGeometry E where
  v := g F.v
  centre := g F.centre
  radius := F.radius
  vertices := F.vertices.map g.toEquiv.toEmbedding
  ends := F.ends.map g.toEquiv.toEmbedding
  halfspaces := (fun H : Set E => g '' H) '' F.halfspaces
  specialPair := fun x y => F.specialPair (g.symm x) (g.symm y)

@[simp] theorem WFanGeometry.mem_map_vertices (F : WFanGeometry E)
    (g : E ≃ᵃⁱ[ℝ] E) (x : E) :
    g x ∈ (F.map g).vertices ↔ x ∈ F.vertices := by
  simp [map]

@[simp] theorem WFanGeometry.mem_map_ends (F : WFanGeometry E)
    (g : E ≃ᵃⁱ[ℝ] E) (x : E) :
    g x ∈ (F.map g).ends ↔ x ∈ F.ends := by
  simp [map]

@[simp] theorem WFanGeometry.map_admissible (F : WFanGeometry E)
    (g : E ≃ᵃⁱ[ℝ] E) (x : E) :
    (F.map g).Admissible (g x) ↔ F.Admissible x := by
  constructor
  · rintro ⟨hd, hr, hh, hs⟩
    refine ⟨by simpa [map] using hd, by simpa [map] using hr, ?_, ?_⟩
    · intro H hH
      obtain ⟨y, hy, he⟩ := hh (g '' H) ⟨H, hH, rfl⟩
      exact g.injective he ▸ hy
    · intro a ha
      simpa using hs (g a) ((F.mem_map_vertices g a).mpr ha)
  · rintro ⟨hd, hr, hh, hs⟩
    refine ⟨by simpa [map] using hd, by simpa [map] using hr, ?_, ?_⟩
    · rintro _ ⟨H, hH, rfl⟩
      exact ⟨x, hh H hH, rfl⟩
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
      simpa using hs b hb

@[simp] theorem WFanGeometry.map_allowed (F : WFanGeometry E)
    (g : E ≃ᵃⁱ[ℝ] E) (x : E) :
    (F.map g).Allowed (g x) ↔ F.Allowed x := by
  simp [Allowed]

/-- Each parameterized fan may be placed by its own isometry; W continues
to quantify over exactly the original integer and real parameter domains. -/
theorem W.map (p1 : P1) (chart : PolygonParameter → WFan → WFanGeometry E)
    (hW : W p1 chart) (g : PolygonParameter → WFan → E ≃ᵃⁱ[ℝ] E) :
    W p1 (fun n f => (chart n f).map (g n f)) := by
  constructor
  · intro n f hn hf p p'
    dsimp only
    intro hp hp' hd
    let u := g n f
    obtain ⟨x, rfl⟩ := u.surjective p
    obtain ⟨y, rfl⟩ := u.surjective p'
    have hx : (chart n f).Admissible x ∨ (chart n f).Allowed x := by
      simpa [u] using hp
    have hy : (chart n f).Admissible y ∨ (chart n f).Allowed y := by
      simpa [u] using hp'
    have hxy : chord 17 ≤ dist x y := by simpa using hd
    obtain ⟨hfx, hfy⟩ := hW.no_long_pair n f hn hf x y hx hy hxy
    exact ⟨((chart n f).mem_map_vertices u x).mpr hfx,
      ((chart n f).mem_map_vertices u y).mpr hfy⟩
  · intro n f hn hf p hp p' hp' hpair
    let u := g n f
    obtain ⟨x, rfl⟩ := u.surjective p
    obtain ⟨y, rfl⟩ := u.surjective p'
    have hx : x ∈ (chart n f).vertices := by simpa [u] using hp
    have hy : y ∈ (chart n f).vertices := by simpa [u] using hp'
    have hxy : ¬ (chart n f).specialPair x y := by
      simpa [WFanGeometry.map, u] using hpair
    simpa using hW.fan_distances n f hn hf x hx y hy hxy

end Uniform5.CaseB
