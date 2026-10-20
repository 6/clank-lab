import Uniform5.CompositionPairedMixedActual

/-! The actual four-slot Type I and three-slot Type II fan vertex sets
both have exactly six elements, proved from their injective charts. -/
noncomputable section
namespace Uniform5.Composition
open Set

private theorem six_range_ncard {E : Type*} (f : Fin 6 → E) (hf : Function.Injective f) :
    (Set.range f).ncard = 6 := by
  rw [← Set.image_univ, Set.ncard_image_of_injective _ hf, Set.ncard_univ]
  simp

namespace TypeIFanChart
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIFanChart D v n)

theorem four_fan_vertices_range (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hvG : v ∈ G.extremePoints ℝ) (hlen : D.length = 4) (j : Fin D.length) :
    actualPolygonFanVertices hP D v = Set.range (T.pairedSixLabels hlen j) := by
  ext x
  constructor
  · intro hx
    rcases (T.mem_fan_vertices hP hG hvG x).mp hx with rfl | rfl | ⟨i, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · rcases finRotate_four_enumeration hlen j i with rfl | rfl | rfl | rfl
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
  · rintro ⟨i, rfl⟩
    exact T.pairedSixLabels_mem_fan hP hG hvG hlen j i

include T in
theorem four_fan_vertices_ncard (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hvG : v ∈ G.extremePoints ℝ) (hlen : D.length = 4) :
    (actualPolygonFanVertices hP D v).ncard = 6 := by
  let j : Fin D.length := ⟨0, by omega⟩
  rw [T.four_fan_vertices_range hP hG hvG hlen j]
  exact six_range_ncard _ (T.pairedSixLabels hlen j).injective

end TypeIFanChart
namespace TypeIIActualFanData
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIIActualFanData D v n)

theorem fan_vertices_range (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hvG : v ∈ G.extremePoints ℝ) :
    actualPolygonFanVertices hP D v = Set.range T.points := by
  ext x
  rw [T.mem_fan_vertices hP hG hn hvG]
  simp [points, Set.mem_range, Fin.exists_fin_succ, eq_comm]
  tauto

include T in
theorem fan_vertices_ncard (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hvG : v ∈ G.extremePoints ℝ) :
    (actualPolygonFanVertices hP D v).ncard = 6 := by
  rw [T.fan_vertices_range hP hG hn hvG]
  exact six_range_ncard _ (T.points_injective hG (by omega))

end TypeIIActualFanData
end Uniform5.Composition
