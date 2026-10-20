import Uniform5.CompositionActualDuoprismChart
import Uniform5.CompositionFacetSystemGeneral

/-! Two distinct facets at a simple four-dimensional vertex cover all its
neighbors. This supplies the middle-duoprism step of the Type II fan. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem finitePolytope_simpleVertex_two_facets_cover {K A B : Set E} {v w : E}
    (hK : FinitePolytope K) (hd : affineDimension K = 4)
    (hv : v ∈ K.extremePoints ℝ)
    (hfour : (geometricNeighbours K hK v).card = 4)
    (hA : Facet K A) (hB : Facet K B) (hvA : v ∈ A) (hvB : v ∈ B)
    (hne : A ≠ B) (he : Edge K v w) : w ∈ A ∨ w ∈ B := by
  classical
  let FA : FacesAt K v := ⟨⟨A, hA.1⟩, hvA⟩
  let FB : FacesAt K v := ⟨⟨B, hB.1⟩, hvB⟩
  let W : geometricNeighbours K hK v := ⟨w, (mem_geometricNeighbours K hK v w).mpr he⟩
  let T : Finset (geometricNeighbours K hK v) := Finset.univ.erase W
  have ht : T.card = 3 := by simp [T, hfour]
  have hcA := (finitePolytope_simpleVertex_facet_iff_three hK hd hv hfour FA).mp hA
  have hcB := (finitePolytope_simpleVertex_facet_iff_three hK hd hv hfour FB).mp hB
  by_contra hh
  have hnA : w ∉ A := fun hw => hh (Or.inl hw)
  have hnB : w ∉ B := fun hw => hh (Or.inr hw)
  have sub (F : FacesAt K v) (hn : w ∉ F.val.val) : neighboursIn K hK v F ⊆ T := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun heq => hn (by
      have hm := (mem_neighboursIn K hK v F x).mp hx
      simpa [heq, W] using hm), Finset.mem_univ x⟩
  have hEq : neighboursIn K hK v FA = neighboursIn K hK v FB :=
    (Finset.eq_of_subset_of_card_le (sub FA hnA) (by omega)).trans
      (Finset.eq_of_subset_of_card_le (sub FB hnB) (by omega)).symm
  let L := finitePolytope_simpleVertexFaceLattice hK hd hv hfour
  have hFaces : FA = FB := L.faceEquiv.injective (by rw [L.incidence, L.incidence, hEq])
  exact hne (congrArg (fun F : FacesAt K v => F.val.val) hFaces)

theorem DuoprismNeighborChart.neighbour_card {K G : Set E} {v : E} {n q : ℕ}
    (D : DuoprismNeighborChart K G v n q) (hK : UnitUniform 4 K)
    (hv : v ∈ K.extremePoints ℝ) :
    (geometricNeighbours K (uniform_finitePolytope hK.1) v).card = 4 := by
  classical
  have hsub : geometricNeighbours K (uniform_finitePolytope hK.1) v ⊆
      ({D.a, D.b, D.g, D.d} : Finset E) := by
    intro w hw
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      (D.neighbors w).mp ((mem_geometricNeighbours K _ v w).mp hw)
  have hlo := finitePolytope_neighbour_card_lower (uniform_finitePolytope hK.1) hv
    (by rw [uniform_dimension hK.1]; norm_num)
  rw [uniform_dimension hK.1] at hlo
  have hhi := Finset.card_le_card hsub
  have hbound : ({D.a, D.b, D.g, D.d} : Finset E).card ≤ 4 := by
    have h₁ := Finset.card_insert_le D.a ({D.b, D.g, D.d} : Finset E)
    have h₂ := Finset.card_insert_le D.b ({D.g, D.d} : Finset E)
    have h₃ := Finset.card_insert_le D.g ({D.d} : Finset E)
    simp only [Finset.card_singleton] at h₃
    omega
  omega

end Uniform5.Composition
