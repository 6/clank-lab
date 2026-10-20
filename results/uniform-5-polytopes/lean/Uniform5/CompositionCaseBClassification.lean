import Uniform5.CompositionSingleLargeClassification
import Uniform5.CompositionTwoLargeFaces
import Uniform5.CompositionTypeIReduction
import Uniform5.CompositionTypeIIReduction
import Uniform5.CompositionWedgeTypeIIIExclusion
import Uniform5.CompositionPairedTypeIProduct
import Uniform5.CompositionPairedMixedProduct
import Uniform5.CompositionPairedTypeIIImpossible

/-! Complete actual Case B composition. The incidence cycles, one/two-face
split, common facet, finite paired cases, and global products are derived
from actual unit uniformity and the named computed inputs. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem unitUniform5_largeFace_known
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    (p1 : CaseB.P1) (partner : CaseB.PartnerRadiusFilter) (hW : Wedge.W p1)
    {P : Set (Space 5)} (hP : UnitUniform 5 P) (hlarge : LargeFace P) : Known P := by
  classical
  obtain ⟨G, n, hG, hn⟩ := hlarge
  obtain ⟨v, hvG⟩ := finitePolytope_extremePoints_nonempty
    (finitePolytope_face (uniform_finitePolytope hP.1) hG.1 (polygonFace_nonempty hG))
  by_cases hu : UniqueLargeFaceAt P v G
  · exact Or.inr (Or.inr (unitUniform5_single_large_polygon_mem_K3
      classification3D classification4D N S hLIB hS1 hB2 hP hG hn hvG hu))
  obtain ⟨H, m, hH, hm, hvH, hHG⟩ := not_uniqueLargeFaceAt_witness hu
  have hGH := hHG.symm
  obtain ⟨D, geometry⟩ := unitUniform5_stage1_geometry hP hG
  obtain ⟨A, _⟩ := unitUniform5_stage1_geometry hP hH
  have hD : D.CaseBTypeI n ∨ D.CaseBTypeII n := by
    rcases D.nonexceptional_cycle_types classification4D hP hG
      (large_polygon_nonexceptional hn) with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (D.typeIII_impossible classification3D classification4D N S
        hLIB hS1 hB2 p1 hW hP hG hn hvG h).elim
  have hA : A.CaseBTypeI m ∨ A.CaseBTypeII m := by
    rcases A.nonexceptional_cycle_types classification4D hP hH
      (large_polygon_nonexceptional hm) with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (A.typeIII_impossible classification3D classification4D N S
        hLIB hS1 hB2 p1 hW hP hH hm hvH h).elim
  have hreduction : TwoLargeFacesCoverAt P v G H ∧
      ∃ K, Facet P K ∧ G ⊆ K ∧ H ⊆ K := by
    rcases hD with hI | hII
    · exact D.typeI_two_large_reduction classification4D p1 partner hW hP hG hn
        hvG geometry hI hH hm hvH hGH
    · exact D.typeII_two_large_reduction p1 hW hP hG hn hvG hII hH hm hvH hGH
  obtain ⟨hcover, K, hK, hGK, hHK⟩ := hreduction
  rcases hD with hI | hII <;> rcases hA with hJ | hJJ
  · exact Or.inr (Or.inl (unitUniform5_paired_typeI_mem_K2
      classification3D classification4D N S hLIB hS1 hB2 hP hG hn hH hm
      hvG hvH hGH hcover hK hGK hHK D A hI hJ))
  · exact Or.inr (Or.inr (unitUniform5_paired_mixed_mem_K3
      classification3D classification4D N S hLIB hS1 hB2 hP hG hn hH hm
      hvG hvH hGH hcover hK hGK hHK D A hI hJJ))
  · have hrev : TwoLargeFacesCoverAt P v H G := fun F k hF hk hvF =>
      (hcover F k hF hk hvF).symm
    exact Or.inr (Or.inr (unitUniform5_paired_mixed_mem_K3
      classification3D classification4D N S hLIB hS1 hB2 hP hH hm hG hn
      hvH hvG hHG hrev hK hHK hGK A D hJ hII))
  · exact (unitUniform5_paired_typeII_impossible classification3D classification4D
      N S hLIB hS1 hB2 hP hG hn hH hm hvG hvH hGH hcover hK hGK hHK D A hII hJJ).elim

end Uniform5.Composition
