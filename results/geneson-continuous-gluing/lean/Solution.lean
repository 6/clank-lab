import Compactness
import MeasureTransfer


noncomputable section
open Set MeasureTheory
namespace Geneson

/-- Geneson (2021), Conjecture 6.3, for arbitrary planar sets. -/
theorem conjecture63 : Conjecture63 := by
  intro n hn P Q c d hp hq hP hQ
  have hPn : P.Nonempty := ⟨(c,d),hp⟩
  have hQn : Q.Nonempty := ⟨(c,d),hq⟩
  have hPc : AvoidingCollars n P := fun C hC hCi havoid =>
    exists_open_avoiding_superset hC hCi havoid
  have hQc : AvoidingCollars n Q := fun C hC hCi havoid =>
    exists_open_avoiding_superset hC hCi havoid
  apply opx_le_of_open_bounds (hPn.mono subset_union_left)
  intro S hSo hSsq hSavoid
  apply area_le_of_compact_bounds hSo.measurableSet
    (add_nonneg (opx_nonneg n hPn) (opx_nonneg n hQn))
  intro K hKS hK
  let A : Set Plane := AnchorSet P K ⟨(c,d),hp⟩
  have hKsq : K ⊆ Square n := hKS.trans hSsq
  have hKAvoid : ¬ Contains (P ∪ Q) K :=
    fun h => hSavoid (contains_mono hKS h)
  have hAc : IsCompact A := isCompact_anchorSet _ hK hKsq
  exact area_le_opx_add_of_partition hPn hQn hK.measurableSet hAc.measurableSet
    (anchorSet_subset _) hKsq (anchorSet_avoids_right hp hq hP hQ hKAvoid)
    (sdiff_anchorSet_avoids_left _) hPc hQc

/-- Expanded, directly inspectable source endpoint, without auxiliary hypotheses. -/
theorem geneson_conjecture_6_3
    (n : ℝ) (hn : 0 < n) (P Q : Set Plane) (c d : ℝ)
    (hp : (c,d) ∈ P) (hq : (c,d) ∈ Q)
    (hP : ∀ p ∈ P, p.1 ≤ c ∧ p.2 ≤ d)
    (hQ : ∀ q ∈ Q, c ≤ q.1 ∧ d ≤ q.2) :
    opx n (P ∪ Q) ≤ opx n P + opx n Q :=
  conjecture63 n hn P Q c d hp hq hP hQ

end Geneson
