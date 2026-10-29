import CanonicalCellLabels
import CellWalkSequence

namespace ADKZPricing
open Matrix Finset
noncomputable section

/-- Complementary original zero labels in the central cell give the
    actual complementary canonical sign vectors used by the transition
    theorem. The source endpoint labels are not replaced by a diameter. -/
theorem central_canonical_complementary {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℝ) (hn : d < n)
    (hu : RowUniform A)
    (Z W : Finset (Fin n)) (hz : ChartVertex A none Z) (hw : ChartVertex A none W)
    (hcomp : ∀ i, i ∈ Z ↔ i ∉ W) :
    ∀ i, (canonicalSigns A Z i = 0 ∧ canonicalSigns A W i = 1) ∨
      (canonicalSigns A Z i = 1 ∧ canonicalSigns A W i = 0) := by
  have hZ := canonical_signs_cell A hn hu none Z hz
  have hW := canonical_signs_cell A hn hu none W hw
  intro i
  have hpZ : 0 ≤ canonicalSigns A Z i := by simpa [starSign] using hZ.1 i
  have hpW : 0 ≤ canonicalSigns A W i := by simpa [starSign] using hW.1 i
  have hvZ := realSign_cases (A i ⬝ᵥ canonicalVertex A Z)
  have hvW := realSign_cases (A i ⬝ᵥ canonicalVertex A W)
  change canonicalSigns A Z i = -1 ∨ canonicalSigns A Z i = 0 ∨ canonicalSigns A Z i = 1 at hvZ
  change canonicalSigns A W i = -1 ∨ canonicalSigns A W i = 0 ∨ canonicalSigns A W i = 1 at hvW
  by_cases hi : i ∈ Z
  · have h0 := (hZ.2 i).mpr hi
    have hn0 : canonicalSigns A W i ≠ 0 := fun h => (hcomp i).mp hi ((hW.2 i).mp h)
    exact Or.inl ⟨h0, by omega⟩
  · have h0 : canonicalSigns A W i = 0 := by
      apply (hW.2 i).mpr
      by_contra hout
      exact hi ((hcomp i).mpr hout)
    have hn0 : canonicalSigns A Z i ≠ 0 := fun h => hi ((hZ.2 i).mp h)
    exact Or.inr ⟨by omega, h0⟩

/-- The two ACTUAL closed cell graphs retain their shared-facet vertices
    and edges. A short union path becomes a central path because its
    single canonical sign sequence cannot spend a negative coordinate. -/
theorem factor_cell_union_lower_bound
    (A : Matrix (Fin 40) (Fin 21) ℝ)
    (hu : RowUniform A)
    (Z W : Finset (Fin 40)) (hz : ChartVertex A none Z) (hw : ChartVertex A none W)
    (hcomp : ∀ i, i ∈ Z ↔ i ∉ W)
    (hcentral : ∀ k, LabelledCell.CellWalk (chartCell A none) Z W k → 21 ≤ k)
    (e : Fin 40) {L : ℕ}
    (h : LabelledCell.CellWalk (LabelledCell.union (chartCell A none) (chartCell A (some e))) Z W L) :
    21 ≤ L := by
  have hn : 20 < 40 := by decide
  obtain ⟨p, hp0, hpL, hv, he⟩ := h.sequence
  let q : ℕ → Fin 40 → ℤ := fun j => canonicalSigns A (p j)
  have hend : ∀ i, (q 0 i = 0 ∧ q L i = 1) ∨ (q 0 i = 1 ∧ q L i = 0) := by
    simpa only [q, hp0, hpL] using central_canonical_complementary A hn hu Z W hz hw hcomp
  have hsteps : ∀ j, j < L → ∑ i, |q (j + 1) i - q j i| ≤ (2 : ℤ) := by
    intro j hj
    rcases he j hj with hc | hc
    · exact le_of_eq (canonical_edge_variation A hn hu none (p j) (p (j + 1)) hc)
    · exact le_of_eq (canonical_edge_variation A hn hu (some e) (p j) (p (j + 1)) hc)
  apply factor_union_transition_lower_bound q L hend (fun _ _ _ => realSign_cases _) hsteps
  intro hnonneg
  have hverts : ∀ j, j ≤ L → (chartCell A none).vertex (p j) := by
    intro j hj
    rcases hv j hj with hc | hc
    · exact hc
    · exact canonical_nonnegative_central A hn hu (some e) (p j) hc (hnonneg j hj)
  have hedges : ∀ j, j < L → (chartCell A none).edge (p j) (p (j + 1)) := by
    intro j hj
    refine ⟨hverts j (by omega), hverts (j + 1) (by omega), ?_⟩
    rcases he j hj with hc | hc
    · exact hc.2.2
    · exact hc.2.2
  have hp := LabelledCell.CellWalk.of_sequence (chartCell A none) L p hverts hedges
  rw [hp0, hpL] at hp
  exact hcentral L hp

#print axioms central_canonical_complementary
#print axioms factor_cell_union_lower_bound
end
end ADKZPricing
