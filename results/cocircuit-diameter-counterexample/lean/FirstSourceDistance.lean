import ChartVertexTransport

namespace ADKZPricing
open Matrix Finset
noncomputable section

/-- Preserve the finite data definitionally while checking every cast
of the source inequalities. No equality transport hides the basis or
neighbor arrays from the potential certificate. -/
def labelledRealSourceCertificate {n d : ℕ} {V : Type*}
    (A : Matrix (Fin n) (Fin (d + 1)) ℚ)
    (S : SourceVertexCertificate (sourceSpatial A) (sourceBound A) V) :
    SourceVertexCertificate (sourceSpatial (A.map (Rat.castHom ℝ)))
      (sourceBound (A.map (Rat.castHom ℝ))) V where
  point v j := (S.point v j : ℝ)
  basis := S.basis
  next := S.next
  feasible v i := by
    simpa only [sourceSpatial, sourceBound, Matrix.map_apply, Rat.coe_castHom,
      Rat.cast_neg] using S.toReal.feasible v i
  basis_injective := S.basis_injective
  active_exact v i := by
    simpa only [sourceSpatial, sourceBound, Matrix.map_apply, Rat.coe_castHom,
      Rat.cast_neg] using S.toReal.active_exact v i
  neighbor_keeps v j k hk := by
    simpa only [sourceSpatial, sourceBound, Matrix.map_apply, Rat.coe_castHom,
      Rat.cast_neg] using S.toReal.neighbor_keeps v j k hk
  neighbor_leaves v j := by
    simpa only [sourceSpatial, sourceBound, Matrix.map_apply, Rat.coe_castHom,
      Rat.cast_neg] using S.toReal.neighbor_leaves v j

/-- Every actual first-factor central path maps to the complete covered
source cell with identical zero labels. The finite source instance and
its potential inequalities remain explicit obligations. -/
theorem first_source_central_distance {n d : ℕ} {V : Type*} [Fintype V] [Nonempty V]
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A) (h0 : 0 < C.chart 0)
    (S : SourceVertexCertificate (sourceSpatial (A.map (Int.castRingHom ℚ)))
      (sourceBound (A.map (Int.castRingHom ℚ))) V)
    (i₀ : Fin n) (ha : ∀ i, 0 < A i 0) (hn : d < n)
    (P : Finset (Fin n) → ℤ)
    (hP : ∀ v j, P (S.labels (S.next v j)) ≤ P (S.labels v) + 1)
    (Z W : Finset (Fin n)) (D : ℕ) (hD : (D : ℤ) ≤ P W - P Z)
    {L : ℕ} (h : LabelledCell.CellWalk
      (chartCell ((chartedGenericFactor A C).map (Rat.castHom ℝ)) none) Z W L) : D ≤ L := by
  let SR := labelledRealSourceCertificate (A.map (Int.castRingHom ℚ)) S
  have hp : ∀ v j, P (SR.labels (SR.next v j)) ≤ P (SR.labels v) + 1 := hP
  apply source_chart_distance _ SR P hp Z W D hD
  apply h.transfer
  · intro z hz
    exact (first_source_real_chart_vertices A C h0 S i₀ ha hn z).mp hz
  · intro z w he
    exact ⟨(first_source_real_chart_vertices A C h0 S i₀ ha hn z).mp he.1,
      (first_source_real_chart_vertices A C h0 S i₀ ha hn w).mp he.2.1, he.2.2⟩

#print axioms first_source_central_distance
end
end ADKZPricing
