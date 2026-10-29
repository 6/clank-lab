import MSWPathTransport
import ProductUnionDistance
import FirstSourceDistance

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace ADKZPricing
open Matrix Finset
noncomputable section

theorem productLabelPair_join {n m : ℕ} (Z : Finset (Fin n)) (W : Finset (Fin m)) :
    productLabelPair (productLabels Z W) = (Z, W) := by
  apply Prod.ext <;> ext i
  · simp [productLabelPair, leftLabels, productLabels_left]
  · simp [productLabelPair, rightLabels, productLabels_right]

theorem productLabels_complement {n m : ℕ}
    (Z Z' : Finset (Fin n)) (W W' : Finset (Fin m))
    (hZ : ∀ i, i ∈ Z ↔ i ∉ Z') (hW : ∀ i, i ∈ W ↔ i ∉ W') :
    ∀ i, i ∈ productLabels Z W ↔ i ∉ productLabels Z' W' := by
  intro i
  refine Fin.addCases (m := n) (n := m)
    (motive := fun i => i ∈ productLabels Z W ↔ i ∉ productLabels Z' W')
    (fun j => ?_) (fun j => ?_) i
  · simpa only [productLabels_left] using hZ j
  · simpa only [productLabels_right] using hW j

theorem chart_vertex_cocircuit (A : Matrix (Fin 80) (Fin 41) ℚ) (hu : Uniform A)
    (c : Option (Fin 80)) (Z : Finset (Fin 80))
    (hz : ChartVertex (A.map (Rat.castHom ℝ)) c Z) :
    Cocircuit A (cellLabelSigns c Z) := by
  obtain ⟨hc, v, _, hf, hv⟩ := hz
  have hs := feasible_complete_signs A c Z v hf hv
  have hcov : Covector A (cellLabelSigns c Z) := ⟨v, fun i => (congrFun hs i).symm⟩
  apply (uniform_covector_cocircuit_iff A hu _ hcov (cellLabelSigns_nonzero c Z hc)).mpr
  rw [cellLabelSigns_zeros, hc]

theorem central_labels_complementary (Z W : Finset (Fin 80))
    (hz : Z.card = 40) (hw : W.card = 40) (hcomp : ∀ i, i ∈ Z ↔ i ∉ W) :
    Complementary (cellLabelSigns none Z) (cellLabelSigns none W) := by
  refine ⟨?_, ?_, ?_⟩
  · change (signZeros (cellLabelSigns none Z)).card = 40
    rw [cellLabelSigns_zeros, hz]
  · change (signZeros (cellLabelSigns none W)).card = 40
    rw [cellLabelSigns_zeros, hw]
  · intro i
    by_cases hi : i ∈ Z
    · have hw' := (hcomp i).mp hi
      exact Or.inl (by simp [cellLabelSigns, starSign, hi, hw'])
    · have hw' : i ∈ W := by simpa using mt (hcomp i).mpr hi
      exact Or.inr (by simp [cellLabelSigns, starSign, hi, hw'])

theorem first_factor_row_uniform {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A) (h0 : 0 < C.chart 0) :
    RowUniform ((chartedGenericFactor A C).map (Rat.castHom ℝ)) :=
  (chartedGenericFactor_real_properties A C h0).1

/-- Conditional assembly, NOT a proof of ProposedEndpoint: the actual
source's specified central21 bound and its endpoint labels still must be
supplied by the complete finite source discovery/checking pipeline. Every
matrix, chart, product, full-graph and fixed-cell path premise below is
instantiated by the actual MSW construction. -/
theorem msw_endpoint_of_factor_distance (Z W : Finset (Fin 40))
    (hz : ChartVertex (mswFirstFactor.map (Rat.castHom ℝ)) none Z)
    (hw : ChartVertex (mswFirstFactor.map (Rat.castHom ℝ)) none W)
    (hcomp : ∀ i, i ∈ Z ↔ i ∉ W)
    (hcentral : ∀ L, LabelledCell.CellWalk
      (chartCell (mswFirstFactor.map (Rat.castHom ℝ)) none) Z W L → 21 ≤ L) :
    ProposedEndpoint := by
  let F := mswFirstFactor.map (Rat.castHom ℝ)
  have hu : RowUniform F := first_factor_row_uniform mswIntegralA mswIntegralStarChart mswIntegralChart_pivot
  have lift (U : Finset (Fin 40)) (hv : ChartVertex F none U) :
      ChartVertex (mswFinalMatrix.map (Rat.castHom ℝ)) none (productLabels U U) := by
    apply (second_chart_vertex_pair mswIntegralA mswIntegralStarChart mswIntegralChart_pivot
      (by decide) none (productLabels U U)).mpr
    rw [productLabelPair_join]
    exact (product_uniform_vertex F F hu hu none U U).mpr ⟨hv, hv⟩
  have hz' := lift Z hz
  have hw' := lift W hw
  have hc := central_labels_complementary _ _ hz'.1 hw'.1
    (productLabels_complement Z W Z W hcomp hcomp)
  refine ⟨mswFinalMatrix, mswFinal_uniform, cellLabelSigns none (productLabels Z Z),
    cellLabelSigns none (productLabels W W),
    chart_vertex_cocircuit _ mswFinal_uniform _ _ hz',
    chart_vertex_cocircuit _ mswFinal_uniform _ _ hw', hc, ?_⟩
  intro hs
  obtain ⟨L, hL, e, hp⟩ := msw_short_walk_product_union _ _ hc hs
  rw [cellLabelSigns_zeros, cellLabelSigns_zeros, productLabelPair_join, productLabelPair_join] at hp
  have hb := product_star_union_distance F hu Z W hz hw hcomp hcentral e hp
  omega

#print axioms chart_vertex_cocircuit
#print axioms msw_endpoint_of_factor_distance
end
end ADKZPricing
