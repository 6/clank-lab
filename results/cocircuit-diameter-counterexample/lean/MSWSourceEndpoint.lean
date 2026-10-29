import MSWEndpointAssembly

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace ADKZPricing
open Matrix Finset
noncomputable section

def mswMinusLabels : Finset (Fin 40) := univ.filter (fun i => i.val < 20)
def mswPlusLabels : Finset (Fin 40) := univ.filter (fun i => 20 ≤ i.val)

theorem msw_source_chart_vertices :
    ChartVertex mswSource none mswMinusLabels ∧ ChartVertex mswSource none mswPlusLabels := by
  constructor
  · refine ⟨by decide, mswMinus, rfl, msw_endpoint_feasible.1, ?_⟩
    intro i
    simpa [mswMinusLabels] using (msw_endpoint_labels i).1
  · refine ⟨by decide, mswPlus, rfl, msw_endpoint_feasible.2, ?_⟩
    intro i
    simpa [mswPlusLabels] using (msw_endpoint_labels i).2

theorem rowScaled_chart_vertex {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) ℚ)
    (s : Fin n → ℚ) (hs : ∀ i, 0 < s i) (c : Option (Fin n)) (Z : Finset (Fin n))
    (hz : ChartVertex A c Z) : ChartVertex (rowScaled A s) c Z := by
  obtain ⟨hc, v, hv0, hf, he⟩ := hz
  refine ⟨hc, v, hv0, (rowScaled_star_iff A s hs c v).mpr hf, ?_⟩
  intro i
  exact ((rowScaled_signed_slacks A s hs (starSign c) v i).2).trans (he i)

theorem central_chart_vertex_real {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℚ) (Z : Finset (Fin n))
    (hz : ChartVertex A none Z) : ChartVertex (A.map (Rat.castHom ℝ)) none Z := by
  obtain ⟨hc, v, hv0, hf, he⟩ := hz
  let w : Fin (d + 1) → ℝ := fun j => (v j : ℝ)
  have hd (i : Fin n) : (A.map (Rat.castHom ℝ)) i ⬝ᵥ w = ((A i ⬝ᵥ v : ℚ) : ℝ) := by
    simp [dotProduct, w]
  refine ⟨hc, w, ?_, ?_, ?_⟩
  · change (v 0 : ℝ) = 1
    exact_mod_cast hv0
  · intro i
    change 0 ≤ starSign none i * ((A.map (Rat.castHom ℝ)) i ⬝ᵥ w)
    simp only [starSign, reduceCtorEq, if_false, one_mul, hd]
    have hp := hf i
    change 0 ≤ starSign none i * (A i ⬝ᵥ v) at hp
    simp only [starSign, reduceCtorEq, if_false, one_mul] at hp
    exact_mod_cast hp
  · intro i
    rw [hd, Rat.cast_eq_zero]
    exact he i

theorem msw_integral_origin_positive (i : Fin 40) : 0 < mswIntegralA i 0 := by
  have hp : (0 : ℚ) < (mswIntegralA i 0 : ℚ) := by
    rw [mswIntegral_positive_scaling]
    exact mul_pos (by exact_mod_cast mswIntegral_scales_positive i) (msw_origin_strict i)
  exact_mod_cast hp

theorem msw_integral_real_vertices :
    ChartVertex ((mswIntegralA.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) none mswMinusLabels ∧
    ChartVertex ((mswIntegralA.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) none mswPlusLabels := by
  have lift (Z : Finset (Fin 40)) (hZ : ChartVertex mswSource none Z) :
      ChartVertex ((mswIntegralA.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) none Z := by
    apply central_chart_vertex_real
    rw [msw_integer_source_binding]
    exact rowScaled_chart_vertex mswSource _
      (fun i => by exact_mod_cast mswIntegral_scales_positive i) none Z hZ
  exact ⟨lift _ msw_source_chart_vertices.1, lift _ msw_source_chart_vertices.2⟩

/-- Final finite-input interface, still CONDITIONAL. The original source
matrix and the specified minus/plus pair are literal. Only the complete
finite source certificate and its checked local potential with gap21 are
missing; there is no residual chart, genericity, adjacency or graph premise. -/
theorem msw_endpoint_of_source_certificate {V : Type*} [Fintype V] [Nonempty V]
    (S : SourceVertexCertificate (sourceSpatial (mswIntegralA.map (Int.castRingHom ℚ)))
      (sourceBound (mswIntegralA.map (Int.castRingHom ℚ))) V)
    (P : Finset (Fin 40) → ℤ)
    (hP : ∀ v j, P (S.labels (S.next v j)) ≤ P (S.labels v) + 1)
    (hgap : (21 : ℤ) ≤ P mswPlusLabels - P mswMinusLabels) : ProposedEndpoint := by
  have hv := msw_integral_real_vertices
  have he (Z : Finset (Fin 40)) := first_source_real_chart_vertices mswIntegralA
    mswIntegralStarChart mswIntegralChart_pivot S 0 msw_integral_origin_positive (by decide) Z
  apply msw_endpoint_of_factor_distance mswMinusLabels mswPlusLabels
    ((he _).mpr hv.1) ((he _).mpr hv.2)
  · intro i
    simp [mswMinusLabels, mswPlusLabels]
  · intro L h
    exact first_source_central_distance mswIntegralA mswIntegralStarChart
      mswIntegralChart_pivot S 0 msw_integral_origin_positive (by decide)
      P hP mswMinusLabels mswPlusLabels 21 hgap h

#print axioms msw_source_chart_vertices
#print axioms msw_integral_real_vertices
#print axioms msw_endpoint_of_source_certificate
end
end ADKZPricing
