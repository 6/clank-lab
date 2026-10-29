import ChartRepair
import PositiveScaling
import ProductRegularity

namespace ADKZPricing
open Matrix Finset
noncomputable section

theorem signed_rows_det {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℤ)
    (c : Option (Fin n)) (f : Fin r → Fin n) (hd : (A.submatrix f id).det ≠ 0) :
    ((rowScaled A (starSign c)).submatrix f id).det ≠ 0 := by
  change Matrix.det (fun i j => (starSign c (f i) : ℤ) * A (f i) j) ≠ 0
  have he := Matrix.det_mul_column (fun i => (starSign c (f i) : ℤ)) (A.submatrix f id)
  change Matrix.det (fun i j => (starSign c (f i) : ℤ) * A (f i) j) =
    (∏ i, starSign c (f i)) * (A.submatrix f id).det at he
  rw [he]
  apply mul_ne_zero _ hd
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  unfold starSign
  split_ifs <;> norm_num

theorem specialized_signed_rows {n r : ℕ} (A D : Matrix (Fin n) (Fin r) ℤ)
    (c : Option (Fin n)) (t : ℚ) :
    specializedMatrix (rowScaled A (starSign c)) (rowScaled D (starSign c)) t =
      rowScaled (specializedMatrix A D t) (starSign c) := by
  ext i j
  simp only [specializedMatrix, rowScaled, Int.cast_mul]
  have hs : ((starSign c i : ℤ) : ℚ) = starSign c i := by
    unfold starSign
    split_ifs <;> norm_num
  rw [hs]
  ring

theorem starSign_abs_mul {n : ℕ} (c : Option (Fin n)) (i : Fin n) (a : ℤ) :
    |starSign c i * a| = |a| := by
  unfold starSign
  split_ifs <;> simp

/-- Finite exact input facts for a common chart. The representation is
    for every ORIGINAL signed row set, including the central cell.
    No regularity, genericity or perturbed-chart assertion is a field. -/
structure IntegralStarChart {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℤ) where
  chart : Fin r → ℤ
  weights : Option (Fin n) → Fin n → ℤ
  positive : ∀ c i, 0 < weights c i
  representation : ∀ c j, chart j = ∑ i, weights c i * (starSign c i * A i j)
  basis : Fin r → Fin n
  basis_injective : Function.Injective basis
  basis_det : (A.submatrix basis id).det ≠ 0

def entryMass {I J : Type*} [Fintype I] [Fintype J] (A : I → J → ℤ) : ℤ :=
  ∑ i, ∑ j, |A i j|

theorem entryMass_nonnegative {I J : Type*} [Fintype I] [Fintype J] (A : I → J → ℤ) :
    0 ≤ entryMass A := sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => abs_nonneg _))

theorem entryMass_bounds {I J : Type*} [Fintype I] [Fintype J] (A : I → J → ℤ)
    (i : I) (j : J) : |A i j| ≤ entryMass A := by
  classical
  apply (single_le_sum (fun k _ => abs_nonneg (A i k)) (mem_univ j)).trans
  exact single_le_sum (fun k _ => sum_nonneg (fun l _ => abs_nonneg (A k l))) (mem_univ i)

def chartDrift {n r : ℕ} (A D : Matrix (Fin n) (Fin r) ℤ) (C : IntegralStarChart A) :
    Option (Fin n) → Fin r → ℤ := fun c j => ∑ i, C.weights c i * (starSign c i * D i j)

/-- A computable single coefficient envelope, with no enumeration of bases.
    It covers the input, Vandermonde direction, every chart weight/drift,
    and the chart itself. All signs are included in the drift sum. -/
def starEnvelope {n r : ℕ} (A D : Matrix (Fin n) (Fin r) ℤ) (C : IntegralStarChart A) : ℤ :=
  1 + entryMass A + entryMass D + entryMass C.weights + entryMass (chartDrift A D C) +
    entryMass (fun _ : Fin 1 => C.chart)

theorem starEnvelope_bounds {n r : ℕ} (A D : Matrix (Fin n) (Fin r) ℤ)
    (C : IntegralStarChart A) :
    1 ≤ starEnvelope A D C ∧
    (∀ i j, |A i j| ≤ starEnvelope A D C) ∧
    (∀ i j, |D i j| ≤ starEnvelope A D C) ∧
    (∀ c i, |C.weights c i| ≤ starEnvelope A D C) ∧
    (∀ c j, |chartDrift A D C c j| ≤ starEnvelope A D C) ∧
    (∀ j, |C.chart j| ≤ starEnvelope A D C) := by
  have hA := entryMass_nonnegative A
  have hD := entryMass_nonnegative D
  have hW := entryMass_nonnegative C.weights
  have hQ := entryMass_nonnegative (chartDrift A D C)
  have hH := entryMass_nonnegative (fun _ : Fin 1 => C.chart)
  unfold starEnvelope
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j; have h := entryMass_bounds A i j; omega
  · intro i j; have h := entryMass_bounds D i j; omega
  · intro c i; have h := entryMass_bounds C.weights c i; omega
  · intro c j; have h := entryMass_bounds (chartDrift A D C) c j; omega
  · intro j; have h := entryMass_bounds (fun _ : Fin 1 => C.chart) 0 j; omega

def chartedGenericFactor {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) ℤ)
    (C : IntegralStarChart A) : Matrix (Fin n) (Fin (d + 1)) ℚ :=
  chartRebased (specializedMatrix A integerVandermonde
    (commonParameter (d + 1) (starEnvelope A integerVandermonde C)))
    (fun j => (C.chart j : ℚ))

/-- Finite old chart data produce a strict common chart for EVERY star
    cell of the explicit generic specialization. Signed chart repair and
    unsigned genericity use exactly the same parameter. -/
theorem specialized_star_chart {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) ℤ)
    (C : IntegralStarChart A) :
    ∀ c v, StarFeasible (specializedMatrix A integerVandermonde
      (commonParameter (d + 1) (starEnvelope A integerVandermonde C))) c v →
      v ≠ 0 → 0 < (fun j => (C.chart j : ℚ)) ⬝ᵥ v := by
  let D : Matrix (Fin n) (Fin (d + 1)) ℤ := integerVandermonde
  let B := starEnvelope A D C
  have hb := starEnvelope_bounds A D C
  intro c v hv hn
  obtain ⟨θ, hθ, hrep, hdet⟩ := strict_chart_certificate_persistence (by omega)
    (rowScaled A (starSign c)) (rowScaled D (starSign c)) C.basis C.basis_injective
    (C.weights c) C.chart B hb.1
    (fun i j => by simpa only [rowScaled, starSign_abs_mul] using hb.2.1 i j)
    (fun i j => by simpa only [rowScaled, starSign_abs_mul] using hb.2.2.1 i j)
    (hb.2.2.2.1 c) (hb.2.2.2.2.1 c) (C.positive c) (C.representation c)
    (signed_rows_det A c C.basis C.basis_det)
  rw [specialized_signed_rows] at hrep hdet
  apply positive_weighted_chart _ θ _ hθ hrep v
  · intro i
    change 0 ≤ rowScaled (specializedMatrix A D (commonParameter (d + 1) B)) (starSign c) i ⬝ᵥ v
    rw [rowScaled_value]
    exact hv i
  · exact full_rank_detects_nonzero _ C.basis hdet v hn

/-- Uniformity and all strict star charts are now conclusions of the
    explicit construction and finite old certificate, not assumed factor
    properties. This is the input required by product regularity. -/
theorem chartedGenericFactor_properties {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A)
    (h0 : 0 < C.chart 0) :
    (∀ f : Fin (d + 1) → Fin n, Function.Injective f →
      ((chartedGenericFactor A C).submatrix f id).det ≠ 0) ∧
    (∀ c v, StarFeasible (chartedGenericFactor A C) c v → v ≠ 0 → 0 < v 0) := by
  have hb := starEnvelope_bounds A integerVandermonde C
  have h0q : (0 : ℚ) < C.chart 0 := by exact_mod_cast h0
  constructor
  · apply chartRebased_uniform _ _ h0q.ne'
    exact explicit_uniform_specialization (by omega) A _ hb.1 hb.2.1 hb.2.2.1
  · intro c v hv hn
    apply chartRebased_strict_chart _ _ h0q (starSign c) _ v hn hv
    intro w hw hfeas
    exact specialized_star_chart A C c w hfeas hw

/-- Instantiate product regularity with the explicit first perturbation.
    Both copies retain the same original row ordering and common chart.
    Only the finite old chart certificate remains as input data. -/
theorem constructed_product_regularity {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A)
    (h0 : 0 < C.chart 0) (hn : d < n)
    (c : Option (Fin (n + n))) (v : Fin (d + d + 1) → ℚ)
    (hv : StarFeasible (orderedProduct (chartedGenericFactor A C) (chartedGenericFactor A C)) c v)
    (hne : v ≠ 0) (label : Fin (d + d) → Fin (n + n)) (hl : Function.Injective label)
    (ha : ∀ j, orderedProduct (chartedGenericFactor A C) (chartedGenericFactor A C) (label j) ⬝ᵥ v = 0) :
    0 < v 0 ∧
      ((orderedProduct (chartedGenericFactor A C) (chartedGenericFactor A C)).submatrix label Fin.succ).det ≠ 0 ∧
      (∀ i, i ∉ Set.range label →
        0 < starSign c i * (orderedProduct (chartedGenericFactor A C) (chartedGenericFactor A C) i ⬝ᵥ v)) := by
  have hp := chartedGenericFactor_properties A C h0
  exact orderedProduct_star_regularity _ _ hn hn hp.1 hp.1 hp.2 hp.2 c v hv hne label hl ha

#print axioms constructed_product_regularity
#print axioms starEnvelope_bounds
#print axioms specialized_star_chart
#print axioms chartedGenericFactor_properties
end
end ADKZPricing
