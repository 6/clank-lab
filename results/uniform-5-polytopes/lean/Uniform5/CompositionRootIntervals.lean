import Uniform5.CompositionRadiusClasses
import Uniform5.CompositionRadiusTransport

/-! Exact conversion from reciprocal-radius root intervals to radius classes. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- Inverting a strictly positive closed root interval reverses its endpoints. -/
noncomputable def reciprocalRadiusInterval (I : ClosedRadiusInterval) (hI : 0 < I.lo) :
    ClosedRadiusInterval where
  lo := 1 / I.hi
  hi := 1 / I.lo
  ordered := one_div_le_one_div_of_le hI I.ordered

theorem reciprocalRadiusInterval_positive (I : ClosedRadiusInterval) (hI : 0 < I.lo) :
    0 < (reciprocalRadiusInterval I hI).lo :=
  one_div_pos.mpr (hI.trans_le I.ordered)

/-- No midpoint or approximate reciprocal enters interval membership. -/
theorem mem_reciprocalRadiusInterval_iff (I : ClosedRadiusInterval) (hI : 0 < I.lo)
    {R : ℝ} (hR : 0 < R) :
    R ∈ (reciprocalRadiusInterval I hI).carrier ↔ 1 / R ∈ I.carrier := by
  change (1 / I.hi ≤ R ∧ R ≤ 1 / I.lo) ↔ (I.lo ≤ 1 / R ∧ 1 / R ≤ I.hi)
  have hh := hI.trans_le I.ordered
  constructor
  · rintro ⟨hl, hu⟩
    constructor
    · have h := one_div_le_one_div_of_le hR hu
      simpa only [one_div_one_div] using h
    · have h := one_div_le_one_div_of_le (one_div_pos.mpr hh) hl
      simpa only [one_div_one_div] using h
  · rintro ⟨hl, hu⟩
    constructor
    · have h := one_div_le_one_div_of_le (one_div_pos.mpr hR) hu
      simpa only [one_div_one_div] using h
    · have h := one_div_le_one_div_of_le hI hl
      simpa only [one_div_one_div] using h

/-- Strict positivity of the actual root excludes a point interval at zero. -/
theorem positive_reciprocal_not_zero_root {R : ℝ} (hR : 0 < R)
    (I : ClosedRadiusInterval) (hzero : I.hi = 0) : 1 / R ∉ I.carrier := by
  intro h
  have hz := h.2
  rw [hzero] at hz
  exact (not_le_of_gt (one_div_pos.mpr hR)) hz

/-- A degenerate interval is discarded only when its zeros are certified
at the excluded endpoint; a tag on another root of the cycle is insufficient. -/
theorem root_outside_degenerate_interval {g : ℝ → ℝ} {s endpoint : ℝ}
    (I : ClosedRadiusInterval)
    (hdegenerate : ∀ t ∈ I.carrier, g t = 0 → t = endpoint)
    (hroot : g s = 0) (hstrict : s < endpoint) : s ∉ I.carrier := by
  intro hs
  exact (ne_of_lt hstrict) (hdegenerate s hs hroot)

/-- Exact zero coverage survives filtering intervals whose only possible
zeros are at a geometrically excluded endpoint. Whole cycles are not dropped. -/
theorem root_coverage_after_endpoint_filter {ι : Type*} [Fintype ι]
    (I : ι → ClosedRadiusInterval) (degenerate : ι → Prop)
    (g : ℝ → ℝ) (endpoint s : ℝ)
    (hcoverage : ∃ i, s ∈ (I i).carrier)
    (hdegenerate : ∀ i, degenerate i → ∀ t ∈ (I i).carrier, g t = 0 → t = endpoint)
    (hroot : g s = 0) (hstrict : s < endpoint) :
    ∃ i, ¬ degenerate i ∧ s ∈ (I i).carrier := by
  obtain ⟨i, hi⟩ := hcoverage
  refine ⟨i, ?_, hi⟩
  intro hd
  exact root_outside_degenerate_interval (I i) (hdegenerate i hd) hroot hstrict hi

/-- Domain-guarded form for the paper's partial geometric closure
function, avoiding claims about the total real expression outside its domain. -/
theorem root_coverage_after_endpoint_filter_on {ι : Type*}
    (I : ι → ClosedRadiusInterval) (degenerate : ι → Prop) (domain : ℝ → Prop)
    (g : ℝ → ℝ) (endpoint s : ℝ)
    (hcoverage : ∃ i, s ∈ (I i).carrier)
    (hdegenerate : ∀ i, degenerate i → ∀ t ∈ (I i).carrier,
      domain t → g t = 0 → t = endpoint)
    (hdomain : domain s) (hroot : g s = 0) (hstrict : s < endpoint) :
    ∃ i, ¬ degenerate i ∧ s ∈ (I i).carrier := by
  obtain ⟨i, hi⟩ := hcoverage
  refine ⟨i, ?_, hi⟩
  intro hd
  exact (ne_of_lt hstrict) (hdegenerate i hd s hi hdomain hroot)

/-- Positive interval witnesses for a common radius necessarily belong to
one actual overlap component after exact reciprocal conversion. -/
theorem reciprocal_root_witnesses_same_class {ι : Type*}
    (I : ι → ClosedRadiusInterval) (hI : ∀ i, 0 < (I i).lo)
    {i j : ι} {R : ℝ} (hR : 0 < R)
    (hi : 1 / R ∈ (I i).carrier) (hj : 1 / R ∈ (I j).carrier) :
    (radiusOverlapGraph (fun i => reciprocalRadiusInterval (I i) (hI i))).connectedComponentMk i =
      (radiusOverlapGraph (fun i => reciprocalRadiusInterval (I i) (hI i))).connectedComponentMk j := by
  apply radius_class_eq_of_common_point _
    ((mem_reciprocalRadiusInterval_iff (I i) (hI i) hR).mpr hi)
    ((mem_reciprocalRadiusInterval_iff (I j) (hI j) hR).mpr hj)

end Uniform5.Composition
