import FirstSourcePreservation
import SourceChartDistance

namespace ADKZPricing
open Matrix Finset
noncomputable section

/-- Regularity here is a ray statement, not an abstract graph premise. -/
def RegularChart {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) K) (c : Option (Fin n)) : Prop :=
  ∀ v, v ≠ 0 → StarFeasible A c v → ∀ label : Fin d → Fin n,
    Function.Injective label → (∀ j, A (label j) ⬝ᵥ v = 0) →
    0 < v 0 ∧ ∀ i, A i ⬝ᵥ v = 0 ↔ i ∈ Set.range label

theorem strict_inactive_complete_labels {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) K)
    (c : Option (Fin n)) (v : Fin (d + 1) → K) (label : Fin d → Fin n)
    (ha : ∀ j, A (label j) ⬝ᵥ v = 0)
    (hs : ∀ i, i ∉ Set.range label → 0 < starSign c i * (A i ⬝ᵥ v)) :
    ∀ i, A i ⬝ᵥ v = 0 ↔ i ∈ Set.range label := by
  intro i
  constructor
  · intro hi
    by_contra hout
    have he := hs i hout
    rw [hi, mul_zero] at he
    exact lt_irrefl _ he
  · rintro ⟨j, rfl⟩
    exact ha j

theorem uniform_regular_chart {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) K)
    (hu : ∀ f : Fin (d + 1) → Fin n, Function.Injective f → (A.submatrix f id).det ≠ 0)
    (c : Option (Fin n)) (hs : ∀ v, StarFeasible A c v → v ≠ 0 → 0 < v 0) :
    RegularChart A c := by
  intro v hv hf label hl ha
  exact ⟨hs v hf hv, uniform_complete_active_labels A hu v hv label hl ha⟩

/-- Canonical normalization preserves every row sign and zero label in
    both directions. A normalized chart vertex is not merely an active
    list with feasibility left assumed. -/
theorem regular_chart_vertex_active_iff {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) K)
    (c : Option (Fin n)) (hr : RegularChart A c) (label : Fin d → Fin n)
    (hl : Function.Injective label) :
    ChartVertex A c (univ.image label) ↔ ActiveRay A c label := by
  constructor
  · rintro ⟨_, v, hv0, hf, hz⟩
    refine ⟨v, ?_, hf, ?_⟩
    · intro he
      have hz := congrFun he 0
      rw [hv0] at hz
      exact one_ne_zero hz
    · intro j
      exact (hz (label j)).mpr (mem_image.mpr ⟨j, mem_univ _, rfl⟩)
  · rintro ⟨v, hv, hf, ha⟩
    obtain ⟨hp, hz⟩ := hr v hv hf label hl ha
    let w := (v 0)⁻¹ • v
    have hw0 : w 0 = 1 := by simp [w, hp.ne']
    have hwf : StarFeasible A c w := by
      intro i
      change 0 ≤ starSign c i * (A i ⬝ᵥ ((v 0)⁻¹ • v))
      rw [dotProduct_smul]
      change 0 ≤ starSign c i * ((v 0)⁻¹ * (A i ⬝ᵥ v))
      rw [mul_left_comm]
      exact mul_nonneg (inv_pos.mpr hp).le (hf i)
    refine ⟨by simp [Finset.card_image_of_injective _ hl], w, hw0, hwf, ?_⟩
    intro i
    change A i ⬝ᵥ ((v 0)⁻¹ • v) = 0 ↔ _
    rw [dotProduct_smul]
    change (v 0)⁻¹ * (A i ⬝ᵥ v) = 0 ↔ _
    rw [mul_eq_zero_iff_left (inv_ne_zero hp.ne')]
    simpa using hz i

/-- Original-label ray equivalence plus established regularity gives
    complete chart-vertex equivalence, for every finite label set. -/
theorem active_equivalence_chart_vertices {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {n d : ℕ} (A B : Matrix (Fin n) (Fin (d + 1)) K)
    (c : Option (Fin n)) (hA : RegularChart A c) (hB : RegularChart B c)
    (he : ∀ label : Fin d → Fin n, Function.Injective label →
      (ActiveRay A c label ↔ ActiveRay B c label)) (Z : Finset (Fin n)) :
    ChartVertex A c Z ↔ ChartVertex B c Z := by
  classical
  by_cases hc : Z.card = d
  · let e := (Z.equivFinOfCardEq hc).symm
    let label : Fin d → Fin n := fun j => (e j).val
    have hl : Function.Injective label := by
      intro i j hij
      exact e.injective (Subtype.ext hij)
    have hZ : univ.image label = Z := by
      ext i
      constructor
      · rintro hi
        obtain ⟨j, _, rfl⟩ := mem_image.mp hi
        exact (e j).property
      · intro hi
        obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
        exact mem_image.mpr ⟨j, mem_univ _, congrArg Subtype.val hj⟩
    rw [← hZ, regular_chart_vertex_active_iff A c hA label hl,
      regular_chart_vertex_active_iff B c hB label hl]
    exact he label hl
  · constructor <;> intro h <;> exact (hc h.1).elim

theorem product_real_regular_chart {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A)
    (h0 : 0 < C.chart 0) (hn : d < n) (c : Option (Fin (n + n))) :
    RegularChart ((firstProduct A C).map (Rat.castHom ℝ)) c := by
  intro v hv hf label hl ha
  have hr := firstProduct_real_regularity A C h0 hn c v hf hv label hl ha
  exact ⟨hr.1, strict_inactive_complete_labels _ c v label ha hr.2.2⟩

theorem second_real_chart_vertices {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A)
    (h0 : 0 < C.chart 0) (hn : d < n) (c : Option (Fin (n + n)))
    (Z : Finset (Fin (n + n))) :
    ChartVertex ((secondPerturbedMatrix A C h0).map (Rat.castHom ℝ)) c Z ↔
      ChartVertex ((firstProduct A C).map (Rat.castHom ℝ)) c Z := by
  have hp := chartedGenericFactor_real_properties _ _ (secondIntegralChart_pivot A C h0)
  exact active_equivalence_chart_vertices _ _ c (uniform_regular_chart _ hp.1 c (hp.2 c))
    (product_real_regular_chart A C h0 hn c) (second_product_real_label_iff A C h0 hn c) Z

theorem first_source_real_chart_vertices {n d : ℕ} {V : Type*} [Fintype V] [Nonempty V]
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A) (h0 : 0 < C.chart 0)
    (S : SourceVertexCertificate (sourceSpatial (A.map (Int.castRingHom ℚ)))
      (sourceBound (A.map (Int.castRingHom ℚ))) V)
    (i₀ : Fin n) (ha : ∀ i, 0 < A i 0) (hn : d < n) (Z : Finset (Fin n)) :
    ChartVertex ((chartedGenericFactor A C).map (Rat.castHom ℝ)) none Z ↔
      ChartVertex ((A.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) none Z := by
  have hp := chartedGenericFactor_real_properties A C h0
  have hr : RegularChart ((A.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) none := by
    intro v hv hf label hl hx
    have hs := source_homogeneous_regularity _ (realSourceCertificate _ S) i₀
      (fun i => by change (0 : ℝ) < ((A i 0 : ℚ) : ℝ); exact_mod_cast ha i) v hv hf label hl hx
    refine ⟨hs.1, strict_inactive_complete_labels _ none v label hx ?_⟩
    intro i hi
    simpa [starSign] using hs.2.2 i hi
  exact active_equivalence_chart_vertices _ _ none (uniform_regular_chart _ hp.1 none (hp.2 none))
    hr (first_source_real_label_iff A C h0 S i₀ ha hn) Z

#print axioms regular_chart_vertex_active_iff
#print axioms second_real_chart_vertices
#print axioms first_source_real_chart_vertices
end
end ADKZPricing
