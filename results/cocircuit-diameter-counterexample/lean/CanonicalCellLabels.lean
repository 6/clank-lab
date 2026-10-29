import ChartVertexTransport
import FactorTransitions
import SignComposition

namespace ADKZPricing
open Matrix Finset
noncomputable section

/-- Fold the dimension-polymorphic minor predicate before concrete
    dimension instantiation; this is exactly global row uniformity. -/
def RowUniform {K : Type*} [Field K] {n r : ℕ} (A : Matrix (Fin n) (Fin r) K) : Prop :=
  ∀ f : Fin r → Fin n, Function.Injective f → (A.submatrix f id).det ≠ 0

def labelOrder {n d : ℕ} (Z : Finset (Fin n)) (h : Z.card = d) : Fin d → Fin n :=
  fun j => ((Z.equivFinOfCardEq h).symm j).val

theorem labelOrder_injective {n d : ℕ} (Z : Finset (Fin n)) (h : Z.card = d) :
    Function.Injective (labelOrder Z h) := by
  intro i j hij
  exact (Z.equivFinOfCardEq h).symm.injective (Subtype.ext hij)

theorem labelOrder_mem {n d : ℕ} (Z : Finset (Fin n)) (h : Z.card = d) (j : Fin d) :
    labelOrder Z h j ∈ Z := ((Z.equivFinOfCardEq h).symm j).property

theorem labelOrder_image {n d : ℕ} (Z : Finset (Fin n)) (h : Z.card = d) :
    univ.image (labelOrder Z h) = Z := by
  ext i
  constructor
  · rintro hi
    obtain ⟨j, _, rfl⟩ := mem_image.mp hi
    exact labelOrder_mem Z h j
  · intro hi
    obtain ⟨j, hj⟩ := (Z.equivFinOfCardEq h).symm.surjective ⟨i, hi⟩
    exact mem_image.mpr ⟨j, mem_univ _, congrArg Subtype.val hj⟩

/-- A SINGLE canonical normalized kernel for an original label set.
    It is independent of the cell, so shared facets cannot acquire
    inconsistent vertex identifications when cell paths are joined. -/
def canonicalVertex {K : Type*} [Field K] {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) K) (Z : Finset (Fin n)) : Fin (d + 1) → K :=
  if h : Z.card = d then affineKernel (A.submatrix (labelOrder Z h) id) else 0

theorem canonical_vertex_of_rep {K : Type*} [Field K] {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) K) (hn : d < n)
    (hu : RowUniform A)
    (Z : Finset (Fin n)) (hc : Z.card = d) (v : Fin (d + 1) → K) (hv0 : v 0 = 1)
    (hz : ∀ i, A i ⬝ᵥ v = 0 ↔ i ∈ Z) : v = canonicalVertex A Z := by
  have ha (j : Fin d) : A (labelOrder Z hc j) ⬝ᵥ v = 0 :=
    (hz _).mpr (labelOrder_mem Z hc j)
  have hd := uniform_charted_spatial_basis A hn hu (labelOrder Z hc)
    (labelOrder_injective Z hc) v hv0 ha
  have hv : (A.submatrix (labelOrder Z hc) id) *ᵥ v = 0 := by ext j; exact ha j
  unfold canonicalVertex
  rw [dif_pos hc]
  exact affineKernel_unique _ hd v _ hv0 (by simp [affineKernel]) hv (affineKernel_equation _ hd)

theorem canonical_chart_vertex {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) K) (hn : d < n)
    (hu : RowUniform A)
    (c : Option (Fin n)) (Z : Finset (Fin n)) (hv : ChartVertex A c Z) :
    canonicalVertex A Z 0 = 1 ∧ StarFeasible A c (canonicalVertex A Z) ∧
      ∀ i, A i ⬝ᵥ canonicalVertex A Z = 0 ↔ i ∈ Z := by
  obtain ⟨hc, v, hv0, hf, hz⟩ := hv
  have he := canonical_vertex_of_rep A hn hu Z hc v hv0 hz
  rw [he] at hv0 hf hz
  exact ⟨hv0, hf, hz⟩

def canonicalSigns {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) ℝ)
    (Z : Finset (Fin n)) : Fin n → ℤ := fun i => realSign (A i ⬝ᵥ canonicalVertex A Z)

theorem realSign_cases (x : ℝ) : realSign x = -1 ∨ realSign x = 0 ∨ realSign x = 1 := by
  unfold realSign
  split_ifs <;> simp

theorem realSign_nonnegative_iff (x : ℝ) : 0 ≤ realSign x ↔ 0 ≤ x := by
  unfold realSign
  split_ifs <;> simp_all

theorem star_realSign_nonnegative {n : ℕ} (c : Option (Fin n)) (i : Fin n) (x : ℝ)
    (hx : 0 ≤ starSign c i * x) : 0 ≤ (starSign c i : ℤ) * realSign x := by
  unfold starSign at hx ⊢
  by_cases h : c = some i
  · rw [if_pos h] at hx ⊢
    have hn : x ≤ 0 := by linarith
    by_cases hx0 : x = 0
    · simp [hx0, realSign]
    · have hxneg : x < 0 := lt_of_le_of_ne hn hx0
      simp [realSign, hxneg]
  · rw [if_neg h] at hx ⊢
    simp only [one_mul] at hx ⊢
    exact (realSign_nonnegative_iff x).mpr hx

/-- Both closed cells read the SAME kernel and the SAME original signs. -/
theorem canonical_signs_cell {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) ℝ) (hn : d < n)
    (hu : RowUniform A)
    (c : Option (Fin n)) (Z : Finset (Fin n)) (hv : ChartVertex A c Z) :
    (∀ i, 0 ≤ (starSign c i : ℤ) * canonicalSigns A Z i) ∧
    (∀ i, canonicalSigns A Z i = 0 ↔ i ∈ Z) := by
  have hc := canonical_chart_vertex A hn hu c Z hv
  constructor
  · intro i
    exact star_realSign_nonnegative c i _ (hc.2.1 i)
  · intro i
    exact (realSign_zero_iff _).trans (hc.2.2 i)

/-- If all canonical signs along a union path are nonnegative, its
    vertices really belong to the central closed cell, including facets. -/
theorem canonical_nonnegative_central {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℝ) (hn : d < n)
    (hu : RowUniform A)
    (c : Option (Fin n)) (Z : Finset (Fin n)) (hv : ChartVertex A c Z)
    (hs : ∀ i, 0 ≤ canonicalSigns A Z i) : ChartVertex A none Z := by
  have hc := canonical_chart_vertex A hn hu c Z hv
  refine ⟨hv.1, canonicalVertex A Z, hc.1, ?_, hc.2.2⟩
  intro i
  change 0 ≤ starSign none i * (A i ⬝ᵥ canonicalVertex A Z)
  simpa [starSign] using (realSign_nonnegative_iff _).mp (hs i)

/-- An actual same-cell shared ridge spends two transitions over ALL
    original coordinates; the shared facet is not removed from the count. -/
theorem canonical_edge_variation {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℝ) (hn : d < n)
    (hu : RowUniform A)
    (c : Option (Fin n)) (Z W : Finset (Fin n)) (he : (chartCell A c).edge Z W) :
    ∑ i, |canonicalSigns A W i - canonicalSigns A Z i| = (2 : ℤ) := by
  have hz := canonical_signs_cell A hn hu c Z he.1
  have hw := canonical_signs_cell A hn hu c W he.2.1
  have hzerosZ : univ.filter (fun i => canonicalSigns A Z i = 0) = Z := by ext i; simp [hz.2]
  have hzerosW : univ.filter (fun i => canonicalSigns A W i = 0) = W := by ext i; simp [hw.2]
  have hzeros : univ.filter (fun i => canonicalSigns A Z i = 0 ∧ canonicalSigns A W i = 0) = Z ∩ W := by
    ext i; simp [hz.2, hw.2]
  apply shared_ridge_total_variation (d := d) (canonicalSigns A Z) (canonicalSigns A W)
    (fun i => realSign_cases _) (fun i => realSign_cases _)
  · intro i
    have h1 := hz.1 i
    have h2 := hw.1 i
    have hs : (starSign c i : ℤ) = -1 ∨ (starSign c i : ℤ) = 1 := by
      unfold starSign
      split_ifs <;> simp
    rcases realSign_cases (A i ⬝ᵥ canonicalVertex A Z) with hZ | hZ | hZ <;>
      rcases realSign_cases (A i ⬝ᵥ canonicalVertex A W) with hW | hW | hW <;>
      rcases hs with hs | hs <;>
      norm_num [canonicalSigns, hZ, hW, hs] at h1 h2 ⊢
  · simpa only [hzerosZ] using he.1.1
  · simpa only [hzerosW] using he.2.1.1
  · simpa only [hzeros] using he.2.2

#print axioms canonical_chart_vertex
#print axioms canonical_signs_cell
#print axioms canonical_edge_variation
end
end ADKZPricing
