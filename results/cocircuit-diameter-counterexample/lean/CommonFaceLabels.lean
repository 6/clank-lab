import CellEdges

namespace ADKZPricing
open Matrix Finset
noncomputable section

/-- Two complete d-row labels with d-1 common rows differ by exactly
    one original row on each side. No facet is deleted or relabelled. -/
theorem complete_labels_exchange {n d : ℕ} (bas : Fin d → Fin n)
    (hb : Function.Injective bas) (W : Finset (Fin n)) (hw : W.card = d)
    (hc : ((univ.image bas) ∩ W).card + 1 = d) :
    ∃ drop : Fin d, ∃ newRow : Fin n,
      bas drop ∉ W ∧ newRow ∈ W ∧ newRow ∉ univ.image bas ∧
      (∀ j, bas j ∈ W ↔ j ≠ drop) := by
  classical
  let Z := univ.image bas
  have hz : Z.card = d := by simp [Z, Finset.card_image_of_injective _ hb]
  have hd : (Z \ W).card = 1 := by
    have he := card_sdiff_add_card_inter Z W
    change (Z ∩ W).card + 1 = d at hc
    omega
  obtain ⟨old, hold⟩ := card_eq_one.mp hd
  have hom : old ∈ Z \ W := by rw [hold]; exact mem_singleton_self _
  obtain ⟨drop, _, hdrop⟩ := mem_image.mp (mem_sdiff.mp hom).1
  have hn : (W \ Z).Nonempty := by
    apply card_pos.mp
    have he := card_sdiff_add_card_inter W Z
    rw [inter_comm W] at he
    change (Z ∩ W).card + 1 = d at hc
    omega
  obtain ⟨newRow, hnew⟩ := hn
  refine ⟨drop, newRow, ?_, (mem_sdiff.mp hnew).1, (mem_sdiff.mp hnew).2, ?_⟩
  · rw [hdrop]
    exact (mem_sdiff.mp hom).2
  · intro j
    constructor
    · intro hj he
      subst j
      rw [hdrop] at hj
      exact (mem_sdiff.mp hom).2 hj
    · intro hj
      by_contra hout
      have hm : bas j ∈ Z \ W := mem_sdiff.mpr ⟨mem_image.mpr ⟨j, mem_univ _, rfl⟩, hout⟩
      rw [hold, mem_singleton] at hm
      exact hj (hb (hm.trans hdrop.symm))

/-- The 39-common-label criterion is an actual geometric closed edge:
    every feasible point on the common original face lies on the endpoint
    segment, and every point of that segment lies on that face. This
    discharges the local gain/new-tight-row premises from complete labels. -/
theorem complete_labels_common_face {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) K) (b : Fin n → K)
    (p q : Fin d → K) (bas : Fin d → Fin n) (hb : Function.Injective bas)
    (W : Finset (Fin n)) (hw : W.card = d)
    (hc : ((univ.image bas) ∩ W).card + 1 = d)
    (hdet : (A.submatrix bas id).det ≠ 0)
    (hp : AffineFeasible A b p) (hq : AffineFeasible A b q)
    (hzp : ∀ i, A i ⬝ᵥ p = b i ↔ i ∈ univ.image bas)
    (hzq : ∀ i, A i ⬝ᵥ q = b i ↔ i ∈ W)
    (x : Fin d → K) :
    (AffineFeasible A b x ∧ ∀ i ∈ (univ.image bas) ∩ W, A i ⬝ᵥ x = b i) ↔
      ∃ t : K, 0 ≤ t ∧ t ≤ 1 ∧ x = affineSegment p q t := by
  obtain ⟨drop, newRow, hd, hnew, hnewp, hcommon⟩ :=
    complete_labels_exchange bas hb W hw hc
  have hpa (j : Fin d) : A (bas j) ⬝ᵥ p = b (bas j) :=
    (hzp (bas j)).mpr (mem_image.mpr ⟨j, mem_univ _, rfl⟩)
  have hqa (j : Fin d) (hj : j ≠ drop) : A (bas j) ⬝ᵥ q = b (bas j) :=
    (hzq (bas j)).mpr ((hcommon j).mpr hj)
  have hgain : 0 < A (bas drop) ⬝ᵥ q - b (bas drop) := by
    apply sub_pos.mpr
    apply lt_of_le_of_ne (hq (bas drop))
    intro he
    exact hd ((hzq (bas drop)).mp he.symm)
  have hstrict : b newRow < A newRow ⬝ᵥ p := by
    apply lt_of_le_of_ne (hp newRow)
    intro he
    exact hnewp ((hzp newRow).mp he.symm)
  have he := certified_common_face_segment A b p q bas drop hdet hp hq hpa hqa hgain
    newRow ((hzq newRow).mpr hnew) hstrict x
  apply Iff.trans ?_ he
  apply and_congr_right
  intro _
  constructor
  · intro hx j hj
    apply hx
    exact mem_inter.mpr ⟨mem_image.mpr ⟨j, mem_univ _, rfl⟩, (hcommon j).mpr hj⟩
  · intro hx i hi
    obtain ⟨j, _, rfl⟩ := mem_image.mp (mem_inter.mp hi).1
    exact hx j ((hcommon j).mp (mem_inter.mp hi).2)

#print axioms complete_labels_exchange
#print axioms complete_labels_common_face
end
end ADKZPricing
