import Representation


noncomputable section
open Set MeasureTheory
namespace Geneson

lemma square_compact (n : ℝ) : IsCompact (Square n) :=
  isCompact_Icc.prod isCompact_Icc

lemma square_measure_ne_top (n : ℝ) : volume (Square n) ≠ ⊤ :=
  (square_compact n).measure_lt_top.ne

lemma measure_ne_top_of_subset_square {n : ℝ} {S : Set Plane}
    (hS : S ⊆ Square n) : volume S ≠ ⊤ :=
  (measure_lt_top_of_subset hS (square_measure_ne_top n)).ne

lemma area_nonneg (S : Set Plane) : 0 ≤ Area S := ENNReal.toReal_nonneg

lemma area_mono {n : ℝ} {S T : Set Plane} (hST : S ⊆ T)
    (hT : T ⊆ Square n) : Area S ≤ Area T :=
  ENNReal.toReal_mono (measure_ne_top_of_subset_square hT) (measure_mono hST)

lemma opx_values_nonempty (n : ℝ) {R : Set Plane} (hR : R.Nonempty) :
    {a : ℝ | ∃ S : Set Plane,
      IsOpen S ∧ S ⊆ Square n ∧ ¬ Contains R S ∧ a = Area S}.Nonempty := by
  refine ⟨0, ∅, isOpen_empty, empty_subset _, not_contains_empty hR, ?_⟩
  simp [Area]

lemma opx_values_bddAbove (n : ℝ) (R : Set Plane) :
    BddAbove {a : ℝ | ∃ S : Set Plane,
      IsOpen S ∧ S ⊆ Square n ∧ ¬ Contains R S ∧ a = Area S} := by
  refine ⟨Area (Square n), ?_⟩
  rintro a ⟨S, _, hS, _, rfl⟩
  exact area_mono hS Subset.rfl

lemma area_le_opx {n : ℝ} {R S : Set Plane} (hSo : IsOpen S)
    (hS : S ⊆ Square n) (havoid : ¬ Contains R S) : Area S ≤ opx n R := by
  exact le_csSup (opx_values_bddAbove n R) ⟨S, hSo, hS, havoid, rfl⟩

lemma opx_nonneg (n : ℝ) {R : Set Plane} (hR : R.Nonempty) : 0 ≤ opx n R := by
  simpa [Area] using area_le_opx (n := n) isOpen_empty (empty_subset _)
    (not_contains_empty hR)

lemma opx_le_square_area (n : ℝ) {R : Set Plane} (hR : R.Nonempty) :
    opx n R ≤ Area (Square n) := by
  exact csSup_le (opx_values_nonempty n hR) (by
    rintro a ⟨S, _, hS, _, rfl⟩
    exact area_mono hS Subset.rfl)

lemma opx_le_of_open_bounds {n : ℝ} {R : Set Plane} (hR : R.Nonempty)
    {L : ℝ} (hbound : ∀ S : Set Plane, IsOpen S → S ⊆ Square n →
      ¬ Contains R S → Area S ≤ L) : opx n R ≤ L := by
  apply csSup_le (opx_values_nonempty n hR)
  rintro a ⟨S, hSo, hS, havoid, rfl⟩
  exact hbound S hSo hS havoid

lemma open_subset_interior_square {n : ℝ} {S : Set Plane}
    (hSo : IsOpen S) (hS : S ⊆ Square n) : S ⊆ Ioo 0 n ×ˢ Ioo 0 n := by
  have h := interior_mono hS
  simpa only [hSo.interior_eq, Square, interior_prod_eq, interior_Icc] using h

/-- Real area bounds on compact cores extend to measurable sets by inner regularity. -/
lemma area_le_of_compact_bounds {E : Set Plane} (hE : MeasurableSet E)
    {L : ℝ} (hL : 0 ≤ L)
    (hcore : ∀ C : Set Plane, C ⊆ E → IsCompact C → Area C ≤ L) :
    Area E ≤ L := by
  apply ENNReal.toReal_le_of_le_ofReal hL
  rw [hE.measure_eq_iSup_isCompact volume]
  refine iSup_le fun C => iSup_le fun hCE => iSup_le fun hC => ?_
  exact (ENNReal.le_ofReal_iff_toReal_le hC.measure_lt_top.ne hL).2
    (hcore C hCE hC)

/-- The square's boundary has zero two-dimensional Lebesgue measure. -/
lemma interior_square_ae_eq (n : ℝ) :
    (Ioo 0 n ×ˢ Ioo 0 n : Set Plane) =ᵐ[volume] Square n := by
  exact Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc

lemma area_inter_interior_square {n : ℝ} {E : Set Plane} (hE : E ⊆ Square n) :
    Area (E ∩ (Ioo 0 n ×ˢ Ioo 0 n)) = Area E := by
  apply congrArg ENNReal.toReal
  calc
    volume (E ∩ (Ioo 0 n ×ˢ Ioo 0 n)) = volume (E ∩ Square n) :=
      measure_congr (ae_eq_set_inter .rfl (interior_square_ae_eq n))
    _ = volume E := by rw [inter_eq_left.mpr hE]

/-- Explicit collar API used by the full arbitrary-pattern theorem. -/
def AvoidingCollars (n : ℝ) (R : Set Plane) : Prop :=
  ∀ C : Set Plane, IsCompact C → C ⊆ Ioo 0 n ×ˢ Ioo 0 n →
    ¬ Contains R C → ∃ O : Set Plane,
      IsOpen O ∧ C ⊆ O ∧ O ⊆ Square n ∧ ¬ Contains R O

lemma measurable_avoiding_area_le_opx {n : ℝ} {R E : Set Plane}
    (hR : R.Nonempty) (hE : MeasurableSet E) (hEsq : E ⊆ Square n)
    (havoid : ¬ Contains R E) (hcollar : AvoidingCollars n R) :
    Area E ≤ opx n R := by
  rw [← area_inter_interior_square hEsq]
  apply area_le_of_compact_bounds
    (hE.inter (isOpen_Ioo.prod isOpen_Ioo).measurableSet) (opx_nonneg n hR)
  intro C hCE hC
  obtain ⟨O, hOo, hCO, hOsq, hOavoid⟩ := hcollar C hC
    (hCE.trans inter_subset_right)
    (fun hcopy => havoid (contains_mono (hCE.trans inter_subset_left) hcopy))
  exact (area_mono hCO hOsq).trans (area_le_opx hOo hOsq hOavoid)

/-- Measurable partition assembly; compactness/gluing supplies the partition. -/
lemma area_le_opx_add_of_partition {n : ℝ} {P Q K A : Set Plane}
    (hP : P.Nonempty) (hQ : Q.Nonempty) (hK : MeasurableSet K)
    (hA : MeasurableSet A) (hAK : A ⊆ K) (hKsq : K ⊆ Square n)
    (hAavoid : ¬ Contains Q A) (hBavoid : ¬ Contains P (K \ A))
    (hPc : AvoidingCollars n P) (hQc : AvoidingCollars n Q) :
    Area K ≤ opx n P + opx n Q := by
  have hA_bound := measurable_avoiding_area_le_opx hQ hA (hAK.trans hKsq)
    hAavoid hQc
  have hB_bound := measurable_avoiding_area_le_opx hP (hK.diff hA)
    (sdiff_subset.trans hKsq) hBavoid hPc
  have hsum : Area (K \ A) + Area A = Area K := by
    unfold Area
    rw [← ENNReal.toReal_add (measure_ne_top_of_subset_square
      (sdiff_subset.trans hKsq)) (measure_ne_top_of_subset_square (hAK.trans hKsq))]
    exact congrArg ENNReal.toReal (by
      simpa only [inter_eq_right.mpr hAK] using
        (measure_sdiff_add_inter (μ := volume) K hA))
  linarith

end Geneson
