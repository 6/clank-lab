import RealActiveTransport
import AdjacencyConverse
import EndpointMatrixBridge

set_option maxRecDepth 4096

namespace ADKZPricing
open Matrix Finset
noncomputable section

/-- Cast the uniformity interface before specializing the dimension. -/
theorem rational_uniform_complete_labels {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℚ)
    (hu : UniformAt A)
    (v : Fin (d + 1) → ℝ) (hv : v ≠ 0)
    (label : Fin d → Fin n) (hl : Function.Injective label)
    (ha : ∀ j, (A.map (Rat.castHom ℝ)) (label j) ⬝ᵥ v = 0) :
    ∀ i, (A.map (Rat.castHom ℝ)) i ⬝ᵥ v = 0 ↔ i ∈ Set.range label := by
  apply uniform_complete_active_labels_lambda _ _ v hv label hl ha
  intro f hf
  change Matrix.det (fun i j => (A (f i) j : ℝ)) ≠ 0
  rw [← rational_minor_cast]
  exact Rat.cast_ne_zero.mpr (hu f hf)

theorem endpoint_uniform_at (A : Matrix (Fin 80) (Fin 41) ℚ) (hu : Uniform A) :
    UniformAt A := hu

/-- Original zero labels and a closed arrangement-cell sign determine
    the actual sign vector, including vertices on the shared facet. -/
def cellLabelSigns (c : Option (Fin 80)) (Z : Finset (Fin 80)) : SignVector :=
  fun i => if i ∈ Z then 0 else starSign c i

theorem cellLabelSigns_zero (c : Option (Fin 80)) (Z : Finset (Fin 80)) (i : Fin 80) :
    cellLabelSigns c Z i = 0 ↔ i ∈ Z := by
  simp only [cellLabelSigns, starSign]
  split_ifs <;> simp_all

theorem cellLabelSigns_zeros (c : Option (Fin 80)) (Z : Finset (Fin 80)) :
    signZeros (cellLabelSigns c Z) = Z := by
  ext i
  simp [signZeros, cellLabelSigns_zero]

theorem cellLabelSigns_nonzero (c : Option (Fin 80)) (Z : Finset (Fin 80))
    (hc : Z.card = 40) : cellLabelSigns c Z ≠ 0 := by
  intro hz
  have he : Z = univ := by
    ext i
    simp only [mem_univ, iff_true]
    exact (cellLabelSigns_zero c Z i).mp (congrFun hz i)
  rw [he] at hc
  norm_num at hc

theorem signed_star_realSign (c : Option (Fin 80)) (i : Fin 80) (x : ℝ)
    (hf : 0 ≤ starSign c i * x) (hx : x ≠ 0) : realSign x = starSign c i := by
  unfold starSign at hf ⊢
  by_cases h : c = some i
  · rw [if_pos h] at hf ⊢
    apply (realSign_negative_iff x).mpr
    norm_num at hf
    exact lt_of_le_of_ne hf hx
  · rw [if_neg h] at hf ⊢
    apply (realSign_positive_iff x).mpr
    simpa using lt_of_le_of_ne (by simpa using hf : 0 ≤ x) (Ne.symm hx)

/-- Actual real slacks, including every zero row, identify the labelled
    sign vector. This supplies the frozen Covector witness directly. -/
theorem feasible_complete_signs (A : Matrix (Fin 80) (Fin 41) ℚ)
    (c : Option (Fin 80)) (Z : Finset (Fin 80)) (v : Fin 41 → ℝ)
    (hf : StarFeasible (A.map (Rat.castHom ℝ)) c v)
    (hz : ∀ i, (A.map (Rat.castHom ℝ)) i ⬝ᵥ v = 0 ↔ i ∈ Z) :
    signsOf A v = cellLabelSigns c Z := by
  ext i
  change realSign ((A.map (Rat.castHom ℝ)) i ⬝ᵥ v) = cellLabelSigns c Z i
  by_cases hi : i ∈ Z
  · rw [(hz i).mpr hi]
    simp [cellLabelSigns, hi, realSign]
  · rw [cellLabelSigns, if_neg hi]
    exact signed_star_realSign c i _ (hf i) (fun h => hi ((hz i).mp h))

/-- Both directions use the actual frozen Covector/Cocircuit definitions.
    A nonzero real ray on forty original active rows is a cocircuit, and
    each such cocircuit supplies a real feasible ray on those same rows. -/
theorem uniform_active_cocircuit_iff (A : Matrix (Fin 80) (Fin 41) ℚ)
    (hu : Uniform A) (c : Option (Fin 80)) (label : Fin 40 → Fin 80)
    (hl : Function.Injective label) :
    ActiveRay (A.map (Rat.castHom ℝ)) c label ↔
      Cocircuit A (cellLabelSigns c (univ.image label)) := by
  classical
  have hc : (univ.image label).card = 40 := by simp [Finset.card_image_of_injective _ hl]
  have hnon := cellLabelSigns_nonzero c (univ.image label) hc
  constructor
  · rintro ⟨v, hv, hf, ha⟩
    have hz := rational_uniform_complete_labels A (endpoint_uniform_at A hu) v hv label hl ha
    have he := feasible_complete_signs A c (univ.image label) v hf (by simpa using hz)
    have hcov : Covector A (cellLabelSigns c (univ.image label)) := by
      refine ⟨v, ?_⟩
      intro i
      exact (congrFun he i).symm
    apply (uniform_covector_cocircuit_iff A hu _ hcov hnon).mpr
    rw [cellLabelSigns_zeros, hc]
  · intro h
    obtain ⟨v, hv⟩ := h.1
    have he : signsOf A v = cellLabelSigns c (univ.image label) :=
      funext (fun i => (hv i).symm)
    have hz (i : Fin 80) : (A.map (Rat.castHom ℝ)) i ⬝ᵥ v = 0 ↔ i ∈ univ.image label := by
      rw [← realSign_zero_iff]
      exact (Iff.of_eq (congrArg (fun x : ℤ => x = 0) (congrFun he i))).trans
        (cellLabelSigns_zero c _ i)
    refine ⟨v, ?_, ?_, ?_⟩
    · intro hv0
      apply hnon
      ext i
      rw [← he, hv0]
      simp [signsOf, rowValue, realSign]
    · intro i
      by_cases hi : i ∈ univ.image label
      · rw [(hz i).mpr hi, mul_zero]
      · have hs := congrFun he i
        change realSign ((A.map (Rat.castHom ℝ)) i ⬝ᵥ v) = _ at hs
        rw [cellLabelSigns, if_neg hi] at hs
        have hsigncast : ((starSign c i : ℤ) : ℝ) = starSign c i := by
          unfold starSign
          split_ifs <;> norm_num
        have hnonneg := realSign_signed_nonnegative ((A.map (Rat.castHom ℝ)) i ⬝ᵥ v)
        rw [hs, hsigncast] at hnonneg
        exact hnonneg
    · intro j
      apply (hz (label j)).mpr
      exact mem_image.mpr ⟨j, mem_univ _, rfl⟩

theorem cellLabelSigns_compose (c : Option (Fin 80)) (Z W : Finset (Fin 80)) :
    compose (cellLabelSigns c Z) (cellLabelSigns c W) = cellLabelSigns c (Z ∩ W) := by
  ext i
  have hs : (starSign c i : ℤ) ≠ 0 := by
    unfold starSign
    split_ifs <;> norm_num
  by_cases hz : i ∈ Z <;> by_cases hw : i ∈ W <;>
    simp [compose, cellLabelSigns, hz, hw, hs]

/-- This is adjacency in the faithful FULL cocircuit graph restricted
    to an actual closed arrangement cell. All shared-face vertices and
    edges remain present; no graph after deleting a facet is used. -/
theorem uniform_cell_adjacency_iff (A : Matrix (Fin 80) (Fin 41) ℚ)
    (hu : Uniform A) (c : Option (Fin 80)) (p q : Fin 40 → Fin 80)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hvp : ActiveRay (A.map (Rat.castHom ℝ)) c p)
    (hvq : ActiveRay (A.map (Rat.castHom ℝ)) c q) :
    Adjacent A (cellLabelSigns c (univ.image p)) (cellLabelSigns c (univ.image q)) ↔
      ((univ.image p) ∩ (univ.image q)).card = 39 := by
  have hx := (uniform_active_cocircuit_iff A hu c p hp).mp hvp
  have hy := (uniform_active_cocircuit_iff A hu c q hq).mp hvq
  rw [uniform_adjacency_iff A hu _ _ hx hy, cellLabelSigns_compose,
    cellLabelSigns_compose, inter_comm (univ.image q), cellLabelSigns_zeros]
  constructor
  · exact fun h => h.2.2
  · intro hc
    refine ⟨?_, rfl, hc⟩
    intro he
    have hz := congrArg signZeros he
    rw [cellLabelSigns_zeros, cellLabelSigns_zeros] at hz
    rw [← hz, inter_self, Finset.card_image_of_injective _ hp] at hc
    norm_num at hc

/-- A shared-facet vertex keeps its original zero labels in both cell
    descriptions. This is literal equality, not a quotient or deletion. -/
theorem cellLabelSigns_shared (e : Fin 80) (Z : Finset (Fin 80)) (he : e ∈ Z) :
    cellLabelSigns (some e) Z = cellLabelSigns none Z := by
  ext i
  by_cases hi : i ∈ Z
  · simp [cellLabelSigns, hi]
  · have hie : e ≠ i := by intro h; subst i; exact hi he
    simp [cellLabelSigns, starSign, hi, hie]

#print axioms uniform_active_cocircuit_iff
#print axioms uniform_cell_adjacency_iff
#print axioms cellLabelSigns_shared
end
end ADKZPricing
