import PerturbedStar

namespace ADKZPricing
open Matrix Finset
noncomputable section

theorem specialized_star_weights {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) ℤ)
    (C : IntegralStarChart A) (c : Option (Fin n)) :
    ∃ θ : Fin n → ℚ, (∀ i, 0 < θ i) ∧
      (∀ j, (C.chart j : ℚ) = ∑ i, θ i * starSign c i *
        specializedMatrix A integerVandermonde
          (commonParameter (d + 1) (starEnvelope A integerVandermonde C)) i j) := by
  let D : Matrix (Fin n) (Fin (d + 1)) ℤ := integerVandermonde
  have hb := starEnvelope_bounds A D C
  obtain ⟨θ, hp, hr, _⟩ := strict_chart_certificate_persistence (by omega)
    (rowScaled A (starSign c)) (rowScaled D (starSign c)) C.basis C.basis_injective
    (C.weights c) C.chart _ hb.1
    (fun i j => by simpa only [rowScaled, starSign_abs_mul] using hb.2.1 i j)
    (fun i j => by simpa only [rowScaled, starSign_abs_mul] using hb.2.2.1 i j)
    (hb.2.2.2.1 c) (hb.2.2.2.2.1 c) (C.positive c) (C.representation c)
    (signed_rows_det A c C.basis C.basis_det)
  refine ⟨θ, hp, ?_⟩
  intro j
  rw [specialized_signed_rows] at hr
  simpa only [rowScaled, mul_assoc] using hr j

/-- Rebase the repaired positive representation onto coordinate zero.
    The weights change by the SAME positive h[0] in every star cell. -/
theorem rebased_positive_weights {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℚ) (h : Fin (d + 1) → ℚ)
    (hh : 0 < h 0) (s l : Fin n → ℚ) (hl : ∀ i, 0 < l i)
    (hr : ∀ j, h j = ∑ i, l i * s i * A i j) :
    (∀ i, 0 < l i / h 0) ∧
      (∀ j, (if j = 0 then 1 else 0 : ℚ) =
        ∑ i, (l i / h 0) * s i * chartRebased A h i j) := by
  refine ⟨fun i => div_pos (hl i) hh, ?_⟩
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [chartRebased, Fin.cons_zero, ↓reduceIte]
    have he : (∑ i, l i / h 0 * s i * A i 0) = (∑ i, l i * s i * A i 0) / h 0 := by
      rw [Finset.sum_div]
      apply sum_congr rfl
      intro i _
      ring
    rw [he, ← hr 0, div_self hh.ne']
  · simp only [Fin.succ_ne_zero, ↓reduceIte, chartRebased, Fin.cons_succ]
    have he : (∑ i, l i / h 0 * s i * (h 0 * A i k.succ - A i 0 * h k.succ)) =
        (∑ i, l i * s i * A i k.succ) - (h k.succ / h 0) * (∑ i, l i * s i * A i 0) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply sum_congr rfl
      intro i _
      field_simp
      ring
    rw [he, ← hr k.succ, ← hr 0]
    field_simp

theorem chartedGenericFactor_weights {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A)
    (h0 : 0 < C.chart 0) (c : Option (Fin n)) :
    ∃ θ : Fin n → ℚ, (∀ i, 0 < θ i) ∧
      (∀ j, (if j = 0 then 1 else 0 : ℚ) =
        ∑ i, θ i * starSign c i * chartedGenericFactor A C i j) := by
  obtain ⟨θ, hp, hr⟩ := specialized_star_weights A C c
  have hq : (0 : ℚ) < C.chart 0 := by exact_mod_cast h0
  exact ⟨fun i => θ i / C.chart 0,
    rebased_positive_weights _ (fun j => (C.chart j : ℚ)) hq (starSign c) θ hp hr⟩

/-- Positive chart representations for ALL product-star cells are obtained
    directly from the two corresponding factor representations. Both use
    the same coordinate zero; each contributes one half. No cell LP runs. -/
theorem product_star_weights {n m d e : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℚ) (B : Matrix (Fin m) (Fin (e + 1)) ℚ)
    (hA : ∀ c, ∃ l : Fin n → ℚ, (∀ i, 0 < l i) ∧
      ∀ j, (if j = 0 then 1 else 0 : ℚ) = ∑ i, l i * starSign c i * A i j)
    (hB : ∀ c, ∃ l : Fin m → ℚ, (∀ i, 0 < l i) ∧
      ∀ j, (if j = 0 then 1 else 0 : ℚ) = ∑ i, l i * starSign c i * B i j)
    (c : Option (Fin (n + m))) :
    ∃ l : Fin (n + m) → ℚ, (∀ i, 0 < l i) ∧
      ∀ j, (if j = 0 then 1 else 0 : ℚ) =
        ∑ i, l i * starSign c i * orderedProduct A B i j := by
  obtain ⟨l, hl, hr⟩ := hA (leftStar c)
  obtain ⟨k, hk, hs⟩ := hB (rightStar c)
  refine ⟨Fin.append (fun i => l i / 2) (fun i => k i / 2), ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using div_pos (hl j) (by norm_num : (0 : ℚ) < 2)
    · simpa only [Fin.append_right] using div_pos (hk j) (by norm_num : (0 : ℚ) < 2)
  · intro j
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, starSign_left, starSign_right]
    have hhalfL (a : Fin (d + 1)) :
        (∑ i, l i / 2 * starSign (leftStar c) i * A i a) =
          (if a = 0 then 1 else 0 : ℚ) / 2 := by
      rw [hr a, Finset.sum_div]
      apply sum_congr rfl
      intro i _
      ring
    have hhalfR (a : Fin (e + 1)) :
        (∑ i, k i / 2 * starSign (rightStar c) i * B i a) =
          (if a = 0 then 1 else 0 : ℚ) / 2 := by
      rw [hs a, Finset.sum_div]
      apply sum_congr rfl
      intro i _
      ring
    refine Fin.cases ?_ (fun a => ?_) j
    · simp only [orderedProduct, Fin.append_left, Fin.append_right, Fin.cons_zero,
        ↓reduceIte, hhalfL, hhalfR]
      norm_num
    · refine Fin.addCases (fun b => ?_) (fun b => ?_) a <;>
        simp only [orderedProduct, Fin.append_left, Fin.append_right, Fin.cons_succ,
          Fin.succ_ne_zero, ↓reduceIte, mul_zero, sum_const_zero, add_zero, zero_add,
          hhalfL, hhalfR, zero_div]

#print axioms chartedGenericFactor_weights
#print axioms product_star_weights
end
end ADKZPricing
