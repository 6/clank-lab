import RealChartTransport

namespace ADKZPricing
open Matrix Finset
noncomputable section

theorem rational_minor_of_real {n m r : ℕ}
    (A : Matrix (Fin n) (Fin m) ℚ) (f : Fin r → Fin n) (g : Fin r → Fin m)
    (hd : ((A.map (Rat.castHom ℝ)).submatrix f g).det ≠ 0) :
    (A.submatrix f g).det ≠ 0 := by
  intro hz
  have he := Rat.cast_det (F := ℝ) (A.submatrix f g)
  change (((A.submatrix f g).det : ℚ) : ℝ) =
    ((A.map (Rat.castHom ℝ)).submatrix f g).det at he
  rw [hz] at he
  exact hd (by simpa using he.symm)

/-- A real ray on an actual rational active basis is a POSITIVE multiple
    of its canonical rational kernel. Consequently all original signs,
    zero labels and shared-cell memberships are covered, not only a list
    of rational witnesses. -/
theorem real_ray_canonical_kernel {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℚ) (label : Fin d → Fin n)
    (hd : (A.submatrix label Fin.succ).det ≠ 0)
    (v : Fin (d + 1) → ℝ) (h0 : 0 < v 0)
    (ha : ∀ j, (A.map (Rat.castHom ℝ)) (label j) ⬝ᵥ v = 0) :
    v = (v 0) • (fun j => ((affineKernel (A.submatrix label id) j : ℚ) : ℝ)) := by
  let K := A.submatrix label id
  let w : Fin (d + 1) → ℝ := (v 0)⁻¹ • v
  have hw0 : w 0 = 1 := by simp [w, h0.ne']
  have hw : (K.map (Rat.castHom ℝ)) *ᵥ w = 0 := by
    ext j
    change (A.map (Rat.castHom ℝ)) (label j) ⬝ᵥ ((v 0)⁻¹ • v) = 0
    rw [dotProduct_smul, ha j, smul_zero]
  have he := real_chart_kernel_rational K hd w hw0 hw
  have hv : (v 0) • w = v := by
    simp [w, smul_smul, h0.ne']
  exact hv.symm.trans (congrArg (fun z => (v 0) • z) he)

/-- Signed feasibility and every original zero label transfer through the
    positive ray equality above in both directions. -/
theorem canonical_kernel_labels {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℚ) (label : Fin d → Fin n)
    (hd : (A.submatrix label Fin.succ).det ≠ 0)
    (v : Fin (d + 1) → ℝ) (h0 : 0 < v 0)
    (ha : ∀ j, (A.map (Rat.castHom ℝ)) (label j) ⬝ᵥ v = 0) :
    let q := affineKernel (A.submatrix label id)
    (∀ c, StarFeasible (A.map (Rat.castHom ℝ)) c v ↔ StarFeasible A c q) ∧
    (∀ i, (A.map (Rat.castHom ℝ)) i ⬝ᵥ v = 0 ↔ A i ⬝ᵥ q = 0) := by
  let q := affineKernel (A.submatrix label id)
  have hv := real_ray_canonical_kernel A label hd v h0 ha
  have hcast (i : Fin n) : (A.map (Rat.castHom ℝ)) i ⬝ᵥ (fun j => ((q j : ℚ) : ℝ)) =
      ((A i ⬝ᵥ q : ℚ) : ℝ) := by
    simp [dotProduct, q, Matrix.map_apply]
  have hrow (i : Fin n) : (A.map (Rat.castHom ℝ)) i ⬝ᵥ v =
      v 0 * ((A i ⬝ᵥ q : ℚ) : ℝ) := by
    conv_lhs => rw [hv]
    rw [dotProduct_smul, hcast]
    rfl
  constructor
  · intro c
    apply forall_congr'
    intro i
    have hs : (((starSign c i : ℚ) : ℝ)) = starSign c i := by
      unfold starSign
      split_ifs <;> norm_num
    change (0 ≤ starSign c i * ((A.map (Rat.castHom ℝ)) i ⬝ᵥ v)) ↔
      0 ≤ (starSign c i : ℚ) * (A i ⬝ᵥ q)
    rw [hrow, mul_left_comm, mul_nonneg_iff_of_pos_left h0, ← hs]
    exact_mod_cast (Iff.rfl :
      (0 : ℚ) ≤ starSign c i * (A i ⬝ᵥ q) ↔ 0 ≤ starSign c i * (A i ⬝ᵥ q))
  · intro i
    rw [hrow, mul_eq_zero_iff_left h0.ne']
    exact Rat.cast_eq_zero

/-- For the concrete ordered product construction, real regularity
    discharges the kernel premise for every active ordered label in all
    product-star cells. Shared labels use the SAME canonical kernel. -/
theorem firstProduct_real_kernel_labels {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A)
    (h0 : 0 < C.chart 0) (hn : d < n)
    (c : Option (Fin (n + n))) (v : Fin (d + d + 1) → ℝ)
    (hv : StarFeasible ((firstProduct A C).map (Rat.castHom ℝ)) c v)
    (hne : v ≠ 0) (label : Fin (d + d) → Fin (n + n)) (hl : Function.Injective label)
    (ha : ∀ j, ((firstProduct A C).map (Rat.castHom ℝ)) (label j) ⬝ᵥ v = 0) :
    let P := firstProduct A C
    let q := affineKernel (P.submatrix label id)
    v = (v 0) • (fun j => ((q j : ℚ) : ℝ)) ∧
    (∀ c', StarFeasible (P.map (Rat.castHom ℝ)) c' v ↔ StarFeasible P c' q) ∧
    (∀ i, (P.map (Rat.castHom ℝ)) i ⬝ᵥ v = 0 ↔ P i ⬝ᵥ q = 0) := by
  have hr := firstProduct_real_regularity A C h0 hn c v hv hne label hl ha
  have hd := rational_minor_of_real (firstProduct A C) label Fin.succ hr.2.1
  exact ⟨real_ray_canonical_kernel _ label hd v hr.1 ha,
    canonical_kernel_labels _ label hd v hr.1 ha⟩

#print axioms real_ray_canonical_kernel
#print axioms firstProduct_real_kernel_labels
end
end ADKZPricing
