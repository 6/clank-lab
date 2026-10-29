import SecondPerturbation
import ChartKernel

namespace ADKZPricing
open Matrix Finset
noncomputable section

theorem rational_minor_real {n m r : ℕ}
    (A : Matrix (Fin n) (Fin m) ℚ) (f : Fin r → Fin n) (g : Fin r → Fin m)
    (hd : (A.submatrix f g).det ≠ 0) :
    ((A.map (Rat.castHom ℝ)).submatrix f g).det ≠ 0 := by
  have he := Rat.cast_det (F := ℝ) (A.submatrix f g)
  change (((A.submatrix f g).det : ℚ) : ℝ) =
    ((A.map (Rat.castHom ℝ)).submatrix f g).det at he
  rw [← he]
  exact Rat.cast_ne_zero.mpr hd

/-- A rational positive chart representation is strict on EVERY real ray.
    Full rank is transported by the same checked minor, not inferred by
    inspecting only rational vertices. -/
theorem rational_chart_real {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℚ)
    (f : Fin (d + 1) → Fin n) (hf : (A.submatrix f id).det ≠ 0)
    (c : Option (Fin n)) (w : Fin n → ℚ) (hw : ∀ i, 0 < w i)
    (hr : ∀ j, (if j = 0 then 1 else 0 : ℚ) = ∑ i, w i * starSign c i * A i j)
    (v : Fin (d + 1) → ℝ)
    (hv : StarFeasible (A.map (Rat.castHom ℝ)) c v) (hn : v ≠ 0) : 0 < v 0 := by
  let R := A.map (Rat.castHom ℝ)
  let S := rowScaled R (starSign c)
  have hsign (i : Fin n) : (((starSign c i : ℚ) : ℝ)) = starSign c i := by
    unfold starSign
    split_ifs <;> norm_num
  have hrep (j : Fin (d + 1)) : (if j = 0 then 1 else 0 : ℝ) =
      ∑ i, (w i : ℝ) * S i j := by
    have he := congrArg (fun x : ℚ => (x : ℝ)) (hr j)
    push_cast at he
    change (if j = 0 then 1 else 0 : ℝ) =
      ∑ i, (w i : ℝ) * (starSign c i * (A i j : ℝ))
    by_cases hj : j = 0 <;>
      simp only [hj, ↓reduceIte, Rat.cast_one, Rat.cast_zero, hsign, mul_assoc] at he ⊢ <;>
      exact he
  have hp := positive_weighted_chart S (fun i => (w i : ℝ))
    (fun j => if j = 0 then 1 else 0) (fun i => by change (0 : ℝ) < (w i : ℝ); exact_mod_cast hw i)
    hrep v (fun i => by
      change 0 ≤ rowScaled R (starSign c) i ⬝ᵥ v
      rw [rowScaled_value]
      exact hv i) ?_
  · simpa only [Fin.sum_univ_succ, ↓reduceIte, one_mul, Fin.succ_ne_zero,
      zero_mul, sum_const_zero, add_zero] using hp
  · obtain ⟨i, hi⟩ := full_rank_detects_nonzero R f (rational_minor_real A f id hf) v hn
    refine ⟨i, ?_⟩
    change rowScaled R (starSign c) i ⬝ᵥ v ≠ 0
    rw [rowScaled_value]
    apply mul_ne_zero _ hi
    unfold starSign
    split_ifs <;> norm_num

theorem chartedGenericFactor_real_properties {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A)
    (h0 : 0 < C.chart 0) :
    (∀ f : Fin (d + 1) → Fin n, Function.Injective f →
      (((chartedGenericFactor A C).map (Rat.castHom ℝ)).submatrix f id).det ≠ 0) ∧
    (∀ c v, StarFeasible ((chartedGenericFactor A C).map (Rat.castHom ℝ)) c v →
      v ≠ 0 → 0 < v 0) := by
  have hp := chartedGenericFactor_properties A C h0
  constructor
  · intro f hf
    exact rational_minor_real _ f id (hp.1 f hf)
  · intro c v hv hn
    obtain ⟨f, _, hf⟩ := exists_full_row_basis _ (strict_chart_mulVec_injective _ (hp.2 none))
    obtain ⟨w, hw, hr⟩ := chartedGenericFactor_weights A C h0 c
    exact rational_chart_real _ f hf c w hw hr v hv hn

/-- Actual real product vertices have the same regularity as rational ones;
    the row map commutes with the ordered product and keeps all shared labels. -/
theorem firstProduct_real_regularity {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A)
    (h0 : 0 < C.chart 0) (hn : d < n)
    (c : Option (Fin (n + n))) (v : Fin (d + d + 1) → ℝ)
    (hv : StarFeasible ((firstProduct A C).map (Rat.castHom ℝ)) c v)
    (hne : v ≠ 0) (label : Fin (d + d) → Fin (n + n)) (hl : Function.Injective label)
    (ha : ∀ j, ((firstProduct A C).map (Rat.castHom ℝ)) (label j) ⬝ᵥ v = 0) :
    0 < v 0 ∧
      (((firstProduct A C).map (Rat.castHom ℝ)).submatrix label Fin.succ).det ≠ 0 ∧
      (∀ i, i ∉ Set.range label →
        0 < starSign c i * (((firstProduct A C).map (Rat.castHom ℝ)) i ⬝ᵥ v)) := by
  have hp := chartedGenericFactor_real_properties A C h0
  simp only [firstProduct, orderedProduct_map] at hv ha ⊢
  exact orderedProduct_star_regularity _ _ hn hn hp.1 hp.1 hp.2 hp.2 c v hv hne label hl ha

#print axioms rational_chart_real
#print axioms firstProduct_real_regularity
end
end ADKZPricing
