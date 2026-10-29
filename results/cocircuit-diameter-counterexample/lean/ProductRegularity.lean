import ProductCells
import OrderedSource

namespace ADKZPricing
open Matrix Finset
noncomputable section
variable {𝕜 : Type*} [Field 𝕜] [DecidableEq 𝕜]

def homogeneousZeros {n r : ℕ} (A : Matrix (Fin n) (Fin r) 𝕜)
    (v : Fin r → 𝕜) : Finset (Fin n) := univ.filter (fun i => A i ⬝ᵥ v = 0)

theorem orderedProduct_zero_count {n m d e : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) 𝕜)
    (B : Matrix (Fin m) (Fin (e + 1)) 𝕜) (v : Fin (d + e + 1) → 𝕜) :
    (homogeneousZeros (orderedProduct A B) v).card =
      (homogeneousZeros A (productLeft v)).card +
      (homogeneousZeros B (productRight v)).card := by
  simp only [homogeneousZeros, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fin.sum_univ_add, orderedProduct_left_value, orderedProduct_right_value]

/-- The complete active set, together with factor uniformity and a nonzero
    chart coordinate, kills every direction in the chart hyperplane. -/
theorem uniform_active_chart_kernel {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) 𝕜) (hn : d < n)
    (hu : ∀ f : Fin (d + 1) → Fin n, Function.Injective f → (A.submatrix f id).det ≠ 0)
    (v : Fin (d + 1) → 𝕜) (hv : v 0 ≠ 0)
    (hc : (homogeneousZeros A v).card = d)
    (w : Fin (d + 1) → 𝕜) (hw : w 0 = 0)
    (hz : ∀ i, A i ⬝ᵥ v = 0 → A i ⬝ᵥ w = 0) : w = 0 := by
  let E := ((homogeneousZeros A v).equivFinOfCardEq hc).symm
  let bas : Fin d → Fin n := fun j => (E j).val
  have hb : Function.Injective bas := by
    intro i j hij
    exact E.injective (Subtype.ext hij)
  have ha : ∀ j, A (bas j) ⬝ᵥ v = 0 := fun j =>
    (mem_filter.mp (E j).property).2
  let u := fun j => v j / v 0
  have hu0 : u 0 = 1 := div_self hv
  have hau : ∀ j, A (bas j) ⬝ᵥ u = 0 := by
    intro j
    simp only [u, dotProduct, ← mul_div_assoc, ← Finset.sum_div]
    rw [show ∑ k, A (bas j) k * v k = 0 from ha j, zero_div]
  have hdet := uniform_charted_spatial_basis A hn hu bas hb u hu0 hau
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  have htail : (fun j : Fin d => w j.succ) = 0 := by
    apply hinj
    ext j
    have h := hz (bas j) (ha j)
    simp only [dotProduct, Fin.sum_univ_succ, hw, mul_zero, zero_add] at h
    simpa [Matrix.mulVec, dotProduct, Matrix.submatrix] using h
  ext i
  refine Fin.cases hw (fun j => congrFun htail j) i

/-- Product regularity is derived for ANY ordered active label in ANY
    product-star cell. Its premises concern the two factors only; it does
    not assume regularity of any of the 81 product cells. -/
theorem orderedProduct_star_regularity [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {n m d e : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) 𝕜)
    (B : Matrix (Fin m) (Fin (e + 1)) 𝕜) (hn : d < n) (hm : e < m)
    (huA : ∀ f : Fin (d + 1) → Fin n, Function.Injective f → (A.submatrix f id).det ≠ 0)
    (huB : ∀ f : Fin (e + 1) → Fin m, Function.Injective f → (B.submatrix f id).det ≠ 0)
    (hsA : ∀ c v, StarFeasible A c v → v ≠ 0 → 0 < v 0)
    (hsB : ∀ c v, StarFeasible B c v → v ≠ 0 → 0 < v 0)
    (c : Option (Fin (n + m))) (v : Fin (d + e + 1) → 𝕜)
    (hv : StarFeasible (orderedProduct A B) c v) (hne : v ≠ 0)
    (label : Fin (d + e) → Fin (n + m)) (hl : Function.Injective label)
    (ha : ∀ j, orderedProduct A B (label j) ⬝ᵥ v = 0) :
    0 < v 0 ∧ ((orderedProduct A B).submatrix label Fin.succ).det ≠ 0 ∧
      (∀ i, i ∉ Set.range label →
        0 < starSign c i * (orderedProduct A B i ⬝ᵥ v)) := by
  have ht := orderedProduct_star_strict_chart A B hsA hsB c v hv hne
  have hbA : (homogeneousZeros A (productLeft v)).card ≤ d := by
    have h := uniform_zero_count A huA (productLeft v) ht.2.1
    exact Nat.le_of_lt_succ h
  have hbB : (homogeneousZeros B (productRight v)).card ≤ e := by
    have h := uniform_zero_count B huB (productRight v) ht.2.2
    exact Nat.le_of_lt_succ h
  let J := univ.image label
  have hj : J.card = d + e := by simp [J, Finset.card_image_of_injective _ hl]
  have hsub : J ⊆ homogeneousZeros (orderedProduct A B) v := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := mem_image.mp hi
    exact mem_filter.mpr ⟨mem_univ _, ha j⟩
  have hmany : d + e ≤ (homogeneousZeros (orderedProduct A B) v).card := by
    simpa only [hj] using card_le_card hsub
  have hsum := orderedProduct_zero_count A B v
  have hcA : (homogeneousZeros A (productLeft v)).card = d := by omega
  have hcB : (homogeneousZeros B (productRight v)).card = e := by omega
  have hall : J = homogeneousZeros (orderedProduct A B) v :=
    eq_of_subset_of_card_le hsub (by omega)
  have hkernel (w : Fin (d + e) → 𝕜)
      (hw : ((orderedProduct A B).submatrix label Fin.succ).mulVec w = 0) : w = 0 := by
    let z : Fin (d + e + 1) → 𝕜 := Fin.cons 0 w
    have hz : ∀ i, orderedProduct A B i ⬝ᵥ v = 0 → orderedProduct A B i ⬝ᵥ z = 0 := by
      intro i hi
      have hiJ : i ∈ J := by rw [hall]; exact mem_filter.mpr ⟨mem_univ _, hi⟩
      obtain ⟨j, _, rfl⟩ := mem_image.mp hiJ
      have h := congrFun hw j
      simpa only [z, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
        mul_zero, zero_add, Matrix.mulVec, Matrix.submatrix, Pi.zero_apply] using h
    have hzA : productLeft z = 0 := by
      apply uniform_active_chart_kernel A hn huA (productLeft v) ht.1.ne' hcA _ rfl
      intro i hi
      rw [← orderedProduct_left_value A B z i]
      apply hz
      simpa only [orderedProduct_left_value] using hi
    have hzB : productRight z = 0 := by
      apply uniform_active_chart_kernel B hm huB (productRight v) ht.1.ne' hcB _ rfl
      intro i hi
      rw [← orderedProduct_right_value A B z i]
      apply hz
      simpa only [orderedProduct_right_value] using hi
    ext j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · exact congrFun hzA k.succ
    · exact congrFun hzB k.succ
  have hdet : ((orderedProduct A B).submatrix label Fin.succ).det ≠ 0 := by
    apply isUnit_iff_ne_zero.mp
    apply (Matrix.isUnit_iff_isUnit_det _).mp
    apply Matrix.mulVec_injective_iff_isUnit.mp
    intro x y hxy
    apply sub_eq_zero.mp
    apply hkernel
    rw [Matrix.mulVec_sub, hxy, sub_self]
  refine ⟨ht.1, hdet, ?_⟩
  intro i hi
  have hrow : orderedProduct A B i ⬝ᵥ v ≠ 0 := by
    intro hz
    have hiJ : i ∈ J := by rw [hall]; exact mem_filter.mpr ⟨mem_univ _, hz⟩
    exact hi (by simpa [J] using hiJ)
  have hs : (starSign c i : 𝕜) ≠ 0 := by
    unfold starSign
    split_ifs <;> simp
  exact lt_of_le_of_ne (hv i) (Ne.symm (mul_ne_zero hs hrow))

#print axioms orderedProduct_star_regularity
#print axioms uniform_active_chart_kernel
#print axioms orderedProduct_zero_count
end
end ADKZPricing
