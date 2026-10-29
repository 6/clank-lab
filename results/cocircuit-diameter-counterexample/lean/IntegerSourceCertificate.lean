import SourceRegularity

namespace ADKZPricing
open Matrix Finset
noncomputable section

/-- Finite discovered data, with positive homogeneous integer coordinates.
No vertex completeness, graph distance or genericity premise is a field. -/
structure IntegerSourceData {n d : ℕ} (V : Type*) where
  ray : V → Fin (d + 1) → ℤ
  basis : V → Fin d → Fin n
  next : V → Fin d → V

structure IntegerSourceValid {n d : ℕ} {V : Type*}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (D : IntegerSourceData (n := n) (d := d) V) : Prop where
  chart_positive : ∀ v, 0 < D.ray v 0
  feasible : ∀ v i, 0 ≤ A i ⬝ᵥ D.ray v
  basis_injective : ∀ v, Function.Injective (D.basis v)
  active_exact : ∀ v i, A i ⬝ᵥ D.ray v = 0 ↔ ∃ j, D.basis v j = i
  neighbor_keeps : ∀ v j k, k ≠ j → ∃ l, D.basis (D.next v j) l = D.basis v k
  neighbor_leaves : ∀ v j, ¬ ∃ l, D.basis (D.next v j) l = D.basis v j

def integerSourcePoint {d : ℕ} (w : Fin (d + 1) → ℤ) : Fin d → ℚ :=
  fun j => (w j.succ : ℚ) / (w 0 : ℚ)

/-- The denominator is common and positive. Every signed source slack
is exactly the integer homogeneous slack divided by that denominator. -/
theorem integerSource_slack {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (w : Fin (d + 1) → ℤ)
    (h0 : 0 < w 0) (i : Fin n) :
    sourceSpatial (A.map (Int.castRingHom ℚ)) i ⬝ᵥ integerSourcePoint w -
      sourceBound (A.map (Int.castRingHom ℚ)) i = ((A i ⬝ᵥ w : ℤ) : ℚ) / (w 0 : ℚ) := by
  have hn : (w 0 : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt h0
  have he : ((A i ⬝ᵥ w : ℤ) : ℚ) =
      (A i 0 : ℚ) * (w 0 : ℚ) + ∑ j : Fin d, (A i j.succ : ℚ) * (w j.succ : ℚ) := by
    simp [dotProduct, Fin.sum_univ_succ]
  rw [he, add_div, mul_div_cancel_right₀ _ hn]
  simp [sourceSpatial, sourceBound, integerSourcePoint, dotProduct,
    mul_div_assoc, Finset.sum_div, add_comm]

namespace IntegerSourceValid
variable {n d : ℕ} {V : Type*} {A : Matrix (Fin n) (Fin (d + 1)) ℤ}
variable {D : IntegerSourceData (n := n) (d := d) V} (H : IntegerSourceValid A D)

include H in
theorem affine_active_iff (v : V) (i : Fin n) :
    sourceSpatial (A.map (Int.castRingHom ℚ)) i ⬝ᵥ integerSourcePoint (D.ray v) =
      sourceBound (A.map (Int.castRingHom ℚ)) i ↔ ∃ j, D.basis v j = i := by
  rw [← sub_eq_zero, integerSource_slack A _ (H.chart_positive v) i]
  have hn : (D.ray v 0 : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt (H.chart_positive v)
  rw [div_eq_zero_iff, or_iff_left hn, Int.cast_eq_zero]
  exact H.active_exact v i

/-- This constructor discharges every field of the source cover theorem
from exact integer slacks and original neighbor labels. It introduces no
extra cover, boundedness, regularity or abstract graph hypothesis. -/
def toCertificate : SourceVertexCertificate
    (sourceSpatial (A.map (Int.castRingHom ℚ)))
    (sourceBound (A.map (Int.castRingHom ℚ))) V where
  point v := integerSourcePoint (D.ray v)
  basis := D.basis
  next := D.next
  feasible v i := by
    rw [← sub_nonneg, integerSource_slack A _ (H.chart_positive v) i]
    exact div_nonneg (by exact_mod_cast H.feasible v i)
      (by exact_mod_cast (H.chart_positive v).le)
  basis_injective := H.basis_injective
  active_exact := H.affine_active_iff
  neighbor_keeps v j k hk := (H.affine_active_iff _ _).mpr (H.neighbor_keeps v j k hk)
  neighbor_leaves v j := fun h => H.neighbor_leaves v j ((H.affine_active_iff _ _).mp h)

end IntegerSourceValid

#print axioms integerSource_slack
#print axioms IntegerSourceValid.toCertificate
end
end ADKZPricing
