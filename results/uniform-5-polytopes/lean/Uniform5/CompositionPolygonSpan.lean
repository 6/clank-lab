import Uniform5.CompositionGeometry

/-!
# The explicit regular polygons span their plane

The first three circular vertices are affinely independent: the determinant
of the first two edge differences is positive when the number of sides is
at least three and the circumradius is positive.
-/

noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace

private theorem plane_pair_span_eq_top (u v : Plane)
    (hdet : u 0 * v 1 - u 1 * v 0 ≠ 0) :
    Submodule.span ℝ (Set.range ![u, v]) = ⊤ := by
  have hli : LinearIndependent ℝ ![u, v] := by
    rw [linearIndependent_fin2]
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
    constructor
    · intro hv
      simp [hv] at hdet
    · intro a ha
      have h0 := congrArg (fun z : Plane => z 0) ha
      have h1 := congrArg (fun z : Plane => z 1) ha
      simp only [PiLp.smul_apply, smul_eq_mul] at h0 h1
      apply hdet
      rw [← h0, ← h1]
      ring
  apply hli.span_eq_top_of_card_eq_finrank
  simp [Plane, Space]

/-- The two directions from the first vertex to the next two vertices
span the ambient plane, with a strictly positive oriented determinant. -/
theorem polygon_first_differences_span (n : ℕ) (r : ℝ) (hn : 3 ≤ n) (hr : 0 < r) :
    Submodule.span ℝ (Set.range ![
      polygonPoint n r ⟨1, by omega⟩ - polygonPoint n r ⟨0, by omega⟩,
      polygonPoint n r ⟨2, by omega⟩ - polygonPoint n r ⟨0, by omega⟩]) = ⊤ := by
  let θ : ℝ := 2 * Real.pi / n
  have hn' : (2 : ℝ) < n := by exact_mod_cast (show 2 < n by omega)
  have htpos : 0 < θ := div_pos (mul_pos (by norm_num) Real.pi_pos) (by linarith)
  have htpi : θ < Real.pi := by
    apply (div_lt_iff₀ (by linarith : (0 : ℝ) < n)).mpr
    nlinarith [Real.pi_pos]
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi htpos htpi
  have hc : Real.cos θ < 1 := by
    have hsq := Real.sin_sq_add_cos_sq θ
    have hcle := Real.cos_le_one θ
    have hs2 : 0 < (Real.sin θ) ^ 2 := sq_pos_of_pos hs
    nlinarith
  apply plane_pair_span_eq_top
  have hangle : 2 * Real.pi * (2 : ℕ) / n = 2 * θ := by dsimp [θ]; ring
  have hpositive : 0 < 2 * r ^ 2 * Real.sin θ * (1 - Real.cos θ) :=
    mul_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hr)) hs) (sub_pos.mpr hc)
  have hdet :
      (r * Real.cos θ - r) * (r * Real.sin (2 * θ)) -
        (r * Real.sin θ) * (r * Real.cos (2 * θ) - r) =
      2 * r ^ 2 * Real.sin θ * (1 - Real.cos θ) := by
    rw [Real.sin_two_mul, Real.cos_two_mul]
    ring
  simp only [polygonPoint, PiLp.sub_apply, WithLp.equiv_symm_pi_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Nat.cast_zero, Nat.cast_one, mul_zero, zero_div, Real.cos_zero, Real.sin_zero,
    mul_one, mul_zero, sub_zero, hangle]
  change (r * Real.cos θ - r) * (r * Real.sin (2 * θ)) -
      (r * Real.sin θ) * (r * Real.cos (2 * θ) - r) ≠ 0
  rw [hdet]
  exact ne_of_gt hpositive

/-- The explicit regular polygon really is two-dimensional. -/
theorem affineSpan_polygon_eq_top (n : ℕ) (r : ℝ) (hn : 3 ≤ n) (hr : 0 < r) :
    affineSpan ℝ (polygon n r) = ⊤ := by
  rw [polygon, affineSpan_convexHull (𝕜 := ℝ)]
  apply (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nontrivial ℝ Plane Plane).mpr
  have hspan := polygon_first_differences_span n r hn hr
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  fin_cases i
  · exact vsub_mem_vectorSpan ℝ (Set.mem_range_self _) (Set.mem_range_self _)
  · exact vsub_mem_vectorSpan ℝ (Set.mem_range_self _) (Set.mem_range_self _)

@[simp] theorem affineDimension_polygon (n : ℕ) (r : ℝ) (hn : 3 ≤ n) (hr : 0 < r) :
    affineDimension (polygon n r) = 2 := by
  rw [affineDimension, Uniform5.affineDimension, affineSpan_polygon_eq_top n r hn hr, AffineSubspace.direction_top]
  simp [Plane, Space]

end Uniform5.Composition
