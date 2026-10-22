/- Adapted from targets/thomson-10/lp-formal/n10/Thomson10/Proof.lean (supplied accepted N10 LP proof). N9 design: aravindkarthigeyan/thomson-n9-lean, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e, proof/lean/ThomsonN9/LP/Concrete.lean. -/
import ThomsonN10.Cert.LP.Scalar
import ThomsonN10.Cert.LP.Geometry
import ThomsonN10.Cert.LP.Sums

open scoped BigOperators InnerProductSpace
noncomputable section
set_option maxHeartbeats 0
namespace ThomsonN10.Cert.LP

theorem ordered_lower_bound (p : Fin 10 → Point) (hp : ∀ i, ‖p i‖=1) :
    100*a0 ≤ ∑ i : Fin 10, ∑ j : Fin 10, h ⟪p i,p j⟫_ℝ := by
  have hswap (F : Fin 10 → Fin 10 → Fin 24 → ℝ) :
      (∑ i : Fin 10, ∑ j : Fin 10, ∑ m : Fin 24, F i j m) =
      ∑ m : Fin 24, ∑ i : Fin 10, ∑ j : Fin 10, F i j m := by
    calc
      _ = ∑ i : Fin 10, ∑ m : Fin 24, ∑ j : Fin 10, F i j m := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  have hexp : (∑ i : Fin 10, ∑ j : Fin 10, h ⟪p i,p j⟫_ℝ) =
      100*a0 + ∑ m : Fin 24, weights m * (∑ i : Fin 10, feature m (p i))^2 := by
    simp_rw [kernel_identity _ _ (hp _) (hp _), Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hswap]
    congr 1
    · norm_num; ring
    · apply Finset.sum_congr rfl
      intro m _
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum, mul_assoc]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
  rw [hexp]
  have hn : 0 ≤ ∑ m : Fin 24, weights m * (∑ i : Fin 10, feature m (p i))^2 := by
    apply Finset.sum_nonneg
    intro m _
    exact mul_nonneg (weights_nonneg m) (sq_nonneg _)
  linarith

theorem polynomial_lower_bound (p : Fin 10 → Point) (hp : ∀ i, ‖p i‖=1) :
    (13111005315721/401353681050 : ℝ) ≤
      pairSum (fun i j => h ⟪p i,p j⟫_ℝ) := by
  have hs := sum_symmetric (fun i j => h ⟪p i,p j⟫_ℝ)
    (fun i j => by rw [real_inner_comm])
  have hd : (∑ i : Fin 10, h ⟪p i,p i⟫_ℝ) = 10*h 1 := by
    simp_rw [real_inner_self_eq_norm_sq, hp]
    norm_num
  rw [hd] at hs
  have hb := ordered_lower_bound p hp
  have hc : (100*a0-10*h 1)/2 = (13111005315721/401353681050 : ℝ) := by
    norm_num [a0,h]
  linarith

 theorem lp_separation (p : Fin 10 → EuclideanSpace ℝ (Fin 3))
    (hunit : ∀ i, ‖p i‖=1) (hinjective : Function.Injective p)
    (henergy : energy p ≤ (32717/1000 : ℝ)) :
    ∀ i j, i ≠ j → ⟪p i,p j⟫_ℝ < (13/20 : ℝ) := by
  let r : Fin 10 → Fin 10 → ℝ := fun i j => ‖p i-p j‖⁻¹-h ⟪p i,p j⟫_ℝ
  have hdpos (i j : Fin 10) (hij : i ≠ j) : 0 < ‖p i-p j‖ := by
    apply norm_pos_iff.mpr
    apply sub_ne_zero.mpr
    exact fun he => hij (hinjective he)
  have hr (i j : Fin 10) (hij : i < j) : 0 ≤ r i j := by
    dsimp [r]
    have hm := minorant ⟪p i,p j⟫_ℝ ‖p i-p j‖
      (inner_bounds _ _ (hunit i) (hunit j)) (hdpos i j (ne_of_lt hij))
      (distance_sq _ _ (hunit i) (hunit j))
    linarith
  have he : energy p = pairSum (fun i j => h ⟪p i,p j⟫_ℝ)+pairSum r := by
    simp only [energy, pairSum, r, Finset.sum_sub_distrib]
    ring
  have hb := polynomial_lower_bound p hunit
  intro i j hij
  by_contra hn
  have ht : (13/20 : ℝ) ≤ ⟪p i,p j⟫_ℝ := le_of_not_gt hn
  have hbonus : (51/1000 : ℝ) < r i j := by
    exact residual_bonus _ _ ⟨ht,(inner_bounds _ _ (hunit i) (hunit j)).2⟩
      (hdpos i j hij) (distance_sq _ _ (hunit i) (hunit j))
  have hsingle : r i j ≤ pairSum r := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact pair_le_pairSum r hr i j hlt
    · have hsym : r i j = r j i := by
        dsimp [r]
        rw [norm_sub_rev, real_inner_comm]
      rw [hsym]
      exact pair_le_pairSum r hr j i hgt
  have hmargin : (32717/1000 : ℝ) < 13111005315721/401353681050+51/1000 := by
    norm_num
  linarith

#print axioms lp_separation
end ThomsonN10.Cert.LP
