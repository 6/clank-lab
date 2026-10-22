import ThomsonN10.Interfaces
import Challenge

/-! Final assembly: the complete N=10 target from the package interfaces.
Slack localization and endgame adapted from the MIT N=9 proof
(aravindkarthigeyan/thomson-n9-lean @ 168ff0c, ThomsonN9/Endgame.lean and
ThomsonN9/CentroidBound.lean). -/

namespace ThomsonN10.Assembly

open ThomsonN10 ThomsonN10.Interfaces

theorem pair_slack_le_total (f g : Fin 10 → Fin 10 → ℝ)
    (hminorant : ∀ i j, i < j → g i j ≤ f i j)
    {i j : Fin 10} (hij : i < j) :
    f i j - g i j ≤ pairSum f - pairSum g := by
  have hrow : f i j - g i j ≤ ∑ k ∈ Finset.Ioi i, (f i k - g i k) :=
    Finset.single_le_sum
      (fun k hk => sub_nonneg.mpr (hminorant i k (Finset.mem_Ioi.mp hk)))
      (Finset.mem_Ioi.mpr hij)
  have htotal : (∑ k ∈ Finset.Ioi i, (f i k - g i k)) ≤
      ∑ l : Fin 10, ∑ k ∈ Finset.Ioi l, (f l k - g l k) :=
    Finset.single_le_sum
      (fun l _ => Finset.sum_nonneg fun k hk =>
        sub_nonneg.mpr (hminorant l k (Finset.mem_Ioi.mp hk)))
      (Finset.mem_univ i)
  have heq : (∑ l : Fin 10, ∑ k ∈ Finset.Ioi l, (f l k - g l k)) =
      pairSum f - pairSum g := by
    simp only [pairSum, Finset.sum_sub_distrib]
  linarith

theorem unit_inner_ge {x y : R3} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : -1 ≤ inner ℝ x y := by
  have h := abs_real_inner_le_norm x y
  rw [hx, hy, one_mul] at h
  exact (abs_le.mp h).1

theorem unit_inv_dist {x y : R3} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x - y‖⁻¹ = (Real.sqrt (2 - 2 * inner ℝ x y))⁻¹ := by
  congr 1
  have h : ‖x - y‖ ^ 2 = 2 - 2 * inner ℝ x y := by
    rw [@norm_sub_sq_real, hx, hy]; ring
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

theorem coulombEnergy_eq_pairSum (x : Configuration) :
    coulombEnergy x = pairSum (fun i j => ‖x i - x j‖⁻¹) := rfl

theorem congruent_energy {x y : Configuration} (h : Congruent x y) :
    coulombEnergy x = coulombEnergy y := by
  rcases h with ⟨g, p, hp⟩
  -- double-sum form
  have twice : ∀ z : Configuration, 2 * coulombEnergy z = ∑ i, ∑ j, ‖z i - z j‖⁻¹ := by
    intro z
    classical
    have hterm (i j : Fin 10) : ‖z i - z j‖⁻¹ =
        (if i < j then ‖z i - z j‖⁻¹ else 0) + (if j < i then ‖z i - z j‖⁻¹ else 0) := by
      rcases lt_trichotomy i j with hl | hl | hl
      · simp [hl, not_lt_of_ge hl.le]
      · subst hl; simp
      · simp [hl, not_lt_of_ge hl.le]
    have hup : (∑ i : Fin 10, ∑ j : Fin 10, if i < j then ‖z i - z j‖⁻¹ else 0) =
        coulombEnergy z := by
      unfold coulombEnergy
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_filter]
      congr 1
      ext j
      simp
    have hlo : (∑ i : Fin 10, ∑ j : Fin 10, if j < i then ‖z i - z j‖⁻¹ else 0) =
        coulombEnergy z := by
      rw [Finset.sum_comm]
      convert hup using 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_sub_rev]
    calc 2 * coulombEnergy z
        = (∑ i : Fin 10, ∑ j : Fin 10, if i < j then ‖z i - z j‖⁻¹ else 0) +
          (∑ i : Fin 10, ∑ j : Fin 10, if j < i then ‖z i - z j‖⁻¹ else 0) := by
          rw [hup, hlo]; ring
      _ = ∑ i, ∑ j, ‖z i - z j‖⁻¹ := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          exact (hterm i j).symm
  have hd (i j : Fin 10) : ‖x i - x j‖ = ‖y (p i) - y (p j)‖ := by
    rw [hp i, hp j, ← g.map_sub, g.norm_map]
  have h2 : 2 * coulombEnergy x = 2 * coulombEnergy y := by
    rw [twice, twice]
    simp_rw [hd]
    calc
      (∑ i, ∑ j, (‖y (p i) - y (p j)‖)⁻¹) =
          ∑ i, ∑ j, (‖y (p i) - y j‖)⁻¹ := by
        apply Finset.sum_congr rfl
        intro i _
        exact Equiv.sum_comp p (fun j => (‖y (p i) - y j‖)⁻¹)
      _ = ∑ i, ∑ j, (‖y i - y j‖)⁻¹ :=
        Equiv.sum_comp p (fun i => ∑ j, (‖y i - y j‖)⁻¹)
  linarith

theorem loss_lt_gap : (certLoss : ℝ) < (gapBound : ℝ) := by
  have : certLoss < gapBound := by
    unfold certLoss gapBound; norm_num
  exact_mod_cast this

/-- Every sublevel configuration has all pair products in the contact windows. -/
theorem windows_of_sublevel
    (hLP : LPSeparation) (hPB : PairBound) (hCU : CandidateUpper)
    (hMB : MinorantBound) (hEG : ExteriorGap)
    (h : CandidateParameter) (x : Configuration) (hx : IsSphereConfiguration x)
    (he : coulombEnergy x ≤ coulombEnergy (candidate h)) :
    ∀ i j, i ≠ j → ∃ c : Fin 7, |inner ℝ (x i) (x j) - contact h c| < (windowRadius : ℝ) := by
  have hEU : coulombEnergy x ≤ (certU : ℝ) := he.trans (hCU.1 h)
  have hcap : coulombEnergy x ≤ (energyCap : ℝ) := hEU.trans hCU.2
  have hsep := hLP x hx hcap
  have hbound := hPB x hx (fun i j hij => (hsep i j hij).le)
  let f : Fin 10 → Fin 10 → ℝ := fun i j => (Real.sqrt (2 - 2 * inner ℝ (x i) (x j)))⁻¹
  let g : Fin 10 → Fin 10 → ℝ := fun i j => minorant (inner ℝ (x i) (x j))
  have hfE : pairSum f = coulombEnergy x := by
    rw [coulombEnergy_eq_pairSum]
    unfold pairSum
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    exact (unit_inv_dist (hx.1 i) (hx.1 j)).symm
  have hmin : ∀ i j, i ≠ j → g i j ≤ f i j := fun i j hij =>
    hMB _ (unit_inner_ge (hx.1 i) (hx.1 j)) (hsep i j hij).le
  have hlt : ∀ i j, i < j → ∃ c : Fin 7,
      |inner ℝ (x i) (x j) - contact h c| < (windowRadius : ℝ) := by
    intro i j hij
    by_contra hout
    simp only [not_exists, not_lt] at hout
    have hgap := hEG h _ (unit_inner_ge (hx.1 i) (hx.1 j)) (hsep i j hij.ne).le hout
    have hsingle := pair_slack_le_total f g (fun a b hab => hmin a b hab.ne) hij
    have := loss_lt_gap
    change (gapBound : ℝ) ≤ f i j - g i j at hgap
    linarith
  intro i j hij
  rcases lt_or_gt_of_ne hij with hl | hl
  · exact hlt i j hl
  · obtain ⟨c, hc⟩ := hlt j i hl
    exact ⟨c, by rwa [real_inner_comm]⟩

theorem complete_of_interfaces
    (hP : ParameterExistsUnique) (hLP : LPSeparation) (hPB : PairBound)
    (hCU : CandidateUpper) (hMB : MinorantBound) (hEG : ExteriorGap)
    (hWC : WindowClassification) (hLT : LocalTarget) :
    Challenge.CompleteTarget := by
  have hsub : ∀ h : CandidateParameter, ∀ x : Configuration,
      IsSphereConfiguration x → coulombEnergy x ≤ coulombEnergy (candidate h) →
      Congruent x (candidate h) := by
    intro h x hx he
    exact hLT h x hx (hWC h x hx (windows_of_sublevel hLP hPB hCU hMB hEG h x hx he)) he
  refine ⟨hP, ?_, ?_⟩
  · intro h x hx
    by_cases hle : coulombEnergy x ≤ coulombEnergy (candidate h)
    · exact le_of_eq (congruent_energy (hsub h x hx hle)).symm
    · exact le_of_lt (lt_of_not_ge hle)
  · intro h x hx
    exact ⟨fun he => hsub h x hx he.le, congruent_energy⟩

#print axioms complete_of_interfaces

end ThomsonN10.Assembly
