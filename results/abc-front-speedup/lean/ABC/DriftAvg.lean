import ABC.Tube

/-!
Proof of `tube_averages`, flow-free, by integration by parts on the torus:
* `integral_fderiv_abcField_eq_zero`: `∫_cell V·∇F = 0` for Lipschitz periodic `F`, since
  each `V_i` is independent of `x_i`, so `V_i ∂_i F` is the limit of difference quotients of
  `V_i F` in direction `i`, whose cell integrals vanish by periodicity (dominated convergence);
* zero `x`/`y`-drift: apply it to `F = χ W` with `χ = saw (x_j)`, a periodic sawtooth of slope
  `1` on the bands containing the support of `W`, so `V·∇F = V_j W` almost everywhere;
* positive `z`-drift: `V_z W ≥ 0`, and `V_z W > 0` on a nonempty open subset of the cell.
-/

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace ABC

private lemma box_fubini {L : ℝ} (i : Fin 3) (h : (Fin 3 → ℝ) → ℝ) (hh : Continuous h) :
    ∫ y in Set.univ.pi (fun _ => Set.Ico (0:ℝ) L), h y =
      ∫ q : Fin 2 → ℝ, ∫ x, h (Fin.insertNth i x q) ∂(volume.restrict (Set.Ico 0 L))
        ∂(Measure.pi fun _ => volume.restrict (Set.Ico (0:ℝ) L)) := by
  have hint : IntegrableOn h (Set.univ.pi (fun _ => Set.Ico (0:ℝ) L)) := by
    refine (hh.continuousOn.integrableOn_compact
      (isCompact_univ_pi fun _ => isCompact_Icc (a := (0:ℝ)) (b := L))).mono_set ?_
    exact Set.pi_mono fun _ _ => Set.Ico_subset_Icc_self
  rw [IntegrableOn, volume_pi, Measure.restrict_pi_pi] at hint
  rw [volume_pi, Measure.restrict_pi_pi]
  have hmp := (measurePreserving_piFinSuccAbove
    (fun _ : Fin 3 => volume.restrict (Set.Ico (0:ℝ) L)) i).symm
  rw [← hmp.integral_comp', integral_prod_symm]
  · rfl
  · exact (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hint


private lemma Ico_shift {L : ℝ} (hL : 0 < L) (φ : ℝ → ℝ)
    (hper : Function.Periodic φ L) (t : ℝ) :
    ∫ x in Set.Ico 0 L, φ (x + t) = ∫ x in Set.Ico 0 L, φ x := by
  rw [integral_Ico_eq_integral_Ioc, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hL.le, ← intervalIntegral.integral_of_le hL.le,
    intervalIntegral.integral_comp_add_right]
  simpa [add_comm] using hper.intervalIntegral_add_eq t 0

private lemma pi_shift {L : ℝ} (hL : 0 < L) (i : Fin 3) (g : (Fin 3 → ℝ) → ℝ) (hg : Continuous g)
    (hper : ∀ y, g (y + L • Pi.single i 1) = g y) (t : ℝ) :
    ∫ y in Set.univ.pi (fun _ => Set.Ico (0:ℝ) L), g (y + t • Pi.single i 1) =
      ∫ y in Set.univ.pi (fun _ => Set.Ico (0:ℝ) L), g y := by
  have hins : ∀ (x s : ℝ) (q : Fin 2 → ℝ),
      Fin.insertNth i x q + s • Pi.single i 1 = Fin.insertNth i (x + s) q := by
    intro x s q
    ext j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · simp
    · simp [Fin.succAbove_ne]
  refine (box_fubini (L := L) i (fun y => g (y + t • Pi.single i 1))
    (hg.comp (continuous_id.add continuous_const))).trans
    (Eq.trans ?_ (box_fubini (L := L) i _ hg).symm)
  congr 1
  ext q
  simp only [hins]
  refine Ico_shift hL (fun x => g (Fin.insertNth i x q)) ?_ t
  intro x
  simp only [← hins, hper]


private lemma cell_eq_preimage (L : ℝ) :
    WithLp.toLp 2 ⁻¹' cell 3 L = Set.univ.pi (fun _ => Set.Ico (0:ℝ) L) := by
  ext y; simp [cell]

private lemma cell_integral_eq (L : ℝ) (G : E 3 → ℝ) :
    ∫ x in cell 3 L, G x = ∫ y in Set.univ.pi (fun _ => Set.Ico (0:ℝ) L), G (WithLp.toLp 2 y) := by
  rw [← cell_eq_preimage, (PiLp.volume_preserving_toLp (Fin 3)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding]

private lemma toLp_add_single (y : Fin 3 → ℝ) (t : ℝ) (i : Fin 3) :
    WithLp.toLp 2 y + t • ev i = WithLp.toLp 2 (y + t • Pi.single i 1) := by
  ext j; simp [Pi.single_apply, PiLp.single_apply]

private lemma cell_shift {L : ℝ} (hL : 0 < L) (i : Fin 3) (G : E 3 → ℝ) (hG : Continuous G)
    (hper : ∀ x, G (x + L • ev i) = G x) (t : ℝ) :
    ∫ x in cell 3 L, G (x + t • ev i) = ∫ x in cell 3 L, G x := by
  rw [cell_integral_eq, cell_integral_eq]
  simp only [toLp_add_single]
  refine pi_shift hL i (fun y => G (WithLp.toLp 2 y))
    (hG.comp (PiLp.continuous_toLp 2 _)) (fun y => ?_) t
  simp only [← toLp_add_single, hper]


private lemma abcField_shift (i : Fin 3) (x : E 3) (t : ℝ) :
    abcField (x + t • ev i) i = abcField x i := by
  fin_cases i <;> simp [abcField]

private lemma abcField_abs_le (x : E 3) (i : Fin 3) : |abcField x i| ≤ 2 := by
  have key : ∀ a b : ℝ, |Real.sin a + Real.cos b| ≤ 2 := fun a b =>
    (abs_add_le _ _).trans (by linarith [Real.abs_sin_le_one a, Real.abs_cos_le_one b])
  fin_cases i <;> simp [abcField, key]

private lemma continuous_abcField_apply (i : Fin 3) : Continuous fun x : E 3 => abcField x i := by
  fin_cases i <;> simp [abcField] <;> fun_prop

private lemma integrableOn_cell {L : ℝ} (G : E 3 → ℝ) (hG : Continuous G) :
    IntegrableOn G (cell 3 L) := by
  have hK : IsCompact (WithLp.toLp 2 '' Set.univ.pi (fun _ : Fin 3 => Set.Icc (0:ℝ) L)) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
  refine (hG.continuousOn.integrableOn_compact hK).mono_set ?_
  intro x hx
  refine ⟨WithLp.ofLp x, fun i _ => Set.Ico_subset_Icc_self (hx i), by simp⟩

private lemma eq_sum_single (y : E 3) : y = ∑ i, y i • ev i := by
  ext j; fin_cases j <;> simp [Fin.sum_univ_three]

/-- Integration by parts on the torus: `∫_cell V·∇F = 0` for Lipschitz periodic `F`. -/
private lemma integral_fderiv_abcField_eq_zero {F : E 3 → ℝ} {K : NNReal} (hF : LipschitzWith K F)
    (hper : Periodic (2 * Real.pi) F) {D : E 3 → E 3 →L[ℝ] ℝ}
    (hD : ∀ᵐ x, HasFDerivAt F (D x) x) :
    ∫ x in cell 3 (2 * Real.pi), D x (abcField x) = 0 := by
  have hL : 0 < 2 * Real.pi := by positivity
  set Q : ℝ → E 3 → ℝ := fun t x =>
    ∑ i, abcField x i * (t⁻¹ * (F (x + t • ev i) - F x)) with hQ
  have hQc : ∀ t i, Continuous fun x => abcField x i * (t⁻¹ * (F (x + t • ev i) - F x)) :=
    fun t i => (continuous_abcField_apply i).mul (continuous_const.mul
      ((hF.continuous.comp (continuous_id.add continuous_const)).sub hF.continuous))
  have hQ0 : ∀ t, ∫ x in cell 3 (2 * Real.pi), Q t x = 0 := by
    intro t
    simp only [hQ]
    rw [integral_finsetSum _ (fun i _ => integrableOn_cell _ (hQc t i))]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hG : Continuous fun x => abcField x i * F x :=
      (continuous_abcField_apply i).mul hF.continuous
    have h1 : ∀ x, abcField x i * (t⁻¹ * (F (x + t • ev i) - F x)) =
        t⁻¹ * (abcField (x + t • ev i) i * F (x + t • ev i) - abcField x i * F x) := by
      intro x; rw [abcField_shift]; ring
    simp only [h1]
    have hi1 : IntegrableOn (fun x => abcField (x + t • ev i) i * F (x + t • ev i))
        (cell 3 (2 * Real.pi)) :=
      integrableOn_cell _ (hG.comp (continuous_id.add continuous_const))
    rw [integral_const_mul, integral_sub hi1 (integrableOn_cell _ hG),
      cell_shift hL i (fun x => abcField x i * F x) hG
        (fun x => by simp only [abcField_shift, hper i x]) t, sub_self, mul_zero]
  have hlim : Tendsto (fun t => ∫ x in cell 3 (2 * Real.pi), Q t x) (𝓝[≠] 0)
      (𝓝 (∫ x in cell 3 (2 * Real.pi), D x (abcField x))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 6 * K) ?_ ?_
      (integrableOn_cell _ continuous_const) ?_
    · exact Eventually.of_forall fun t =>
        (continuous_finsetSum _ fun i _ => hQc t i).aestronglyMeasurable
    · refine Eventually.of_forall fun t => Eventually.of_forall fun x => ?_
      have hb : ∀ i, |abcField x i * (t⁻¹ * (F (x + t • ev i) - F x))| ≤ 2 * K := by
        intro i
        rw [abs_mul, abs_mul, abs_inv]
        have h2 : |F (x + t • ev i) - F x| ≤ K * |t| := by
          have := hF.dist_le_mul (x + t • ev i) x
          simpa [Real.dist_eq, dist_eq_norm, norm_smul, PiLp.norm_single] using this
        have h3 : |t|⁻¹ * |F (x + t • ev i) - F x| ≤ K := by
          rcases eq_or_ne t 0 with rfl | ht
          · simp
          · rw [inv_mul_le_iff₀ (abs_pos.mpr ht)]; linarith
        exact mul_le_mul (abcField_abs_le x i) h3 (by positivity) (by norm_num)
      simp only [hQ, Real.norm_eq_abs]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ => hb i).trans ?_
      simp; linarith
    · filter_upwards [ae_restrict_of_ae hD] with x hx
      have hsl : ∀ i, Tendsto (fun t : ℝ => t⁻¹ * (F (x + t • ev i) - F x)) (𝓝[≠] 0)
          (𝓝 (D x (ev i))) := by
        intro i
        have h1 : HasDerivAt (fun t : ℝ => x + t • ev i) (ev i) 0 := by
          simpa using ((hasDerivAt_id (0:ℝ)).smul_const (ev i)).const_add x
        have h2 : HasFDerivAt F (D x) (x + (0:ℝ) • ev i) := by simpa using hx
        have := (hasDerivAt_iff_tendsto_slope_zero.mp (h2.comp_hasDerivAt 0 h1))
        simpa using this
      have hV : D x (abcField x) = ∑ i, abcField x i * D x (ev i) := by
        conv_lhs => rw [eq_sum_single (abcField x)]
        simp [map_sum]
      rw [hV]
      exact tendsto_finsetSum _ fun i _ => tendsto_const_nhds.mul (hsl i)
  have h0 : Tendsto (fun t => ∫ x in cell 3 (2 * Real.pi), Q t x) (𝓝[≠] 0) (𝓝 0) := by
    simp only [hQ0]; exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim h0


/-- The tent `max v (-M v)` with slope `1` on the right and `-M` on the left. -/
private def tent (M v : ℝ) : ℝ := max v (-(M * v))

/-- A `p`-periodic sawtooth: slope `1` on most of each period, slope `-M` near `A + pℤ`. -/
private def saw (A M p u : ℝ) : ℝ := ⨅ k : ℤ, tent M (u - A - k * p)

private lemma tent_nonneg {M : ℝ} (hM : 0 ≤ M) (v : ℝ) : 0 ≤ tent M v := by
  unfold tent; rcases le_total 0 v with h | h
  · exact le_max_of_le_left h
  · exact le_max_of_le_right (by nlinarith)

private lemma tent_le_add {M : ℝ} (hM : 0 ≤ M) (v v' : ℝ) :
    tent M v ≤ tent M v' + (1 + M) * |v - v'| := by
  unfold tent
  have h1 := le_abs_self (v - v')
  have h2 := neg_abs_le (v - v')
  have h3 : M * (v' - v) ≤ M * |v - v'| := mul_le_mul_of_nonneg_left (by linarith) hM
  have h4 := abs_nonneg (v - v')
  apply max_le
  · nlinarith [le_max_left v' (-(M * v'))]
  · nlinarith [le_max_right v' (-(M * v'))]

private lemma saw_bdd {A M p : ℝ} (hM : 0 ≤ M) (u : ℝ) :
    BddBelow (Set.range fun k : ℤ => tent M (u - A - k * p)) :=
  ⟨0, by rintro _ ⟨k, rfl⟩; exact tent_nonneg hM _⟩

private lemma saw_nonneg {A M p : ℝ} (hM : 0 ≤ M) (u : ℝ) : 0 ≤ saw A M p u :=
  le_ciInf fun _ => tent_nonneg hM _

private lemma saw_le {A M p : ℝ} (hM : 0 ≤ M) (hp : 0 < p) (u : ℝ) : saw A M p u ≤ p := by
  refine (ciInf_le (saw_bdd hM u) ⌊(u - A) / p⌋).trans ?_
  have h1 := Int.floor_le ((u - A) / p)
  have h2 := Int.lt_floor_add_one ((u - A) / p)
  have h1' : (⌊(u - A) / p⌋ : ℝ) * p ≤ u - A := by
    have := mul_le_mul_of_nonneg_right h1 hp.le; rwa [div_mul_cancel₀ _ hp.ne'] at this
  have h2' : u - A < ((⌊(u - A) / p⌋ : ℝ) + 1) * p := by
    have := mul_lt_mul_of_pos_right h2 hp; rwa [div_mul_cancel₀ _ hp.ne'] at this
  unfold tent
  apply max_le
  · nlinarith
  · nlinarith

private lemma saw_le_add {A M p : ℝ} (hM : 0 ≤ M) (u u' : ℝ) :
    saw A M p u ≤ saw A M p u' + (1 + M) * dist u u' := by
  rw [← sub_le_iff_le_add]
  refine le_ciInf fun k => ?_
  rw [sub_le_iff_le_add]
  refine (ciInf_le (saw_bdd hM u) k).trans ?_
  have := tent_le_add hM (u - A - k * p) (u' - A - k * p)
  rw [Real.dist_eq]
  convert this using 3; ring_nf

private lemma saw_lipschitz {A M p : ℝ} (hM : 0 ≤ M) :
    LipschitzWith (Real.toNNReal (1 + M)) (saw A M p) :=
  LipschitzWith.of_le_add_mul' _ fun u u' => saw_le_add hM u u'

private lemma saw_add_period (A M p u : ℝ) : saw A M p (u + p) = saw A M p u := by
  unfold saw
  rw [← (Equiv.addRight (1 : ℤ)).iInf_comp]
  congr 1; ext k; congr 1; simp only [Equiv.coe_addRight]; push_cast; ring

private lemma saw_eq {A M p : ℝ} (hM : 0 ≤ M) (hp : 0 < p) (u : ℝ) (m : ℤ)
    (h0 : 0 ≤ u - A - m * p) (h1 : u - A - m * p ≤ M * (p - (u - A - m * p))) :
    saw A M p u = u - A - m * p := by
  apply le_antisymm
  · refine (ciInf_le (saw_bdd hM u) m).trans ?_
    unfold tent; exact max_le le_rfl (by nlinarith)
  · refine le_ciInf fun k => ?_
    unfold tent
    rcases le_or_gt k m with hk | hk
    · have : (k : ℝ) ≤ m := by exact_mod_cast hk
      exact le_max_of_le_left (by nlinarith)
    · have : (m : ℝ) + 1 ≤ k := by exact_mod_cast hk
      have := mul_nonneg (mul_nonneg hM (sub_nonneg.2 this)) hp.le
      exact le_max_of_le_right (by nlinarith)


private lemma periodic_int {L : ℝ} {G : E 3 → ℝ} (hper : Periodic L G) (k : ℤ) (i : Fin 3)
    (x : E 3) : G (x + ((k : ℝ) * L) • ev i) = G x := by
  have : Function.Periodic (fun s : ℝ => G (x + s • ev i)) L := fun s => by
    simp only [add_smul, ← add_assoc, hper i]
  simpa using this.int_mul_eq k

private lemma exists_cell_eq {L : ℝ} (hL : 0 < L) {G : E 3 → ℝ} (hper : Periodic L G) (x : E 3) :
    ∃ y ∈ cell 3 L, G y = G x := by
  set d : Fin 3 → ℤ := fun i => -toIcoDiv hL 0 (x i)
  refine ⟨x + ((d 0 : ℝ) * L) • ev 0 + ((d 1 : ℝ) * L) • ev 1 + ((d 2 : ℝ) * L) • ev 2,
    ?_, by rw [periodic_int hper, periodic_int hper, periodic_int hper]⟩
  intro i
  have key : ∀ j : Fin 3, x j + (d j : ℝ) * L ∈ Set.Ico 0 L := by
    intro j
    have := toIcoMod_mem_Ico hL 0 (x j)
    rw [← self_sub_toIcoDiv_zsmul, zero_add] at this
    simpa [d, sub_eq_add_neg, zsmul_eq_mul] using this
  fin_cases i <;> simpa using key _

private lemma cell_subset_compact (L : ℝ) :
    cell 3 L ⊆ WithLp.toLp 2 '' Set.univ.pi (fun _ : Fin 3 => Set.Icc (0:ℝ) L) :=
  fun x hx => ⟨WithLp.ofLp x, fun i _ => Set.Ico_subset_Icc_self (hx i), by simp⟩

private lemma exists_bound {L : ℝ} (hL : 0 < L) {G : E 3 → ℝ} (hG : Continuous G)
    (hper : Periodic L G) : ∃ B, ∀ x, |G x| ≤ B := by
  have hK : IsCompact (WithLp.toLp 2 '' Set.univ.pi (fun _ : Fin 3 => Set.Icc (0:ℝ) L)) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hG.continuousOn
  refine ⟨B, fun x => ?_⟩
  obtain ⟨y, hy, hyx⟩ := exists_cell_eq hL hper x
  rw [← hyx, ← Real.norm_eq_abs]
  exact hB y (cell_subset_compact L hy)


/-- A first integral whose support projects into bands in coordinate `j` has zero
`j`-drift. -/
private lemma integral_abcField_mul_eq_zero {W : E 3 → ℝ} {KW : NNReal} (hWl : LipschitzWith KW W)
    (hWp : Periodic (2 * Real.pi) W) (hW0 : ∀ x, 0 ≤ W x)
    (hflow : ∀ᵐ x, ⟪abcField x, gradient W x⟫ = 0) (j : Fin 3) (A δ : ℝ) (hδ : 0 < δ)
    (hband : ∀ x, W x ≠ 0 → ∃ m : ℤ,
      x j ∈ Set.Icc (A + 2 * Real.pi * m + δ) (A + 2 * Real.pi * (m + 1) - δ)) :
    ∫ x in cell 3 (2 * Real.pi), abcField x j * W x = 0 := by
  set p := 2 * Real.pi with hp_def
  have hp : 0 < p := by positivity
  set M := 2 * p / δ with hM_def
  have hM : 0 ≤ M := by positivity
  have hMδ : M * δ = 2 * p := by rw [hM_def]; field_simp
  obtain ⟨B, hB⟩ := exists_bound hp hWl.continuous hWp
  set χ : E 3 → ℝ := fun x => saw A M p (x j) with hχ
  have hχ0 : ∀ x, 0 ≤ χ x := fun x => saw_nonneg hM _
  have hχp : ∀ x, χ x ≤ p := fun x => saw_le hM hp _
  set F : E 3 → ℝ := fun x => χ x * W x with hF
  have hFl : LipschitzWith (Real.toNNReal (p * KW + B * (1 + M))) F := by
    refine LipschitzWith.of_dist_le' fun x y => ?_
    have h1 : |W x - W y| ≤ KW * dist x y := by
      simpa [Real.dist_eq] using hWl.dist_le_mul x y
    have h2 : |χ x - χ y| ≤ (1 + M) * dist x y := by
      have := (saw_lipschitz (A := A) (p := p) hM).dist_le_mul (x j) (y j)
      rw [Real.coe_toNNReal _ (by positivity)] at this
      simpa [Real.dist_eq] using
        this.trans (mul_le_mul_of_nonneg_left (PiLp.dist_apply_le x y j) (by positivity))
    rw [Real.dist_eq]
    have : χ x * W x - χ y * W y = χ x * (W x - W y) + W y * (χ x - χ y) := by ring
    simp only [hF]; rw [this]
    calc |χ x * (W x - W y) + W y * (χ x - χ y)|
        ≤ |χ x| * |W x - W y| + |W y| * |χ x - χ y| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ p * (KW * dist x y) + B * ((1 + M) * dist x y) := by
          refine add_le_add (mul_le_mul ?_ h1 (abs_nonneg _) hp.le)
            (mul_le_mul (hB y) h2 (abs_nonneg _) ((abs_nonneg _).trans (hB y)))
          rw [abs_of_nonneg (hχ0 x)]; exact hχp x
      _ = (p * KW + B * (1 + M)) * dist x y := by ring
  have hFp : Periodic p F := by
    intro i x
    simp only [hF, hχ, hWp i x]
    congr 1
    by_cases hij : i = j
    · subst hij; simp [saw_add_period]
    · simp [Ne.symm hij]
  set D : E 3 → E 3 →L[ℝ] ℝ := fun x => if W x = 0 then 0 else
    χ x • fderiv ℝ W x + W x • (EuclideanSpace.proj j : E 3 →L[ℝ] ℝ) with hD_def
  have hloc : ∀ x, W x ≠ 0 → ∃ c : ℝ, ∀ᶠ y in 𝓝 x, χ y = y j - c := by
    intro x hx
    obtain ⟨m, hm1, hm2⟩ := hband x hx
    refine ⟨A + m * p, ?_⟩
    have hc : Continuous fun y : E 3 => y j := by fun_prop
    have hU : ∀ᶠ y in 𝓝 x, y j ∈ Set.Ioo (x j - δ / 2) (x j + δ / 2) :=
      hc.continuousAt (Ioo_mem_nhds (by linarith) (by linarith))
    filter_upwards [hU] with y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hw : δ / 2 ≤ p - (y j - A - m * p) := by nlinarith
    have hw' : M * (δ / 2) ≤ M * (p - (y j - A - m * p)) := mul_le_mul_of_nonneg_left hw hM
    simp only [hχ]
    rw [saw_eq hM hp (y j) m (by nlinarith) (by nlinarith)]
    ring
  have hD : ∀ᵐ x, HasFDerivAt F (D x) x := by
    filter_upwards [hWl.ae_differentiableAt] with x hx
    by_cases h : W x = 0
    · simp only [hD_def, h, ite_true]
      have hmin : IsLocalMin W x := Filter.Eventually.of_forall fun y => by
        rw [h]; exact hW0 y
      have hW' : HasFDerivAt W (0 : E 3 →L[ℝ] ℝ) x := by
        rw [← hmin.fderiv_eq_zero]; exact hx.hasFDerivAt
      rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hW' ⊢
      refine Asymptotics.IsBigO.trans_isLittleO ?_ hW'
      refine Asymptotics.IsBigO.of_bound p (Eventually.of_forall fun h' => ?_)
      simp only [hF, h, mul_zero, sub_zero, Real.norm_eq_abs]
      show |χ (x + h') * W (x + h') - 0| ≤ p * |W (x + h') - 0|
      rw [sub_zero, sub_zero, abs_mul]
      rw [abs_of_nonneg (hχ0 _)]
      exact mul_le_mul_of_nonneg_right (hχp _) (abs_nonneg _)
    · obtain ⟨c, hc⟩ := hloc x h
      have hχd : HasFDerivAt χ (EuclideanSpace.proj j : E 3 →L[ℝ] ℝ) x := by
        have h0 : HasFDerivAt (fun y : E 3 => y j) (EuclideanSpace.proj j : E 3 →L[ℝ] ℝ) x :=
          (EuclideanSpace.proj j : E 3 →L[ℝ] ℝ).hasFDerivAt
        have := h0.sub_const c
        exact this.congr_of_eventuallyEq hc
      simp only [hD_def, h, ite_false]
      exact hχd.mul hx.hasFDerivAt
  have hint : ∀ᵐ x, D x (abcField x) = abcField x j * W x := by
    filter_upwards [hflow] with x hfx
    by_cases h : W x = 0
    · simp [hD_def, h]
    · simp only [hD_def, h, ite_false]
      have : fderiv ℝ W x (abcField x) = 0 := by
        rw [← InnerProductSpace.toDual_symm_apply, real_inner_comm]; exact hfx
      simp [this]; ring
  calc ∫ x in cell 3 p, abcField x j * W x = ∫ x in cell 3 p, D x (abcField x) :=
        integral_congr_ae (ae_restrict_of_ae (hint.mono fun x hx => hx.symm))
    _ = 0 := integral_fderiv_abcField_eq_zero hFl hFp hD


/-- A tube supported where `V_z ≥ c₀ > 0` has positive `z`-drift. -/
private lemma integral_abcField_two_mul_pos {W : E 3 → ℝ} (hWc : Continuous W)
    (hWp : Periodic (2 * Real.pi) W) (hW0 : ∀ x, 0 ≤ W x) {x₀ : E 3} (hx₀ : W x₀ ≠ 0)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hz : ∀ x, W x ≠ 0 → c₀ ≤ abcField x 2) :
    0 < ∫ x in cell 3 (2 * Real.pi), abcField x 2 * W x := by
  set p := 2 * Real.pi with hp_def
  have hp : 0 < p := by positivity
  obtain ⟨x₁, hx₁, hx₁eq⟩ := exists_cell_eq hp hWp x₀
  have hpos1 : 0 < W x₁ := lt_of_le_of_ne (hW0 _) (by rw [hx₁eq]; exact hx₀.symm)
  set v : E 3 := ev 0 + ev 1 + ev 2 with hv_def
  have hv : ∀ i, v i = 1 := by intro i; fin_cases i <;> simp [v]
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < W (x₁ + t • v) ∧ ∀ i, x₁ i + t < p := by
    refine Eventually.and ?_ ?_
    · have hc : Continuous fun t : ℝ => W (x₁ + t • v) := by fun_prop
      have := hc.continuousAt (x := 0) |>.eventually (lt_mem_nhds (by simpa using hpos1))
      exact nhdsWithin_le_nhds this
    · refine eventually_all.2 fun i => nhdsWithin_le_nhds ?_
      have : Tendsto (fun t : ℝ => x₁ i + t) (𝓝 0) (𝓝 (x₁ i)) := by
        simpa using (tendsto_const_nhds.add tendsto_id : Tendsto (fun t : ℝ => x₁ i + t) (𝓝 0)
          (𝓝 (x₁ i + 0)))
      exact this.eventually (eventually_lt_nhds (hx₁ i).2)
  obtain ⟨t, ⟨ht1, ht2⟩, ht0⟩ := (hev.and self_mem_nhdsWithin).exists
  set U : Set (E 3) := {x | ∀ i, x i ∈ Set.Ioo 0 p} ∩ {x | 0 < W x} with hU_def
  have hUo : IsOpen U := by
    refine IsOpen.inter ?_ (isOpen_lt continuous_const hWc)
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage (by fun_prop)
  have hx₂ : x₁ + t • v ∈ U := by
    refine ⟨fun i => ?_, ht1⟩
    have h0 := (hx₁ i).1
    have : (x₁ + t • v) i = x₁ i + t := by simp [hv]
    rw [this]
    exact ⟨by linarith [show (0:ℝ) < t from ht0], ht2 i⟩
  have hUpos : 0 < volume U := hUo.measure_pos volume ⟨_, hx₂⟩
  have hnn : ∀ x, 0 ≤ abcField x 2 * W x := by
    intro x
    by_cases h : W x = 0
    · simp [h]
    · exact mul_nonneg (hc₀.le.trans (hz x h)) (hW0 x)
  have hsub : U ⊆ Function.support (fun x => abcField x 2 * W x) ∩ cell 3 p := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨?_, fun i => Set.Ioo_subset_Ico_self (hx1 i)⟩
    exact mul_ne_zero (lt_of_lt_of_le hc₀ (hz x hx2.ne')).ne' hx2.ne'
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Eventually.of_forall hnn)
    (integrableOn_cell _ ((continuous_abcField_apply 2).mul hWc))]
  exact lt_of_lt_of_le hUpos (measure_mono hsub)

/-- A tube's first integral has zero drift in `x` and `y` and positive
drift in `z`, averaged over the period cell. -/
theorem tube_averages {W : E 3 → ℝ} (hW : VortexTube W) :
    ∫ x in cell 3 (2 * Real.pi), abcField x 0 * W x = 0 ∧
      ∫ x in cell 3 (2 * Real.pi), abcField x 1 * W x = 0 ∧
      0 < ∫ x in cell 3 (2 * Real.pi), abcField x 2 * W x := by
  obtain ⟨⟨C, hC⟩, hper, hnn, ⟨x₀, hx₀⟩, hflow, ⟨c₀, hc₀, hz⟩, a, b, δ, hδ, hband⟩ := hW
  refine ⟨?_, ?_, integral_abcField_two_mul_pos hC.continuous hper hnn hx₀ hc₀ hz⟩
  · exact integral_abcField_mul_eq_zero hC hper hnn hflow 0 a δ hδ fun x hx =>
      let ⟨m, _, h, _⟩ := hband x hx; ⟨m, h⟩
  · exact integral_abcField_mul_eq_zero hC hper hnn hflow 1 b δ hδ fun x hx =>
      let ⟨_, k, _, h⟩ := hband x hx; ⟨k, h⟩

end ABC
