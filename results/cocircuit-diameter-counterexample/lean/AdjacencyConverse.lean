import SignComposition

namespace ADKZPricing
open Matrix Finset
noncomputable section

theorem rowValue_sub (A : Matrix (Fin 80) (Fin 41) ℚ) (v w : Fin 41 → ℝ) (i : Fin 80) :
    rowValue A (v - w) i = rowValue A v i - rowValue A w i := by
  simp [rowValue, mul_sub, Finset.sum_sub_distrib]

theorem uniform_annihilate_41 (A : Matrix (Fin 80) (Fin 41) ℚ) (hu : Uniform A)
    (J : Finset (Fin 80)) (hc : 41 ≤ J.card) (w : Fin 41 → ℝ)
    (hz : ∀ i ∈ J, rowValue A w i = 0) : w = 0 := by
  by_contra hn
  have hb := rational_uniform_zero_count A hu w hn
  have hsub : J ⊆ univ.filter (fun i => (∑ j, (A i j : ℝ) * w j) = 0) := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _, hz i hi⟩
  have hcard := card_le_card hsub
  omega

theorem nonnegative_ray_signs (A : Matrix (Fin 80) (Fin 41) ℚ)
    (v w : Fin 41 → ℝ) (c : ℝ) (hc : 0 ≤ c) (he : v = c • w)
    (hn : signsOf A v ≠ 0) : signsOf A v = signsOf A w := by
  have hp : 0 < c := lt_of_le_of_ne hc (by
    intro hz
    apply hn
    ext i
    simp [signsOf, rowValue, he, ← hz, realSign])
  ext i
  change realSign (rowValue A v i) = realSign (rowValue A w i)
  rw [he, rowValue_smul, realSign_pos_scale _ _ hp]

/-- A composition face with 39 zeros contains only its two given
    cocircuits. Uniformity forces every other representative into their
    span, and sign feasibility forces nonnegative coefficients. -/
theorem composition_39_only_endpoints (A : Matrix (Fin 80) (Fin 41) ℚ)
    (hu : Uniform A) (X Y : SignVector) (hx : Cocircuit A X) (hy : Cocircuit A Y)
    (hcomm : compose X Y = compose Y X) (hcard : (signZeros (compose X Y)).card = 39)
    (Z : SignVector) (hz : Cocircuit A Z) (hf : FaceLE Z (compose X Y)) : Z = X ∨ Z = Y := by
  classical
  let T := compose X Y
  let J := signZeros T
  have hJcard : J.card = 39 := hcard
  have hxcard : (signZeros X).card = 40 := uniform_cocircuit_zero_count A hu X hx
  have hycard : (signZeros Y).card = 40 := uniform_cocircuit_zero_count A hu Y hy
  have hzcard : (signZeros Z).card = 40 := uniform_cocircuit_zero_count A hu Z hz
  obtain ⟨i, hix, hiT⟩ := exists_mem_not_mem_of_card_lt_card (show J.card < (signZeros X).card by omega)
  obtain ⟨j, hjy, hjT⟩ := exists_mem_not_mem_of_card_lt_card (show J.card < (signZeros Y).card by omega)
  have hxi : X i = 0 := (mem_filter.mp hix).2
  have hyj : Y j = 0 := (mem_filter.mp hjy).2
  have hTi : T i ≠ 0 := by simpa [J, signZeros] using hiT
  have hTj : T j ≠ 0 := by simpa [J, signZeros] using hjT
  have hyi : Y i ≠ 0 := by simpa [T, compose, hxi] using hTi
  have hxj : X j ≠ 0 := by
    intro hzero
    exact hTj ((compose_zero_iff X Y j).mpr ⟨hzero, hyj⟩)
  have hij : i ≠ j := by intro he; subst j; exact hxj hxi
  obtain ⟨x, hxr⟩ := hx.1
  obtain ⟨y, hyr⟩ := hy.1
  obtain ⟨z, hzr⟩ := hz.1
  have hx' : signsOf A x = X := funext (fun k => (hxr k).symm)
  have hy' : signsOf A y = Y := funext (fun k => (hyr k).symm)
  have hz' : signsOf A z = Z := funext (fun k => (hzr k).symm)
  have hxi0 : rowValue A x i = 0 := (realSign_zero_iff _).mp ((hxr i).symm.trans hxi)
  have hyj0 : rowValue A y j = 0 := (realSign_zero_iff _).mp ((hyr j).symm.trans hyj)
  have hyi0 : rowValue A y i ≠ 0 := by
    intro he
    exact hyi ((hyr i).trans ((realSign_zero_iff _).mpr he))
  have hxj0 : rowValue A x j ≠ 0 := by
    intro he
    exact hxj ((hxr j).trans ((realSign_zero_iff _).mpr he))
  let a := rowValue A z j / rowValue A x j
  let b := rowValue A z i / rowValue A y i
  have hTf_j : T j = X j := by simp [T, compose, hxj]
  have hTf_i : T i = Y i := by simp [T, compose, hxi]
  have ha : 0 ≤ a := compatible_ratio_nonnegative _ _ (by
    have h := hf j
    rw [show compose X Y j = X j from hTf_j, hzr j, hxr j] at h
    exact h)
  have hb : 0 ≤ b := compatible_ratio_nonnegative _ _ (by
    have h := hf i
    rw [show compose X Y i = Y i from hTf_i, hzr i, hyr i] at h
    exact h)
  let q := z - (a • x + b • y)
  have hq (k : Fin 80) : rowValue A q k = rowValue A z k -
      (a * rowValue A x k + b * rowValue A y k) := by
    rw [rowValue_sub, rowValue_add, rowValue_smul, rowValue_smul]
  have hqJ : ∀ k ∈ J, rowValue A q k = 0 := by
    intro k hk
    have hTk : T k = 0 := (mem_filter.mp hk).2
    have hXY := (compose_zero_iff X Y k).mp hTk
    have hZk : Z k = 0 := (hf k).elim id (fun h => h.trans hTk)
    have hz0 : rowValue A z k = 0 := (realSign_zero_iff _).mp ((hzr k).symm.trans hZk)
    have hx0 : rowValue A x k = 0 := (realSign_zero_iff _).mp ((hxr k).symm.trans hXY.1)
    have hy0 : rowValue A y k = 0 := (realSign_zero_iff _).mp ((hyr k).symm.trans hXY.2)
    rw [hq, hz0, hx0, hy0]
    ring
  have hqi : rowValue A q i = 0 := by
    rw [hq, hxi0]
    dsimp only [b]
    field_simp
  have hqj : rowValue A q j = 0 := by
    rw [hq, hyj0]
    dsimp only [a]
    field_simp
  have hq0 : q = 0 := by
    refine uniform_annihilate_41 A hu (insert i (insert j J)) ?_ q ?_
    · simp [card_insert_of_not_mem, hiT, hjT, hij, show J.card = 39 from hcard]
    · intro k hk
      rcases mem_insert.mp hk with rfl | hk
      · exact hqi
      rcases mem_insert.mp hk with rfl | hk
      · exact hqj
      · exact hqJ k hk
  have hdecomp : z = a • x + b • y := sub_eq_zero.mp hq0
  obtain ⟨k, hkZ, hkT⟩ := exists_mem_not_mem_of_card_lt_card
    (show J.card < (signZeros Z).card by omega)
  have hZk : Z k = 0 := (mem_filter.mp hkZ).2
  have hTk : T k ≠ 0 := by simpa [J, signZeros] using hkT
  have hsT : (T k : ℝ) ≠ 0 := by exact_mod_cast hTk
  have hpx : 0 ≤ (T k : ℝ) * rowValue A x k := by
    have hfX := face_left_compose X Y k
    by_cases hzero : X k = 0
    · have hx0 : rowValue A x k = 0 := (realSign_zero_iff _).mp ((hxr k).symm.trans hzero)
      rw [hx0, mul_zero]
    · have he : X k = T k := hfX.resolve_left hzero
      rw [← he, hxr k]
      exact realSign_signed_nonnegative _
  have hpy : 0 ≤ (T k : ℝ) * rowValue A y k := by
    have hfY := face_right_compose hcomm k
    by_cases hzero : Y k = 0
    · have hy0 : rowValue A y k = 0 := (realSign_zero_iff _).mp ((hyr k).symm.trans hzero)
      rw [hy0, mul_zero]
    · have he : Y k = T k := hfY.resolve_left hzero
      rw [← he, hyr k]
      exact realSign_signed_nonnegative _
  have hsum : a * ((T k : ℝ) * rowValue A x k) + b * ((T k : ℝ) * rowValue A y k) = 0 := by
    have he := congrArg (fun v => rowValue A v k) hdecomp
    dsimp only at he
    have hz0 : rowValue A z k = 0 := (realSign_zero_iff _).mp ((hzr k).symm.trans hZk)
    rw [rowValue_add, rowValue_smul, rowValue_smul, hz0] at he
    calc
      a * ((T k : ℝ) * rowValue A x k) + b * ((T k : ℝ) * rowValue A y k) =
          (T k : ℝ) * (a * rowValue A x k + b * rowValue A y k) := by ring
      _ = 0 := by rw [← he, mul_zero]
  have hab : a = 0 ∨ b = 0 := by
    by_cases ha0 : a = 0
    · exact Or.inl ha0
    by_cases hb0 : b = 0
    · exact Or.inr hb0
    exfalso
    have hax : a * ((T k : ℝ) * rowValue A x k) = 0 := by
      have hp := mul_nonneg ha hpx
      have hq := mul_nonneg hb hpy
      linarith
    have hby : b * ((T k : ℝ) * rowValue A y k) = 0 := by linarith
    have hx0 := (mul_eq_zero.mp ((mul_eq_zero.mp hax).resolve_left ha0)).resolve_left hsT
    have hy0 := (mul_eq_zero.mp ((mul_eq_zero.mp hby).resolve_left hb0)).resolve_left hsT
    exact hTk ((compose_zero_iff X Y k).mpr
      ⟨(hxr k).trans ((realSign_zero_iff _).mpr hx0),
        (hyr k).trans ((realSign_zero_iff _).mpr hy0)⟩)
  have hzn : signsOf A z ≠ 0 := by simpa only [hz'] using hz.2.1
  rcases hab with ha0 | hb0
  · right
    have he := nonnegative_ray_signs A z y b hb (by simpa [ha0] using hdecomp) hzn
    simpa only [hz', hy'] using he
  · left
    have he := nonnegative_ray_signs A z x a ha (by simpa [hb0] using hdecomp) hzn
    simpa only [hz', hx'] using he

/-- Exact faithful adjacency criterion, derived from the frozen
    composition/face definition for this uniform realizable endpoint. -/
theorem uniform_adjacency_iff (A : Matrix (Fin 80) (Fin 41) ℚ) (hu : Uniform A)
    (X Y : SignVector) (hx : Cocircuit A X) (hy : Cocircuit A Y) :
    Adjacent A X Y ↔ X ≠ Y ∧ compose X Y = compose Y X ∧
      (signZeros (compose X Y)).card = 39 := by
  constructor
  · intro h
    exact ⟨h.2.2.1, h.2.2.2.1, adjacent_composition_zero_count A hu X Y h⟩
  · rintro ⟨hne, hcomm, hcard⟩
    exact ⟨hx, hy, hne, hcomm, covector_commuting_compose A X Y hx.1 hy.1 hcomm,
      composition_39_only_endpoints A hu X Y hx hy hcomm hcard⟩

#print axioms composition_39_only_endpoints
#print axioms uniform_adjacency_iff
end
end ADKZPricing
