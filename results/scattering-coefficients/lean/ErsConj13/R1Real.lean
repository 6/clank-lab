import ErsConj13.R1Consistent

/-!
# Realization: limits of ordered products as Poisson automorphisms with the filtration
-/

noncomputable section

namespace ErsConj13.Scat

open MvPowerSeries

/-! ## Walls on one ray compose multiplicatively -/

lemma subst_rayMono_wall (s : Slope) {F : PowerSeries ℚ} (hF : PowerSeries.constantCoeff F = 1) :
    subst (wv s F) (rayMono s) = rayMono s := by
  have hFc := (ord_rayEval_sub_one s hF).mono (rlen_pos s)
  have hP : rayEval s F ^ (ray s).1 * (rayEval s F ^ (ray s).1)⁻¹ = 1 :=
    mul_inv_of_cc (ord_pow_sub_one hFc _)
  rw [rayMono_eq, subst_monomial' _ (subVec_wv s F), monomial_eq_XX]
  simp only [wv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, rvec,
    Finsupp.add_apply, Finsupp.single_eq_same]
  simp
  have : (rayEval s F ^ (ray s).1)⁻¹ ^ (ray s).2 * rayEval s F ^ ((ray s).2 * (ray s).1) = 1 := by
    rw [mul_comm ((ray s).2), pow_mul, ← mul_pow, mul_comm, hP, one_pow]
  linear_combination (X 0 ^ (ray s).1 * X 1 ^ (ray s).2) * this

lemma subst_rayEval_wall (s : Slope) {F : PowerSeries ℚ} (hF : PowerSeries.constantCoeff F = 1)
    (G : PowerSeries ℚ) : subst (wv s F) (rayEval s G) = rayEval s G := by
  rw [rayEval, PowerSeries.subst_def, subst_comp_subst_apply (hasSubst_rayMono s).const
    (subVec_wv s F).hasSubst, subst_rayMono_wall s hF]

lemma wall_mul_same (s : Slope) {F G : PowerSeries ℚ} (hF : PowerSeries.constantCoeff F = 1)
    (hG : PowerSeries.constantCoeff G = 1) (h : B) :
    wall s (F * G) h = wall s F (wall s G h) := by
  have sF := subVec_wv s F
  simp only [wall_eq]
  rw [subst_comp_subst_apply (subVec_wv s G).hasSubst sF.hasSubst]
  congr 1
  have hFc := (ord_rayEval_sub_one s hF).mono (rlen_pos s)
  have hGc := (ord_rayEval_sub_one s hG).mono (rlen_pos s)
  have ccG : constantCoeff (rayEval s G ^ (ray s).1) ≠ 0 := by
    have := ord_one_iff.mp (ord_pow_sub_one hGc (ray s).1)
    rw [map_sub, map_one, sub_eq_zero] at this; rw [this]; norm_num
  funext i; fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]
    have e0 : ∀ K : PowerSeries ℚ, wv s K 0 = X 0 * rayEval s K ^ (ray s).2 := fun K => rfl
    rw [e0 G, e0 (F * G), subst_mul sF.hasSubst, subst_pow sF.hasSubst, subst_X' _ sF,
      subst_rayEval_wall s hF, e0 F, rayEval_mul, mul_pow]
    ring
  · simp only [Fin.mk_one, Fin.isValue]
    have e1 : ∀ K : PowerSeries ℚ, wv s K 1 = X 1 * (rayEval s K ^ (ray s).1)⁻¹ := fun K => rfl
    rw [e1 G, e1 (F * G), subst_mul sF.hasSubst, subst_X' _ sF, subst_inv' sF.hasSubst ccG,
      subst_pow sF.hasSubst, subst_rayEval_wall s hF, e1 F, rayEval_mul, mul_pow,
      inv_mul_of_cc (ord_pow_sub_one hFc _) (ord_pow_sub_one hGc _)]
    ring

lemma ps_inv_cc {F : PowerSeries ℚ} (hF : PowerSeries.constantCoeff F = 1) :
    PowerSeries.constantCoeff F⁻¹ = 1 := by
  have h := PowerSeries.mul_inv_cancel F (by rw [hF]; norm_num)
  have := congrArg PowerSeries.constantCoeff h
  rw [map_mul, hF, one_mul, map_one] at this; exact this

lemma wall_inv_left (s : Slope) {F : PowerSeries ℚ} (hF : PowerSeries.constantCoeff F = 1)
    (h : B) : wall s F⁻¹ (wall s F h) = h := by
  rw [← wall_mul_same s (ps_inv_cc hF) hF, PowerSeries.inv_mul_cancel _ (by rw [hF]; norm_num),
    wall_one]

lemma wall_inv_right (s : Slope) {F : PowerSeries ℚ} (hF : PowerSeries.constantCoeff F = 1)
    (h : B) : wall s F (wall s F⁻¹ h) = h := by
  rw [← wall_mul_same s hF (ps_inv_cc hF), PowerSeries.mul_inv_cancel _ (by rw [hF]; norm_num),
    wall_one]


/-! ## Level-wise list sequences and limits -/

/-- A level-wise sequence of lists: level `N` is level `M ≥ N` filtered to `|r| < N`. -/
def IsLevelwise (LS : ℕ → List Slope) : Prop :=
  ∀ N M, N ≤ M → (LS M).filter (fun s => decide (rlen s < N)) = LS N

lemma levelwise_sort : IsLevelwise fun N => (slopesBelow N).sort (· ≤ ·) :=
  fun _ _ h => sort_filter_slopesBelow h

lemma levelwise_rev : IsLevelwise fun N => ((slopesBelow N).sort (· ≤ ·)).reverse := by
  intro N M h
  simp only [List.filter_reverse, sort_filter_slopesBelow h]

lemma prodL_stab_gen {f : Slope → PowerSeries ℚ} (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1)
    {LS : ℕ → List Slope} (hLS : IsLevelwise LS) {N M : ℕ} (hNM : N ≤ M) {h : B} (hh : Ord 1 h) :
    EqMod N (prodL f (LS M) h) (prodL f (LS N) h) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; intro e he; omega
  set f' : Slope → PowerSeries ℚ := fun s => if rlen s < N then f s else 1 with hf'def
  have hf' : ∀ s, PowerSeries.constantCoeff (f' s) = 1 := fun s => by
    rw [hf'def]; dsimp only; split_ifs
    · exact hf s
    · simp
  have hag : Agree N f f' := by
    intro s j hj
    rw [hf'def]; dsimp only
    split_ifs with h
    · rfl
    · have : j = 0 := by
        by_contra hj0; have : rlen s ≤ j * rlen s := Nat.le_mul_of_pos_left _ (by omega)
        omega
      subst this
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hf s]; simp
  have h1 := prodL_weak_pert hf hf' hN hag (LS M) hh
  have h2 : prodL f' (LS M) h = prodL f (LS N) h := by
    rw [prodL_filter f f' (fun s => decide (rlen s < N))
      (fun s hs => by rw [hf'def]; dsimp only; rw [if_pos (of_decide_eq_true hs)])
      (fun s hs => by rw [hf'def]; dsimp only; rw [if_neg (of_decide_eq_false hs)]),
      hLS N M hNM]
  rw [← h2]
  exact h1.mono' (by omega)

/-- The limit of the level-wise products on the generators. -/
def limV (f : Slope → PowerSeries ℚ) (LS : ℕ → List Slope) (i : Fin 2) : B :=
  fun e => coeff e (prodL f (LS (e.degree + 1)) (X i))

lemma limV_eqMod {f : Slope → PowerSeries ℚ} (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1)
    {LS : ℕ → List Slope} (hLS : IsLevelwise LS) (i : Fin 2) (N : ℕ) :
    EqMod N (limV f LS i) (prodL f (LS N) (X i)) := by
  intro e he
  have h := prodL_stab_gen hf hLS (show e.degree + 1 ≤ N by rw [degree_fin2]; omega) (ord_X i)
  have := h e (by rw [← degree_fin2]; omega)
  exact this.symm

lemma limV_subVec {f : Slope → PowerSeries ℚ} (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1)
    {LS : ℕ → List Slope} (hLS : IsLevelwise LS) : SubVec (limV f LS) := by
  intro i
  have h := eqMod_iff.mp (limV_eqMod hf hLS i 1)
  obtain ⟨b, -, e⟩ := prodL_unip hf (LS 1) i
  rw [e] at h
  have := h.add ((ord_X i).mul_right (1 + b))
  simpa using this

/-! ## Inverses of finite products -/

/-- The family of inverse ray functions. -/
def invFam (f : Slope → PowerSeries ℚ) (s : Slope) : PowerSeries ℚ := (f s)⁻¹

lemma invFam_cc {f : Slope → PowerSeries ℚ} (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1)
    (s : Slope) : PowerSeries.constantCoeff (invFam f s) = 1 := ps_inv_cc (hf s)

lemma prodL_inv_right {f : Slope → PowerSeries ℚ} (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1)
    (L : List Slope) (h : B) : prodL f L (prodL (invFam f) L.reverse h) = h := by
  induction L generalizing h with
  | nil => rw [List.reverse_nil, prodL_nil, prodL_nil]
  | cons s L ih =>
    rw [List.reverse_cons, prodL_append, prodL_cons, prodL_cons, prodL_nil, ih]
    exact wall_inv_right s (hf s) h

lemma prodL_inv_left {f : Slope → PowerSeries ℚ} (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1)
    (L : List Slope) (h : B) : prodL (invFam f) L.reverse (prodL f L h) = h := by
  induction L generalizing h with
  | nil => rw [List.reverse_nil, prodL_nil, prodL_nil]
  | cons s L ih =>
    rw [List.reverse_cons, prodL_append, prodL_cons, prodL_cons, prodL_nil]
    show prodL (invFam f) L.reverse (wall s (f s)⁻¹ (wall s (f s) (prodL f L h))) = h
    rw [wall_inv_left s (hf s), ih]


/-! ## The limit automorphism -/

/-- The ascending level-wise lists and their reverses. -/
abbrev LSa : ℕ → List Slope := fun N => (slopesBelow N).sort (· ≤ ·)
abbrev LSr : ℕ → List Slope := fun N => ((slopesBelow N).sort (· ≤ ·)).reverse

lemma subst_limV_eqMod {f : Slope → PowerSeries ℚ} (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1)
    {LS : ℕ → List Slope} (hLS : IsLevelwise LS) (N : ℕ) (g : B) :
    EqMod N (subst (limV f LS) g) (prodL f (LS N) g) := by
  have hv : SubVec (fun j => prodL f (LS N) (X j)) := fun j => by
    obtain ⟨b, -, e⟩ := prodL_unip hf (LS N) j
    beta_reduce; rw [e]; exact (ord_X j).mul_right _
  rw [prodL_eq_subst hf]
  exact subst_congr_vec g (limV_subVec hf hLS) hv (fun j => limV_eqMod hf hLS j N)

lemma limV_inv_right {f : Slope → PowerSeries ℚ} (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1)
    (i : Fin 2) : subst (limV f LSa) (limV (invFam f) LSr i) = X i := by
  apply sub_eq_zero.mp
  apply eq_zero_of_ord_all
  intro N
  rw [← eqMod_iff]
  have h1 := subst_congr_arg (limV_eqMod (invFam_cc hf) levelwise_rev i N) (limV_subVec hf levelwise_sort)
  have h2 := subst_limV_eqMod hf levelwise_sort N (prodL (invFam f) (LSr N) (X i))
  have h3 := prodL_inv_right hf (LSa N) (X i)
  rw [show LSr N = (LSa N).reverse from rfl, h3] at h2
  exact h1.trans' h2

lemma limV_inv_left {f : Slope → PowerSeries ℚ} (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1)
    (i : Fin 2) : subst (limV (invFam f) LSr) (limV f LSa i) = X i := by
  apply sub_eq_zero.mp
  apply eq_zero_of_ord_all
  intro N
  rw [← eqMod_iff]
  have h1 := subst_congr_arg (limV_eqMod hf levelwise_sort i N)
    (limV_subVec (invFam_cc hf) levelwise_rev)
  have h2 := subst_limV_eqMod (invFam_cc hf) levelwise_rev N (prodL f (LSa N) (X i))
  have h3 : prodL (invFam f) ((slopesBelow N).sort (· ≤ ·)).reverse (prodL f (LSa N) (X i)) = X i :=
    prodL_inv_left hf (LSa N) (X i)
  rw [h3] at h2
  exact h1.trans' h2

/-- The limit of the ascending products of a family, as a ring automorphism. -/
def limEquiv (f : Slope → PowerSeries ℚ) (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1) :
    B ≃+* B :=
  ErsConj13.substEquiv (limV f LSa) (limV (invFam f) LSr)
    (fun i => ord_one_iff.mp (limV_subVec hf levelwise_sort i))
    (fun i => ord_one_iff.mp (limV_subVec (invFam_cc hf) levelwise_rev i))
    (limV_inv_right hf) (limV_inv_left hf)

lemma limEquiv_apply (f : Slope → PowerSeries ℚ) (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1)
    (g : B) : limEquiv f hf g = subst (limV f LSa) g := rfl

lemma limEquiv_symm_apply (f : Slope → PowerSeries ℚ)
    (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1) (g : B) :
    (limEquiv f hf).symm g = subst (limV (invFam f) LSr) g := rfl

lemma eqMod_bracket {N : ℕ} {a a' b b' : B} (ha : EqMod N a a') (hb : EqMod N b b') :
    EqMod N (ErsConj13.bracket a b) (ErsConj13.bracket a' b') := by
  rw [eqMod_iff] at *
  have e : ErsConj13.bracket a b - ErsConj13.bracket a' b' =
      ErsConj13.bracket (a - a') b + ErsConj13.bracket a' (b - b') := by
    rw [bracket_sub_left', bracket_sub_right']; ring
  rw [e]; exact (ord_bracket_left ha _).add (ord_bracket_right _ hb)

lemma limEquiv_poisson (f : Slope → PowerSeries ℚ) (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1)
    (a b : B) : limEquiv f hf (ErsConj13.bracket a b) =
      ErsConj13.bracket (limEquiv f hf a) (limEquiv f hf b) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_ord_all
  intro N
  rw [← eqMod_iff, limEquiv_apply, limEquiv_apply, limEquiv_apply]
  have h1 := subst_limV_eqMod hf levelwise_sort N (ErsConj13.bracket a b)
  rw [prodL_bracket hf] at h1
  exact h1.trans' (eqMod_bracket (subst_limV_eqMod hf levelwise_sort N a)
    (subst_limV_eqMod hf levelwise_sort N b)).symm'

/-! ## The h-filtration for products and limits -/

open ErsConj13 (OGe OLe hdeg zero_mem_OGe zero_mem_OLe oneGe_pow oneLe_pow OGe_add OLe_add OGe_mul OLe_mul OGe_mono OLe_mono oneGe_mul oneLe_mul inv_mem_OGe inv_mem_OLe)

/-- `c ∈ 1 + 𝒪`: -/
lemma OGe_cmem {c : B} (hc : c - 1 ∈ OGe 1) : c ∈ OGe 0 := by
  have : c = 1 + (c - 1) := by ring
  rw [this]
  refine OGe_add ?_ (OGe_mono (by norm_num) hc)
  intro e he
  rw [MvPowerSeries.coeff_one] at he
  split_ifs at he with h
  · subst h; simp [hdeg]
  · exact absurd rfl he

lemma monomial_mem_OGe (v : Fin 2 →₀ ℕ) (c : ℚ) : (monomial v c : B) ∈ OGe (hdeg v) := by
  intro e he
  rw [coeff_monomial] at he
  split_ifs at he with h
  · subst h; exact le_rfl
  · exact absurd rfl he

lemma sum_mem_OGe {ι : Type*} (s : Finset ι) {k : ℤ} (g : ι → B) (h : ∀ i ∈ s, g i ∈ OGe k) :
    (∑ i ∈ s, g i) ∈ OGe k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_mem_OGe k
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact OGe_add (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Substitutions `X i ↦ X i · c i` with `c i ∈ 1 + 𝒪` preserve each `𝒪_k`. -/
lemma subst_mem_OGe {a : Fin 2 → B} (ha : ∀ i, ∃ c, c - 1 ∈ OGe 1 ∧ a i = X i * c)
    {k : ℤ} {f : B} (hf : f ∈ OGe k) : subst a f ∈ OGe k := by
  classical
  have hsv : SubVec a := fun i => by
    obtain ⟨c, -, e⟩ := ha i; rw [e]; exact (ord_X i).mul_right _
  intro e he
  set K := e.degree + 1
  have ht := truncTotal_subst_eq_truncTotal_truncTotal_subst (k := K) (f := f)
    (fun i => ord_one_iff.mp (hsv i))
  have hce : coeff e (subst a f) = coeff e (subst a ((truncTotal K f : MvPolynomial (Fin 2) ℚ) : B)) := by
    have := congrArg (MvPolynomial.coeff e) ht
    rwa [coeff_truncTotal _ (by simp [K]), coeff_truncTotal _ (by simp [K])] at this
  rw [hce] at he
  revert he
  apply (show subst a ((truncTotal K f : MvPolynomial (Fin 2) ℚ) : B) ∈ OGe k from ?_) e
  rw [poly_as_sum, subst_sum' hsv]
  refine sum_mem_OGe _ _ fun v hv => ?_
  rw [subst_monomial' a hsv]
  have hcv : MvPolynomial.coeff v (truncTotal K f) ≠ 0 := MvPolynomial.mem_support_iff.mp hv
  have hvk : k ≤ hdeg v := by
    have : coeff v f ≠ 0 := by
      intro h0; apply hcv; rw [coeff_truncTotal_eq_ite]; split_ifs <;> simp [h0]
    exact hf v this
  obtain ⟨c0, hc0, e0⟩ := ha 0
  obtain ⟨c1, hc1, e1⟩ := ha 1
  rw [e0, e1, mul_pow, mul_pow]
  have hX : X 0 ^ v 0 * X 1 ^ v 1 = (monomial v 1 : B) := by
    rw [monomial_eq_XX]; simp
  have hm : (X 0 ^ v 0 * c0 ^ v 0 * (X 1 ^ v 1 * c1 ^ v 1) : B) =
      (monomial v 1 : B) * (c0 ^ v 0 * c1 ^ v 1) := by rw [← hX]; ring
  rw [hm, MvPowerSeries.smul_eq_C_mul]
  have hcc : c0 ^ v 0 * c1 ^ v 1 ∈ OGe 0 := by
    have := OGe_mul (OGe_cmem (oneGe_pow hc0 (v 0)))
      (OGe_cmem (oneGe_pow hc1 (v 1)))
    simpa using this
  have hmon := OGe_mul (monomial_mem_OGe v (1 : ℚ)) hcc
  rw [add_zero] at hmon
  have hC : (C (MvPolynomial.coeff v (truncTotal K f)) : B) ∈ OGe 0 := by
    intro e' he'
    rw [coeff_C] at he'
    split_ifs at he' with h
    · subst h; simp [hdeg]
    · exact absurd rfl he'
  have := OGe_mul hC hmon
  rw [zero_add] at this
  exact OGe_mono hvk this

/-- `c ∈ 1 + 𝒪`: -/
lemma OLe_cmem {c : B} (hc : c - 1 ∈ OLe (-1)) : c ∈ OLe 0 := by
  have : c = 1 + (c - 1) := by ring
  rw [this]
  refine OLe_add ?_ (OLe_mono (by norm_num) hc)
  intro e he
  rw [MvPowerSeries.coeff_one] at he
  split_ifs at he with h
  · subst h; simp [hdeg]
  · exact absurd rfl he

lemma monomial_mem_OLe (v : Fin 2 →₀ ℕ) (c : ℚ) : (monomial v c : B) ∈ OLe (hdeg v) := by
  intro e he
  rw [coeff_monomial] at he
  split_ifs at he with h
  · subst h; exact le_rfl
  · exact absurd rfl he

lemma sum_mem_OLe {ι : Type*} (s : Finset ι) {k : ℤ} (g : ι → B) (h : ∀ i ∈ s, g i ∈ OLe k) :
    (∑ i ∈ s, g i) ∈ OLe k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_mem_OLe k
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact OLe_add (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Substitutions `X i ↦ X i · c i` with `c i ∈ 1 + 𝒪` preserve each `𝒪_k`. -/
lemma subst_mem_OLe {a : Fin 2 → B} (ha : ∀ i, ∃ c, c - 1 ∈ OLe (-1) ∧ a i = X i * c)
    {k : ℤ} {f : B} (hf : f ∈ OLe k) : subst a f ∈ OLe k := by
  classical
  have hsv : SubVec a := fun i => by
    obtain ⟨c, -, e⟩ := ha i; rw [e]; exact (ord_X i).mul_right _
  intro e he
  set K := e.degree + 1
  have ht := truncTotal_subst_eq_truncTotal_truncTotal_subst (k := K) (f := f)
    (fun i => ord_one_iff.mp (hsv i))
  have hce : coeff e (subst a f) = coeff e (subst a ((truncTotal K f : MvPolynomial (Fin 2) ℚ) : B)) := by
    have := congrArg (MvPolynomial.coeff e) ht
    rwa [coeff_truncTotal _ (by simp [K]), coeff_truncTotal _ (by simp [K])] at this
  rw [hce] at he
  revert he
  apply (show subst a ((truncTotal K f : MvPolynomial (Fin 2) ℚ) : B) ∈ OLe k from ?_) e
  rw [poly_as_sum, subst_sum' hsv]
  refine sum_mem_OLe _ _ fun v hv => ?_
  rw [subst_monomial' a hsv]
  have hcv : MvPolynomial.coeff v (truncTotal K f) ≠ 0 := MvPolynomial.mem_support_iff.mp hv
  have hvk : hdeg v ≤ k := by
    have : coeff v f ≠ 0 := by
      intro h0; apply hcv; rw [coeff_truncTotal_eq_ite]; split_ifs <;> simp [h0]
    exact hf v this
  obtain ⟨c0, hc0, e0⟩ := ha 0
  obtain ⟨c1, hc1, e1⟩ := ha 1
  rw [e0, e1, mul_pow, mul_pow]
  have hX : X 0 ^ v 0 * X 1 ^ v 1 = (monomial v 1 : B) := by
    rw [monomial_eq_XX]; simp
  have hm : (X 0 ^ v 0 * c0 ^ v 0 * (X 1 ^ v 1 * c1 ^ v 1) : B) =
      (monomial v 1 : B) * (c0 ^ v 0 * c1 ^ v 1) := by rw [← hX]; ring
  rw [hm, MvPowerSeries.smul_eq_C_mul]
  have hcc : c0 ^ v 0 * c1 ^ v 1 ∈ OLe 0 := by
    have := OLe_mul (OLe_cmem (oneLe_pow hc0 (v 0)))
      (OLe_cmem (oneLe_pow hc1 (v 1)))
    simpa using this
  have hmon := OLe_mul (monomial_mem_OLe v (1 : ℚ)) hcc
  rw [add_zero] at hmon
  have hC : (C (MvPolynomial.coeff v (truncTotal K f)) : B) ∈ OLe 0 := by
    intro e' he'
    rw [coeff_C] at he'
    split_ifs at he' with h
    · subst h; simp [hdeg]
    · exact absurd rfl he'
  have := OLe_mul hC hmon
  rw [zero_add] at this
  exact OLe_mono hvk this

lemma rayEval_mem_OGe (s : Slope) (hs : (ray s).1 < (ray s).2) {F : PowerSeries ℚ}
    (hF : PowerSeries.constantCoeff F = 1) : rayEval s F - 1 ∈ OGe 1 := by
  classical
  intro e he
  rw [map_sub, coeff_rayEval, coeff_one] at he
  split_ifs at he with h1 h2
  · exfalso; apply he
    have hc := h1.choose_spec
    have h0 : (0 : ℕ) • rvec s = h1.choose • rvec s := by rw [zero_smul]; exact h2 ▸ hc
    have hz : h1.choose = 0 := (smul_rvec_inj h0).symm
    rw [hz, PowerSeries.coeff_zero_eq_constantCoeff_apply, hF, sub_self]
  · have hc := h1.choose_spec
    have hj : h1.choose ≠ 0 := by intro h; apply h2; rw [hc, h, zero_smul]
    rw [hc]
    simp only [hdeg, Finsupp.smul_apply, rvec_apply0, rvec_apply1, smul_eq_mul]
    push_cast
    have : (1 : ℤ) ≤ h1.choose := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
    have : (1 : ℤ) ≤ (ray s).2 - (ray s).1 := by omega
    nlinarith
  · exfalso; exact h1 ⟨0, by simp [*]⟩
  · exfalso; apply he; simp

lemma wv_mem_OGe (s : Slope) (hs : (ray s).1 < (ray s).2) {F : PowerSeries ℚ}
    (hF : PowerSeries.constantCoeff F = 1) :
    ∀ i, ∃ c, c - 1 ∈ OGe 1 ∧ wv s F i = X i * c := by
  have h1 := rayEval_mem_OGe s hs hF
  intro i; fin_cases i
  · exact ⟨rayEval s F ^ (ray s).2, oneGe_pow h1 _, rfl⟩
  · refine ⟨(rayEval s F ^ (ray s).1)⁻¹, ?_, rfl⟩
    have hp := oneGe_pow h1 (ray s).1
    refine inv_mem_OGe hp ?_
    rw [mul_comm]
    exact mul_inv_of_cc (ord_pow_sub_one ((ord_rayEval_sub_one s hF).mono (rlen_pos s)) _)

lemma wv_one_mem_OGe (s : Slope) : ∀ i, ∃ c, c - 1 ∈ OGe 1 ∧ wv s 1 i = X i * c :=
  fun i => ⟨1, by simpa using zero_mem_OGe 1, by rw [wv_one, mul_one]⟩

lemma prodL_mem_OGe {f : Slope → PowerSeries ℚ} (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1)
    (hsupp : ∀ s, (ray s).1 < (ray s).2 ∨ f s = 1) (L : List Slope) (i : Fin 2) :
    ∃ a ∈ OGe 1, prodL f L (X i) = X i * (1 + a) := by
  have hw : ∀ s, ∀ i, ∃ c, c - 1 ∈ OGe 1 ∧ wv s (f s) i = X i * c := fun s => by
    rcases hsupp s with h | h
    · exact wv_mem_OGe s h (hf s)
    · rw [h]; exact wv_one_mem_OGe s
  induction L with
  | nil => exact ⟨0, zero_mem_OGe _, by rw [prodL_nil]; ring⟩
  | cons s L ih =>
    obtain ⟨a, ha, e⟩ := ih
    obtain ⟨c, hc, ec⟩ := hw s i
    have hsv := subVec_wv s (f s)
    refine ⟨c * (1 + subst (wv s (f s)) a) - 1, ?_, ?_⟩
    · apply oneGe_mul hc
      simpa using subst_mem_OGe (hw s) ha
    · rw [prodL_cons, e, wall_eq, subst_mul hsv.hasSubst, subst_add hsv.hasSubst, subst_X' _ hsv,
        ec, show subst (wv s (f s)) (1 : B) = 1 from by simpa using subst_C' (wv s (f s)) 1]
      ring

/-- Limits of `X i (1 + 𝒪)`. -/
lemma lim_mem_OGe {v : B} (i : Fin 2) (h : ∀ N, ∃ a ∈ OGe 1, EqMod N v (X i * (1 + a))) :
    ∃ a ∈ OGe 1, v = X i * (1 + a) := by
  classical
  set a : B := fun e => coeff (Finsupp.single i 1 + e) v - (if e = 0 then 1 else 0) with hadef
  have hcoa : ∀ e, coeff e a = coeff (Finsupp.single i 1 + e) v - (if e = 0 then 1 else 0) :=
    fun e => rfl
  refine ⟨a, ?_, ?_⟩
  · intro e he
    obtain ⟨aN, haN, hN⟩ := h (e.degree + 2)
    have := hN (Finsupp.single i 1 + e) (by rw [← degree_fin2, map_add]; simp; omega)
    rw [coeff_X_mul_add] at this
    rw [hcoa, this, map_add, coeff_one] at he
    have : coeff e aN ≠ 0 := by intro h0; apply he; rw [h0]; split_ifs <;> simp
    exact haN e this
  · ext e
    rw [X_def, coeff_monomial_mul]
    split_ifs with hle
    · obtain ⟨e', rfl⟩ : ∃ e', e = Finsupp.single i 1 + e' := ⟨e - Finsupp.single i 1, by
        rw [add_tsub_cancel_of_le hle]⟩
      rw [add_tsub_cancel_left, one_mul, map_add, hcoa, coeff_one]
      split_ifs <;> ring
    · obtain ⟨aN, -, hN⟩ := h (e.degree + 1)
      rw [hN e (by rw [← degree_fin2]; omega), X_def, coeff_monomial_mul, if_neg hle]

lemma limV_mem_OGe {f : Slope → PowerSeries ℚ} (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1)
    (hsupp : ∀ s, (ray s).1 < (ray s).2 ∨ f s = 1) {LS : ℕ → List Slope} (hLS : IsLevelwise LS) (i : Fin 2) :
    ∃ a ∈ OGe 1, limV f LS i = X i * (1 + a) := by
  apply lim_mem_OGe i
  intro N
  obtain ⟨a, ha, e⟩ := prodL_mem_OGe hf hsupp (LS N) i
  exact ⟨a, ha, by rw [← e]; exact limV_eqMod hf hLS i N⟩

lemma subst_monomial_mem_OGe {v : Fin 2 → B} (hv : ∀ i, ∃ a ∈ OGe 1, v i = X i * (1 + a))
    (m : Fin 2 →₀ ℕ) : ∃ a ∈ OGe 1, subst v (monomial m 1 : B) = monomial m 1 * (1 + a) := by
  obtain ⟨a0, ha0, e0⟩ := hv 0
  obtain ⟨a1, ha1, e1⟩ := hv 1
  have hsv : SubVec v := fun i => by
    obtain ⟨a, -, e⟩ := hv i; rw [e]; exact (ord_X i).mul_right _
  refine ⟨(1 + a0) ^ m 0 * (1 + a1) ^ m 1 - 1, oneGe_mul (oneGe_pow (by simpa using ha0) _)
    (oneGe_pow (by simpa using ha1) _), ?_⟩
  rw [subst_monomial' v hsv, e0, e1, mul_pow, mul_pow, monomial_eq_XX, one_smul,
    map_one (C (σ := Fin 2) (R := ℚ))]
  ring

lemma rayEval_mem_OLe (s : Slope) (hs : (ray s).2 < (ray s).1) {F : PowerSeries ℚ}
    (hF : PowerSeries.constantCoeff F = 1) : rayEval s F - 1 ∈ OLe (-1) := by
  classical
  intro e he
  rw [map_sub, coeff_rayEval, coeff_one] at he
  split_ifs at he with h1 h2
  · exfalso; apply he
    have hc := h1.choose_spec
    have h0 : (0 : ℕ) • rvec s = h1.choose • rvec s := by rw [zero_smul]; exact h2 ▸ hc
    have hz : h1.choose = 0 := (smul_rvec_inj h0).symm
    rw [hz, PowerSeries.coeff_zero_eq_constantCoeff_apply, hF, sub_self]
  · have hc := h1.choose_spec
    have hj : h1.choose ≠ 0 := by intro h; apply h2; rw [hc, h, zero_smul]
    rw [hc]
    simp only [hdeg, Finsupp.smul_apply, rvec_apply0, rvec_apply1, smul_eq_mul]
    push_cast
    have : (1 : ℤ) ≤ h1.choose := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
    have : (ray s).2 - (ray s).1 ≤ (-1 : ℤ) := by omega
    nlinarith
  · exfalso; exact h1 ⟨0, by simp [*]⟩
  · exfalso; apply he; simp

lemma wv_mem_OLe (s : Slope) (hs : (ray s).2 < (ray s).1) {F : PowerSeries ℚ}
    (hF : PowerSeries.constantCoeff F = 1) :
    ∀ i, ∃ c, c - 1 ∈ OLe (-1) ∧ wv s F i = X i * c := by
  have h1 := rayEval_mem_OLe s hs hF
  intro i; fin_cases i
  · exact ⟨rayEval s F ^ (ray s).2, oneLe_pow h1 _, rfl⟩
  · refine ⟨(rayEval s F ^ (ray s).1)⁻¹, ?_, rfl⟩
    have hp := oneLe_pow h1 (ray s).1
    refine inv_mem_OLe hp ?_
    rw [mul_comm]
    exact mul_inv_of_cc (ord_pow_sub_one ((ord_rayEval_sub_one s hF).mono (rlen_pos s)) _)

lemma wv_one_mem_OLe (s : Slope) : ∀ i, ∃ c, c - 1 ∈ OLe (-1) ∧ wv s 1 i = X i * c :=
  fun i => ⟨1, by simpa using zero_mem_OLe (-1), by rw [wv_one, mul_one]⟩

lemma prodL_mem_OLe {f : Slope → PowerSeries ℚ} (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1)
    (hsupp : ∀ s, (ray s).2 < (ray s).1 ∨ f s = 1) (L : List Slope) (i : Fin 2) :
    ∃ a ∈ OLe (-1), prodL f L (X i) = X i * (1 + a) := by
  have hw : ∀ s, ∀ i, ∃ c, c - 1 ∈ OLe (-1) ∧ wv s (f s) i = X i * c := fun s => by
    rcases hsupp s with h | h
    · exact wv_mem_OLe s h (hf s)
    · rw [h]; exact wv_one_mem_OLe s
  induction L with
  | nil => exact ⟨0, zero_mem_OLe _, by rw [prodL_nil]; ring⟩
  | cons s L ih =>
    obtain ⟨a, ha, e⟩ := ih
    obtain ⟨c, hc, ec⟩ := hw s i
    have hsv := subVec_wv s (f s)
    refine ⟨c * (1 + subst (wv s (f s)) a) - 1, ?_, ?_⟩
    · apply oneLe_mul hc
      simpa using subst_mem_OLe (hw s) ha
    · rw [prodL_cons, e, wall_eq, subst_mul hsv.hasSubst, subst_add hsv.hasSubst, subst_X' _ hsv,
        ec, show subst (wv s (f s)) (1 : B) = 1 from by simpa using subst_C' (wv s (f s)) 1]
      ring

/-- Limits of `X i (1 + 𝒪)`. -/
lemma lim_mem_OLe {v : B} (i : Fin 2) (h : ∀ N, ∃ a ∈ OLe (-1), EqMod N v (X i * (1 + a))) :
    ∃ a ∈ OLe (-1), v = X i * (1 + a) := by
  classical
  set a : B := fun e => coeff (Finsupp.single i 1 + e) v - (if e = 0 then 1 else 0) with hadef
  have hcoa : ∀ e, coeff e a = coeff (Finsupp.single i 1 + e) v - (if e = 0 then 1 else 0) :=
    fun e => rfl
  refine ⟨a, ?_, ?_⟩
  · intro e he
    obtain ⟨aN, haN, hN⟩ := h (e.degree + 2)
    have := hN (Finsupp.single i 1 + e) (by rw [← degree_fin2, map_add]; simp; omega)
    rw [coeff_X_mul_add] at this
    rw [hcoa, this, map_add, coeff_one] at he
    have : coeff e aN ≠ 0 := by intro h0; apply he; rw [h0]; split_ifs <;> simp
    exact haN e this
  · ext e
    rw [X_def, coeff_monomial_mul]
    split_ifs with hle
    · obtain ⟨e', rfl⟩ : ∃ e', e = Finsupp.single i 1 + e' := ⟨e - Finsupp.single i 1, by
        rw [add_tsub_cancel_of_le hle]⟩
      rw [add_tsub_cancel_left, one_mul, map_add, hcoa, coeff_one]
      split_ifs <;> ring
    · obtain ⟨aN, -, hN⟩ := h (e.degree + 1)
      rw [hN e (by rw [← degree_fin2]; omega), X_def, coeff_monomial_mul, if_neg hle]

lemma limV_mem_OLe {f : Slope → PowerSeries ℚ} (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1)
    (hsupp : ∀ s, (ray s).2 < (ray s).1 ∨ f s = 1) {LS : ℕ → List Slope} (hLS : IsLevelwise LS) (i : Fin 2) :
    ∃ a ∈ OLe (-1), limV f LS i = X i * (1 + a) := by
  apply lim_mem_OLe i
  intro N
  obtain ⟨a, ha, e⟩ := prodL_mem_OLe hf hsupp (LS N) i
  exact ⟨a, ha, by rw [← e]; exact limV_eqMod hf hLS i N⟩

lemma subst_monomial_mem_OLe {v : Fin 2 → B} (hv : ∀ i, ∃ a ∈ OLe (-1), v i = X i * (1 + a))
    (m : Fin 2 →₀ ℕ) : ∃ a ∈ OLe (-1), subst v (monomial m 1 : B) = monomial m 1 * (1 + a) := by
  obtain ⟨a0, ha0, e0⟩ := hv 0
  obtain ⟨a1, ha1, e1⟩ := hv 1
  have hsv : SubVec v := fun i => by
    obtain ⟨a, -, e⟩ := hv i; rw [e]; exact (ord_X i).mul_right _
  refine ⟨(1 + a0) ^ m 0 * (1 + a1) ^ m 1 - 1, oneLe_mul (oneLe_pow (by simpa using ha0) _)
    (oneLe_pow (by simpa using ha1) _), ?_⟩
  rw [subst_monomial' v hsv, e0, e1, mul_pow, mul_pow, monomial_eq_XX, one_smul,
    map_one (C (σ := Fin 2) (R := ℚ))]
  ring


/-! ## Splitting a sorted list at the diagonal -/

lemma split_sorted (l : List Slope) (hl : l.Pairwise (· ≤ ·)) (p : Slope → Bool)
    (hp : ∀ a b, a ≤ b → p b = true → p a = true) :
    l = l.filter p ++ l.filter (fun x => !p x) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have ih' := ih (List.pairwise_cons.mp hl).2
    cases hx : p x
    · have hall : ∀ y ∈ l, p y = false := fun y hy => by
        by_contra h
        have := hp x y ((List.pairwise_cons.mp hl).1 y hy) (by simpa using h)
        rw [hx] at this; exact absurd this (by simp)
      have h1 : l.filter p = [] := List.filter_eq_nil_iff.mpr (fun y hy => by simp [hall y hy])
      have h2 : l.filter (fun x => !p x) = l := List.filter_eq_self.mpr (fun y hy => by simp [hall y hy])
      rw [List.filter_cons, List.filter_cons, hx, h1, h2]; simp
    · rw [List.filter_cons, List.filter_cons, hx]
      simp only [if_true, Bool.not_true, Bool.false_eq_true, if_false, List.cons_append]
      congr 1

lemma eq_singleton_of {l : List Slope} {a : Slope} (hnd : l.Nodup) (hall : ∀ x ∈ l, x = a)
    (ha : a ∈ l) : l = [a] := by
  rcases l with _ | ⟨b, l⟩
  · simp at ha
  · have hb := hall b List.mem_cons_self
    subst hb
    rcases l with _ | ⟨c, l⟩
    · rfl
    · exfalso
      have hc := hall c (List.mem_cons_of_mem _ List.mem_cons_self)
      subst hc
      exact (List.nodup_cons.mp hnd).1 List.mem_cons_self

lemma one_le_iff (τ : Slope) : ((1 : ℚ≥0) : Slope) ≤ τ ↔ (ray τ).1 ≤ (ray τ).2 := by
  rw [slope_le_iff, ray_one]; simp

lemma lt_one_iff' (τ : Slope) : τ < ((1 : ℚ≥0) : Slope) ↔ (ray τ).2 < (ray τ).1 := by
  rw [lt_iff_not_ge, one_le_iff]; omega

lemma one_lt_iff' (τ : Slope) : ((1 : ℚ≥0) : Slope) < τ ↔ (ray τ).1 < (ray τ).2 := by
  rw [lt_iff_not_ge, le_one_iff]; omega

/-- The parts of a family below and above the diagonal. -/
def famLt (φ : Slope → PowerSeries ℚ) (s : Slope) : PowerSeries ℚ :=
  if s < ((1 : ℚ≥0) : Slope) then φ s else 1
def famGt (φ : Slope → PowerSeries ℚ) (s : Slope) : PowerSeries ℚ :=
  if ((1 : ℚ≥0) : Slope) < s then φ s else 1

lemma prodL_split {φ : Slope → PowerSeries ℚ} (S : List Slope) (hS : S.Pairwise (· ≤ ·))
    (hnd : S.Nodup) (h1 : ((1 : ℚ≥0) : Slope) ∈ S) (g : B) :
    prodL φ S g = prodL (famLt φ) S
      (wall ((1 : ℚ≥0) : Slope) (φ ((1 : ℚ≥0) : Slope)) (prodL (famGt φ) S g)) := by
  set one : Slope := ((1 : ℚ≥0) : Slope)
  have hs1 := split_sorted S hS (fun s => decide (s < one))
    (fun a b hab hb => by simp only [decide_eq_true_eq] at hb ⊢; exact lt_of_le_of_lt hab hb)
  set T := S.filter (fun x => !decide (x < one))
  have hT : T.Pairwise (· ≤ ·) := List.Pairwise.filter _ hS
  have hs2 := split_sorted T hT (fun s => decide (s ≤ one))
    (fun a b hab hb => by simp only [decide_eq_true_eq] at hb ⊢; exact le_trans hab hb)
  have hmid : T.filter (fun s => decide (s ≤ one)) = [one] := by
    apply eq_singleton_of ((hnd.filter _).filter _)
    · intro x hx
      simp only [T, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not,
        decide_eq_true_eq] at hx
      exact le_antisymm hx.2 (not_lt.mp hx.1.2)
    · simp [T, h1]
  have hgt : T.filter (fun x => !decide (x ≤ one)) = S.filter (fun s => decide (one < s)) := by
    simp only [T, List.filter_filter]
    apply List.filter_congr
    intro x _
    by_cases h : one < x
    · have h1 : ¬ x ≤ one := not_le.mpr h
      have h2 : ¬ x < one := fun h' => lt_asymm h h'
      simp [h, h1, h2]
    · have h1 : x ≤ one := not_lt.mp h
      simp [h, h1]
  conv_lhs => rw [hs1, hs2, hmid, hgt]
  rw [prodL_append, prodL_append, prodL_cons, prodL_nil]
  rw [prodL_filter φ (famGt φ) (fun s => decide (one < s))
      (fun s hs => by rw [famGt, if_pos (of_decide_eq_true hs)])
      (fun s hs => by rw [famGt, if_neg (of_decide_eq_false hs)]),
    prodL_filter φ (famLt φ) (fun s => decide (s < one))
      (fun s hs => by rw [famLt, if_pos (of_decide_eq_true hs)])
      (fun s hs => by rw [famLt, if_neg (of_decide_eq_false hs)])]

end ErsConj13.Scat
