import ErsConj13.KSPoisson

/-!
# Existence of ordered factorizations (Kontsevich–Soibelman)
-/

noncomputable section

namespace ErsConj13.Scat

open MvPowerSeries
open ErsConj13 (bracket zd)

/-! ## Helpers: trivial walls, stabilization, weak perturbation -/

lemma wv_one (s : Slope) : wv s 1 = X := by
  funext i; fin_cases i <;> simp [wv, rayEval_one]

lemma wall_one (s : Slope) (h : B) : wall s 1 h = h := by
  rw [wall_eq, wv_one, subst_self']

/-- Agreement of two families in all coefficients of degree `< d` (degree of `z^{jr}` is `j|r|`). -/
def Agree (d : ℕ) (f f' : Slope → PowerSeries ℚ) : Prop :=
  ∀ s j, j * rlen s < d → PowerSeries.coeff j (f s) = PowerSeries.coeff j (f' s)

lemma prodL_weak_pert {f f' : Slope → PowerSeries ℚ} (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1)
    (hf' : ∀ s, PowerSeries.constantCoeff (f' s) = 1) {d : ℕ} (hd1 : 1 ≤ d) (hag : Agree d f f')
    (L : List Slope) {h : B} (hh : Ord 1 h) : EqMod (d + 1) (prodL f L h) (prodL f' L h) := by
  have hd : ∀ s ∈ L, Ord d (rayEval s (f s) - rayEval s (f' s)) :=
    fun s _ => ord_rayEval_sub s fun j hj => hag s j hj
  have hp := prodL_pert hf hf' hd1 L hd hh
  have hsum : Ord (d + 1) (L.map (pertTerm f f' h)).sum := by
    have : ∀ t ∈ L, Ord (d + 1) (pertTerm f f' h t) := fun t ht => pertTerm_ord (hd t ht)
    clear hp hd
    induction L with
    | nil => simpa using Ord.zero _
    | cons t L ih =>
      rw [List.map_cons, List.sum_cons]
      exact (this t List.mem_cons_self).add (ih fun u hu => this u (List.mem_cons_of_mem _ hu))
  rw [eqMod_iff]
  have := (hp.mono (by omega : d + 1 ≤ d + 2)).add hsum
  simpa using this

lemma prodL_filter (f f' : Slope → PowerSeries ℚ) (p : Slope → Bool)
    (h1 : ∀ s, p s = true → f' s = f s) (h0 : ∀ s, p s = false → f' s = 1)
    (L : List Slope) (h : B) : prodL f' L h = prodL f (L.filter p) h := by
  induction L with
  | nil => rw [List.filter_nil, prodL_nil, prodL_nil]
  | cons s L ih =>
    rw [prodL_cons, List.filter_cons]
    cases hs : p s
    · rw [h0 s hs, wall_one, ih, if_neg (by simp)]
    · rw [h1 s hs, ih, if_pos rfl, prodL_cons]

lemma sort_filter_slopesBelow {N M : ℕ} (hNM : N ≤ M) :
    ((slopesBelow M).sort (· ≤ ·)).filter (fun s => decide (rlen s < N)) =
      (slopesBelow N).sort (· ≤ ·) := by
  refine List.Perm.eq_of_pairwise' (r := fun a b : Slope => a ≤ b)
    (List.Pairwise.filter _ (Finset.pairwise_sort _ _)) (Finset.pairwise_sort _ _) ?_
  rw [List.perm_ext_iff_of_nodup ((Finset.sort_nodup _ _).filter _) (Finset.sort_nodup _ _)]
  intro s
  simp only [List.mem_filter, Finset.mem_sort, mem_slopesBelow, decide_eq_true_eq]
  omega

/-- Stabilization: the levelwise products are compatible. -/
lemma orderedProd_stab {f : Slope → PowerSeries ℚ} (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1)
    {N M : ℕ} (hNM : N ≤ M) (i : Fin 2) :
    EqMod N (orderedProd f M (X i)) (orderedProd f N (X i)) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; intro e he; omega
  set f' : Slope → PowerSeries ℚ := fun s => if rlen s < N then f s else 1
  have hf' : ∀ s, PowerSeries.constantCoeff (f' s) = 1 := fun s => by
    simp only [f']; split_ifs <;> simp [hf]
  have hag : Agree N f f' := by
    intro s j hj
    simp only [f']
    split_ifs with h
    · rfl
    · have : j = 0 := by
        by_contra hj0; have : rlen s ≤ j * rlen s := Nat.le_mul_of_pos_left _ (by omega)
        omega
      subst this; simp [hf]
  have h1 := prodL_weak_pert hf hf' hN hag ((slopesBelow M).sort (· ≤ ·)) (ord_X i)
  have h2 : prodL f' ((slopesBelow M).sort (· ≤ ·)) (X i) = orderedProd f N (X i) := by
    rw [prodL_filter f f' (fun s => decide (rlen s < N))
      (fun s hs => by simp only [f', if_pos (of_decide_eq_true hs)])
      (fun s hs => by simp only [f', if_neg (of_decide_eq_false hs)]),
      orderedProd_eq, sort_filter_slopesBelow hNM]
  rw [orderedProd_eq, ← h2]
  exact h1.mono' (by omega)

lemma prodL_unip {f : Slope → PowerSeries ℚ} (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1)
    (L : List Slope) (i : Fin 2) : ∃ b, Ord 1 b ∧ prodL f L (X i) = X i * (1 + b) := by
  induction L with
  | nil => exact ⟨0, Ord.zero 1, by simp [prodL_nil]⟩
  | cons s L ih =>
    obtain ⟨b, hb, e⟩ := ih
    rw [prodL_cons, e]
    exact wall_unip s (hf s) hb

lemma prodL_bracket {f : Slope → PowerSeries ℚ} (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1)
    (L : List Slope) (g h : B) : prodL f L (bracket g h) = bracket (prodL f L g) (prodL f L h) := by
  induction L with
  | nil => rfl
  | cons s L ih => rw [prodL_cons, prodL_cons, prodL_cons, ih, wall_bracket s (hf s)]

lemma bracket_X0_X1 : bracket (X 0 : B) (X 1) = X 0 * X 1 := by
  simp only [ErsConj13.bracket, zd_X]; simp

lemma prodL_bracket_gen {f : Slope → PowerSeries ℚ} (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1)
    (L : List Slope) :
    bracket (prodL f L (X 0)) (prodL f L (X 1)) = prodL f L (X 0) * prodL f L (X 1) := by
  rw [← prodL_bracket hf, bracket_X0_X1]
  induction L with
  | nil => rfl
  | cons s L ih =>
    rw [prodL_cons, prodL_cons, prodL_cons, ih, wall_eq]
    exact subst_mul (subVec_wv s (f s)).hasSubst _ _


/-! ## The divergence condition -/

lemma ord_of_X_mul {k : ℕ} (i : Fin 2) {W : B} (h : Ord (k + 1) (X i * W)) : Ord k W := by
  rw [ord_iff] at *
  intro e he
  have := h (Finsupp.single i 1 + e) (by rw [map_add]; simp; omega)
  rwa [coeff_X_mul_add] at this

lemma bracket_X0_X1mul (β : B) : bracket (X 0 : B) (X 1 * β) = X 0 * X 1 * (β + zd 1 β) := by
  simp only [ErsConj13.bracket, zd_mul, zd_X]; simp; ring

lemma bracket_X0mul_X1 (α : B) : bracket (X 0 * α : B) (X 1) = X 0 * X 1 * (α + zd 0 α) := by
  simp only [ErsConj13.bracket, zd_mul, zd_X]; simp; ring

/-- If `g` and a Poisson product `P` agree to order `n` on the generators, the degree-`(n−1)`
discrepancy `(α, β)` (with `g x − P x = x α`, `g y − P y = y β`) is divergence-free. -/
lemma divergence {n : ℕ} (hn : 2 ≤ n) {a0 a1 b0 b1 : B} (hb0 : Ord 1 b0) (hb1 : Ord 1 b1)
    (hα : Ord (n - 1) (a0 - b0)) (hβ : Ord (n - 1) (a1 - b1))
    (hP : bracket (X 0 * (1 + b0)) (X 1 * (1 + b1)) = X 0 * (1 + b0) * (X 1 * (1 + b1)))
    (hg : bracket (X 0 * (1 + a0)) (X 1 * (1 + a1)) = X 0 * (1 + a0) * (X 1 * (1 + a1))) :
    Ord n (zd 0 (a0 - b0) + zd 1 (a1 - b1)) := by
  set α := a0 - b0
  set β := a1 - b1
  have ea : X 0 * (1 + a0) = X 0 + X 0 * b0 + X 0 * α := by simp only [α]; ring
  have eb : X 1 * (1 + a1) = X 1 + X 1 * b1 + X 1 * β := by simp only [β]; ring
  have ea' : X 0 * (1 + b0) = X 0 + X 0 * b0 := by ring
  have eb' : X 1 * (1 + b1) = X 1 + X 1 * b1 := by ring
  rw [ea, eb] at hg
  rw [ea', eb'] at hP
  simp only [bracket_add_left, bracket_add_right'] at hg hP
  simp only [bracket_X0_X1mul, bracket_X0mul_X1] at hg hP
  have hXα : Ord n (X 0 * α) := by
    have := (ord_X 0).mul hα; rwa [show 1 + (n - 1) = n by omega] at this
  have hXβ : Ord n (X 1 * β) := by
    have := (ord_X 1).mul hβ; rwa [show 1 + (n - 1) = n by omega] at this
  have hXb0 : Ord 2 (X 0 * b0) := (ord_X 0).mul hb0
  have hXb1 : Ord 2 (X 1 * b1) := (ord_X 1).mul hb1
  have key : X 0 * X 1 * (zd 0 α + zd 1 β) =
      -(bracket (X 0 * b0) (X 1 * β) + bracket (X 0 * α) (X 1 * b1)
        + bracket (X 0 * α) (X 1 * β) - X 0 * b0 * (X 1 * β) - X 0 * α * (X 1 * b1)
        - X 0 * α * (X 1 * β)) := by
    linear_combination hg - hP
  have hord : Ord (n + 2) (X 0 * X 1 * (zd 0 α + zd 1 β)) := by
    rw [key]
    refine Ord.neg (((((?_ : Ord (n + 2) _).add ?_).add ?_).sub ?_).sub ?_ |>.sub ?_)
    · have := ord_bracket hXb0 hXβ; rwa [show 2 + n = n + 2 by ring] at this
    · exact ord_bracket hXα hXb1
    · exact (ord_bracket hXα hXβ).mono (by omega)
    · have := hXb0.mul hXβ; rwa [show 2 + n = n + 2 by ring] at this
    · exact hXα.mul hXb1
    · exact (hXα.mul hXβ).mono (by omega)
  have h1 : Ord (n + 1) (X 1 * (zd 0 α + zd 1 β)) := by
    apply ord_of_X_mul 0; rw [← mul_assoc]; exact hord
  exact ord_of_X_mul 1 h1


/-! ## Helpers for the existence step -/

lemma exists_ray {k : Fin 2 →₀ ℕ} (hk : k ≠ 0) : ∃ s j, 1 ≤ j ∧ k = j • rvec s := by
  have hk' : k 0 ≠ 0 ∨ k 1 ≠ 0 := by
    by_contra h; push Not at h; apply hk; ext i; fin_cases i <;> simp [h.1, h.2]
  set g := Nat.gcd (k 0) (k 1)
  have hg : 0 < g := by
    rcases hk' with h0 | h1
    · exact Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero h0)
    · exact Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero h1)
  have hcop : Nat.Coprime (k 0 / g) (k 1 / g) := Nat.coprime_div_gcd_div_gcd hg
  refine ⟨slopeOf (k 0 / g) (k 1 / g), g, hg, ?_⟩
  ext i
  simp only [Finsupp.smul_apply, smul_eq_mul]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, rvec_apply0, ray_slopeOf hcop]
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
  · simp only [Fin.mk_one, Fin.isValue, rvec_apply1, ray_slopeOf hcop]
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm

lemma rayEval_add (s : Slope) (F G : PowerSeries ℚ) :
    rayEval s (F + G) = rayEval s F + rayEval s G := by
  rw [rayEval, rayEval, rayEval, PowerSeries.subst_add (hasSubst_rayMono s)]

lemma rayEval_monomial (s : Slope) (j : ℕ) (c : ℚ) :
    rayEval s (PowerSeries.monomial j c) = monomial (j • rvec s) c := by
  classical
  ext e
  rw [coeff_rayEval, coeff_monomial]
  split_ifs with h1 h2 h2
  · rw [PowerSeries.coeff_monomial, if_pos]
    exact (smul_rvec_inj (h1.choose_spec.symm.trans h2)).symm ▸ rfl
  · rw [PowerSeries.coeff_monomial, if_neg]
    intro hc; apply h2; rw [h1.choose_spec, hc]
  · exact absurd ⟨j, h2⟩ h1
  · rfl

lemma list_sum_single {L : List Slope} (hL : L.Nodup) {s : Slope} (hs : s ∈ L) (F : Slope → ℚ)
    (hF : ∀ t, t ≠ s → F t = 0) : (L.map F).sum = F s := by
  induction L with
  | nil => simp at hs
  | cons t L ih =>
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hs with hst | hs'
    · subst hst
      have hnot : s ∉ L := (List.nodup_cons.mp hL).1
      have : (L.map F).sum = 0 := by
        clear ih hs hL
        induction L with
        | nil => simp
        | cons u L ih2 =>
          rw [List.map_cons, List.sum_cons, hF u (fun h => hnot (by rw [← h]; exact List.mem_cons_self)),
            zero_add]
          exact ih2 (fun h => hnot (List.mem_cons_of_mem _ h))
      rw [this, add_zero]
    · rw [hF t (fun h => (List.nodup_cons.mp hL).1 (h ▸ hs')), zero_add]
      exact ih (List.nodup_cons.mp hL).2 hs'


/-! ## The existence step -/

/-- `f` factors `g` up to order `n`. -/
def FactorsUpTo (g : B → B) (n : ℕ) (f : Slope → PowerSeries ℚ) : Prop :=
  ∀ N ≤ n, ∀ i, EqMod N (orderedProd f N (X i)) (g (X i))

/-- The hypotheses on the target used by existence (only its values on the generators matter). -/
structure GenHyp (g : B → B) : Prop where
  h0 : ∃ a, Ord 1 a ∧ g (X 0) = X 0 * (1 + a)
  h1 : ∃ a, Ord 1 a ∧ g (X 1) = X 1 * (1 + a)
  hb : bracket (g (X 0)) (g (X 1)) = g (X 0) * g (X 1)

/-- The correction of the ray function of `s` in degree `m`. -/
def corr (m : ℕ) (α β : B) (s : Slope) : ℚ :=
  if rlen s ∣ m then
    (if (ray s).2 ≠ 0 then coeff ((m / rlen s) • rvec s) α / (ray s).2
     else -(coeff ((m / rlen s) • rvec s) β / (ray s).1))
  else 0

/-- The corrected family. -/
def corrFam (f : Slope → PowerSeries ℚ) (m : ℕ) (α β : B) (s : Slope) : PowerSeries ℚ :=
  f s + PowerSeries.monomial (m / rlen s) (corr m α β s)

lemma corr_eq_zero_of {m : ℕ} {α β : B} {s : Slope} (h : ¬ rlen s ∣ m) : corr m α β s = 0 := by
  simp [corr, h]

lemma corrFam_cc {f : Slope → PowerSeries ℚ} (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1)
    {m : ℕ} (hm : 1 ≤ m) (α β : B) (s : Slope) :
    PowerSeries.constantCoeff (corrFam f m α β s) = 1 := by
  rw [corrFam, map_add, hf, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_monomial]
  split_ifs with h
  · by_cases hd : rlen s ∣ m
    · exfalso; obtain ⟨c, hc⟩ := hd
      have := rlen_pos s
      rw [hc, Nat.mul_div_cancel_left _ (by omega)] at h
      subst h; omega
    · rw [corr_eq_zero_of hd, add_zero]
  · simp

lemma corrFam_agree (f : Slope → PowerSeries ℚ) (m : ℕ) (α β : B) :
    Agree m f (corrFam f m α β) := by
  intro s j hj
  rw [corrFam, map_add, PowerSeries.coeff_monomial]
  split_ifs with h
  · by_cases hd : rlen s ∣ m
    · exfalso; rw [h, Nat.div_mul_cancel hd] at hj; omega
    · rw [corr_eq_zero_of hd, add_zero]
  · rw [add_zero]

lemma corrFam_delta (f : Slope → PowerSeries ℚ) (m : ℕ) (α β : B) (s : Slope) :
    rayEval s (corrFam f m α β s) - rayEval s (f s) =
      monomial ((m / rlen s) • rvec s) (corr m α β s) := by
  rw [corrFam, rayEval_add, rayEval_monomial]; ring

lemma coeff_corr_term (m : ℕ) (α β : B) (c : ℚ) (t : Slope) (e : Fin 2 →₀ ℕ) :
    coeff e (C c * monomial ((m / rlen t) • rvec t) (corr m α β t) : B) =
      if e = (m / rlen t) • rvec t then c * corr m α β t else 0 := by
  rw [coeff_C_mul, coeff_monomial]; split_ifs <;> simp

lemma coeff_corr_low {m : ℕ} {α β : B} (L : List Slope) (c : Slope → ℚ) (e : Fin 2 →₀ ℕ)
    (he : e.degree < m) :
    coeff e ((L.map fun t => (C (c t) : B) * monomial ((m / rlen t) • rvec t) (corr m α β t)).sum)
      = 0 := by
  rw [map_list_sum, List.map_map]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
  simp only [Function.comp_apply, coeff_corr_term]
  split_ifs with h
  · by_cases hd : rlen t ∣ m
    · exfalso; rw [h, map_nsmul, rvec_degree, smul_eq_mul, Nat.div_mul_cancel hd] at he; omega
    · rw [corr_eq_zero_of hd, mul_zero]
  · rfl

lemma coeff_corr_top {m : ℕ} {α β : B} (L : List Slope) (hL : L.Nodup) (c : Slope → ℚ)
    {s : Slope} (hs : s ∈ L) {j : ℕ} (hj : 1 ≤ j) (hjm : j * rlen s = m) :
    coeff (j • rvec s)
      ((L.map fun t => (C (c t) : B) * monomial ((m / rlen t) • rvec t) (corr m α β t)).sum)
      = c s * corr m α β s := by
  rw [map_list_sum, List.map_map]
  have hjs : m / rlen s = j := by rw [← hjm, Nat.mul_div_cancel _ (rlen_pos s)]
  rw [list_sum_single hL hs]
  · simp only [Function.comp_apply, hjs]; rw [coeff_C_mul, coeff_monomial_same]
  · intro t ht
    simp only [Function.comp_apply, coeff_corr_term]
    rw [if_neg]
    intro h
    exact ht (smul_rvec_eq hj h).1.symm


lemma agree_symm {d : ℕ} {f f' : Slope → PowerSeries ℚ} (h : Agree d f f') : Agree d f' f :=
  fun s j hj => (h s j hj).symm

lemma ray_eq_of_snd_zero {s : Slope} (h : (ray s).2 = 0) : (ray s).1 = 1 := by
  have := ray_coprime s; rw [h] at this; simpa using this

/-- The pertTerm sums, factored. -/
lemma pertSum_X0 (f f' : Slope → PowerSeries ℚ) (L : List Slope) :
    (L.map (pertTerm f f' (X 0))).sum =
      X 0 * (L.map fun t => (C ((ray t).2 : ℚ) : B) * (rayEval t (f t) - rayEval t (f' t))).sum := by
  rw [← List.sum_map_mul_left]
  congr 1; apply List.map_congr_left; intro t _
  rw [pertTerm, lin_X, lin_X, if_pos rfl, if_neg (show (1 : Fin 2) ≠ 0 by decide), one_smul,
    zero_smul, sub_zero, show ((ray t).2 : B) = C ((ray t).2 : ℚ) from (map_natCast C _).symm]
  ring

lemma pertSum_X1 (f f' : Slope → PowerSeries ℚ) (L : List Slope) :
    (L.map (pertTerm f f' (X 1))).sum =
      X 1 * (L.map fun t => (C (-((ray t).1 : ℚ)) : B) * (rayEval t (f t) - rayEval t (f' t))).sum := by
  rw [← List.sum_map_mul_left]
  congr 1; apply List.map_congr_left; intro t _
  rw [pertTerm, lin_X, lin_X, if_neg (show (0 : Fin 2) ≠ 1 by decide), if_pos rfl, one_smul,
    zero_smul, zero_sub, map_neg, show ((ray t).1 : B) = C ((ray t).1 : ℚ) from (map_natCast C _).symm]
  ring

/-- One step of the degree induction. -/
theorem ks_step {g : B → B} (hg : GenHyp g) {n : ℕ} (hn : 2 ≤ n) {f : Slope → PowerSeries ℚ}
    (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1) (hF : FactorsUpTo g n f) :
    ∃ f', (∀ s, PowerSeries.constantCoeff (f' s) = 1) ∧ Agree (n - 1) f f' ∧
      FactorsUpTo g (n + 1) f' := by
  obtain ⟨a0, ha0, hg0⟩ := hg.h0
  obtain ⟨a1, ha1, hg1⟩ := hg.h1
  set L := (slopesBelow (n + 1)).sort (· ≤ ·) with hLdef
  have hLnd : L.Nodup := Finset.sort_nodup _ _
  obtain ⟨b0, hb0, hP0⟩ := prodL_unip hf L 0
  obtain ⟨b1, hb1, hP1⟩ := prodL_unip hf L 1
  have hEq : ∀ i, EqMod n (prodL f L (X i)) (g (X i)) := fun i => by
    have := orderedProd_stab hf (Nat.le_succ n) i
    rw [orderedProd_eq] at this
    exact this.trans' (hF n le_rfl i)
  set m := n - 1 with hmdef
  have hm : 1 ≤ m := by omega
  have hnm : n = m + 1 := by omega
  have hα : Ord m (a0 - b0) := by
    have := eqMod_iff.mp (hEq 0); rw [hP0, hg0, hnm] at this
    apply ord_of_X_mul 0
    rw [show X 0 * (a0 - b0) = -(X 0 * (1 + b0) - X 0 * (1 + a0)) by ring]; exact this.neg
  have hβ : Ord m (a1 - b1) := by
    have := eqMod_iff.mp (hEq 1); rw [hP1, hg1, hnm] at this
    apply ord_of_X_mul 1
    rw [show X 1 * (a1 - b1) = -(X 1 * (1 + b1) - X 1 * (1 + a1)) by ring]; exact this.neg
  have hdiv := divergence hn hb0 hb1 hα hβ
    (by rw [← hP0, ← hP1]; exact prodL_bracket_gen hf L) (by rw [← hg0, ← hg1]; exact hg.hb)
  set α := a0 - b0 with hαdef
  set β := a1 - b1 with hβdef
  have hdivc : ∀ e : Fin 2 →₀ ℕ, e.degree = m →
      (e 0 : ℚ) * coeff e α + (e 1 : ℚ) * coeff e β = 0 := by
    intro e he
    have := ord_iff.mp hdiv e (by omega)
    rwa [map_add, coeff_zd, coeff_zd] at this
  set f' := corrFam f m α β with hf'def
  have hf' : ∀ s, PowerSeries.constantCoeff (f' s) = 1 := corrFam_cc hf hm α β
  have hag : Agree m f f' := corrFam_agree f m α β
  refine ⟨f', hf', hag, ?_⟩
  intro N hN i
  rcases Nat.lt_or_ge N (n + 1) with hlt | hge
  · have hw := prodL_weak_pert hf' hf hm (agree_symm hag) ((slopesBelow N).sort (· ≤ ·)) (ord_X i)
    rw [← hnm] at hw
    rw [orderedProd_eq]
    exact (hw.mono' (by omega)).trans' (by rw [← orderedProd_eq]; exact hF N (by omega) i)
  have hN' : N = n + 1 := by omega
  subst hN'
  have hδ : ∀ t ∈ L, Ord m (rayEval t (f' t) - rayEval t (f t)) :=
    fun t _ => ord_rayEval_sub t fun j hj => (hag t j hj).symm
  have hp := prodL_pert hf' hf hm L hδ (ord_X i)
  rw [show m + 2 = n + 1 by omega] at hp
  have hLm : ∀ s, rlen s ≤ m → s ∈ L := fun s hs => by
    rw [hLdef, Finset.mem_sort, mem_slopesBelow]; omega
  -- the residual: the correction sum equals the discrepancy to order `n + 1`
  have key : Ord (n + 1) ((L.map (pertTerm f' f (X i))).sum - (g (X i) - prodL f L (X i))) := by
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [pertSum_X0, hP0, hg0]
      simp only [hf'def, corrFam_delta]
      rw [show X 0 * (List.map (fun t => (C ((ray t).2 : ℚ) : B) *
          monomial ((m / rlen t) • rvec t) (corr m α β t)) L).sum - (X 0 * (1 + a0) - X 0 * (1 + b0))
          = X 0 * ((List.map (fun t => (C ((ray t).2 : ℚ) : B) *
          monomial ((m / rlen t) • rvec t) (corr m α β t)) L).sum - α) by simp only [hαdef]; ring]
      rw [hnm, add_comm]
      refine (ord_X 0).mul ?_
      rw [ord_iff]; intro e he
      rw [map_sub, sub_eq_zero]
      rcases Nat.lt_or_ge e.degree m with hlow | hhigh
      · rw [coeff_corr_low L _ e hlow, ord_iff.mp hα e hlow]
      · have hem : e.degree = m := by omega
        have he0 : e ≠ 0 := by rintro rfl; simp at hem; omega
        obtain ⟨s, j, hj, rfl⟩ := exists_ray he0
        have hjm : j * rlen s = m := by rw [← hem, map_nsmul, rvec_degree, smul_eq_mul]
        rw [coeff_corr_top L hLnd _ (hLm s (by rw [← hjm]; exact Nat.le_mul_of_pos_left _ hj)) hj hjm]
        have hd : rlen s ∣ m := ⟨j, by rw [← hjm]; ring⟩
        have hjs : m / rlen s = j := by rw [← hjm, Nat.mul_div_cancel _ (rlen_pos s)]
        simp only [corr, hd, if_true, hjs]
        by_cases hq : (ray s).2 ≠ 0
        · rw [if_pos hq]; field_simp
        · rw [if_neg hq]
          push Not at hq
          have hp1 := ray_eq_of_snd_zero hq
          have := hdivc (j • rvec s) hem
          simp only [Finsupp.smul_apply, rvec_apply0, rvec_apply1, hq, hp1, smul_eq_mul] at this
          simp only [hq, Nat.cast_zero, zero_mul]
          have hj' : (j : ℚ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
          simp at this
          rcases this with h | h
          · exact absurd (by exact_mod_cast h) hj'
          · exact h.symm
    · simp only [Fin.mk_one, Fin.isValue]
      rw [pertSum_X1, hP1, hg1]
      simp only [hf'def, corrFam_delta]
      rw [show X 1 * (List.map (fun t => (C (-((ray t).1 : ℚ)) : B) *
          monomial ((m / rlen t) • rvec t) (corr m α β t)) L).sum - (X 1 * (1 + a1) - X 1 * (1 + b1))
          = X 1 * ((List.map (fun t => (C (-((ray t).1 : ℚ)) : B) *
          monomial ((m / rlen t) • rvec t) (corr m α β t)) L).sum - β) by simp only [hβdef]; ring]
      rw [hnm, add_comm]
      refine (ord_X 1).mul ?_
      rw [ord_iff]; intro e he
      rw [map_sub, sub_eq_zero]
      rcases Nat.lt_or_ge e.degree m with hlow | hhigh
      · rw [coeff_corr_low L _ e hlow, ord_iff.mp hβ e hlow]
      · have hem : e.degree = m := by omega
        have he0 : e ≠ 0 := by rintro rfl; simp at hem; omega
        obtain ⟨s, j, hj, rfl⟩ := exists_ray he0
        have hjm : j * rlen s = m := by rw [← hem, map_nsmul, rvec_degree, smul_eq_mul]
        rw [coeff_corr_top L hLnd _ (hLm s (by rw [← hjm]; exact Nat.le_mul_of_pos_left _ hj)) hj hjm]
        have hd : rlen s ∣ m := ⟨j, by rw [← hjm]; ring⟩
        have hjs : m / rlen s = j := by rw [← hjm, Nat.mul_div_cancel _ (rlen_pos s)]
        simp only [corr, hd, if_true, hjs]
        have := hdivc (j • rvec s) hem
        simp only [Finsupp.smul_apply, rvec_apply0, rvec_apply1, smul_eq_mul] at this
        have hj' : (j : ℚ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
        push_cast at this
        by_cases hq : (ray s).2 ≠ 0
        · rw [if_pos hq]
          have hq' : ((ray s).2 : ℚ) ≠ 0 := by exact_mod_cast hq
          field_simp
          have : (j : ℚ) * (((ray s).1 : ℚ) * coeff (j • rvec s) α
            + ((ray s).2 : ℚ) * coeff (j • rvec s) β) = 0 := by linear_combination this
          rcases mul_eq_zero.mp this with h | h
          · exact absurd (by exact_mod_cast h) hj'
          · linear_combination -h
        · rw [if_neg hq]
          push Not at hq
          have hp1 := ray_eq_of_snd_zero hq
          rw [hp1]; push_cast; ring
  have := (hp.add key)
  rw [eqMod_iff, orderedProd_eq]
  have e : prodL f' L (X i) - g (X i) = (prodL f' L (X i) - prodL f L (X i)
      - (L.map (pertTerm f' f (X i))).sum) + ((L.map (pertTerm f' f (X i))).sum
      - (g (X i) - prodL f L (X i))) := by ring
  rw [e]; exact this


lemma agree_trans {d : ℕ} {f f' f'' : Slope → PowerSeries ℚ} (h : Agree d f f') (h' : Agree d f' f'') :
    Agree d f f'' := fun s j hj => (h s j hj).trans (h' s j hj)

lemma agree_mono {d d' : ℕ} (hdd : d ≤ d') {f f' : Slope → PowerSeries ℚ} (h : Agree d' f f') :
    Agree d f f' := fun s j hj => h s j (by omega)

lemma prodL_one (L : List Slope) (h : B) : prodL (fun _ => 1) L h = h := by
  induction L with
  | nil => rw [prodL_nil]
  | cons s L ih => rw [prodL_cons, ih, wall_one]

lemma factors_base {g : B → B} (hg : GenHyp g) : FactorsUpTo g 2 (fun _ => 1) := by
  intro N hN i
  rw [orderedProd_eq, prodL_one]
  apply EqMod.mono' hN
  rw [eqMod_iff]
  fin_cases i
  · obtain ⟨a, ha, e⟩ := hg.h0
    simp only [Fin.zero_eta, Fin.isValue]; rw [e]
    have : X 0 - X 0 * (1 + a) = -(X 0 * a) := by ring
    rw [this]; exact ((ord_X 0).mul ha).neg
  · obtain ⟨a, ha, e⟩ := hg.h1
    simp only [Fin.mk_one, Fin.isValue]; rw [e]
    have : X 1 - X 1 * (1 + a) = -(X 1 * a) := by ring
    rw [this]; exact ((ord_X 1).mul ha).neg

/-- The approximating families. -/
structure Approx (g : B → B) (k : ℕ) where
  f : Slope → PowerSeries ℚ
  cc : ∀ s, PowerSeries.constantCoeff (f s) = 1
  fac : FactorsUpTo g (k + 2) f

noncomputable def approxSeq {g : B → B} (hg : GenHyp g) : (k : ℕ) → Approx g k
  | 0 => ⟨fun _ => 1, fun _ => by simp, factors_base hg⟩
  | k + 1 =>
    let a := approxSeq hg k
    let h := ks_step hg (by omega : 2 ≤ k + 2) a.cc a.fac
    ⟨h.choose, h.choose_spec.1, h.choose_spec.2.2⟩

lemma approxSeq_agree_succ {g : B → B} (hg : GenHyp g) (k : ℕ) :
    Agree (k + 1) (approxSeq hg k).f (approxSeq hg (k + 1)).f := by
  have h := ks_step hg (by omega : 2 ≤ k + 2) (approxSeq hg k).cc (approxSeq hg k).fac
  exact h.choose_spec.2.1

lemma approxSeq_agree {g : B → B} (hg : GenHyp g) {k k' : ℕ} (hkk : k ≤ k') :
    Agree (k + 1) (approxSeq hg k).f (approxSeq hg k').f := by
  induction k', hkk using Nat.le_induction with
  | base => exact fun s j _ => rfl
  | succ k' hk ih =>
    exact agree_trans ih (agree_mono (by omega) (approxSeq_agree_succ hg k'))

/-- Existence of the ordered factorization (KS). -/
theorem factor_exists_aux {g : B → B} (hg : GenHyp g) :
    ∃ F : Slope → PowerSeries ℚ, (∀ s, PowerSeries.constantCoeff (F s) = 1) ∧
      ∀ N i, EqMod N (orderedProd F N (X i)) (g (X i)) := by
  set F : Slope → PowerSeries ℚ := fun s =>
    PowerSeries.mk fun j => PowerSeries.coeff j ((approxSeq hg (j * rlen s)).f s)
  have hFag : ∀ k, Agree (k + 1) F (approxSeq hg k).f := by
    intro k s j hj
    simp only [F, PowerSeries.coeff_mk]
    exact approxSeq_agree hg (by omega) s j (by omega)
  have hFcc : ∀ s, PowerSeries.constantCoeff (F s) = 1 := by
    intro s
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp only [F, PowerSeries.coeff_mk, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [Nat.zero_mul]
    exact (approxSeq hg 0).cc s
  refine ⟨F, hFcc, fun N i => ?_⟩
  have h1 := prodL_weak_pert hFcc (approxSeq hg N).cc (by omega : 1 ≤ N + 1) (hFag N)
    ((slopesBelow N).sort (· ≤ ·)) (ord_X i)
  rw [orderedProd_eq]
  refine (h1.mono' (by omega)).trans' ?_
  rw [← orderedProd_eq]
  exact (approxSeq hg N).fac N (by omega) i

end ErsConj13.Scat
