import ErsConj13.R1Pieces
import ErsConj13.Extraction

/-!
# Change of lattice: `D((1+X)⁵, 1+Y)` on `ℚ⟦X,Y⟧` versus `D(1+x, 1+y⁵)` on `ℚ⟦x,y⟧`

`ι5 : X ↦ x, Y ↦ y⁵` maps exponents `(p,q) ↦ (p, 5q)`. The C-ray `(d,e)` goes to the B-ray
`v ∝ (d, 5e)`: `v = (d, 5e)` when `5 ∤ d` (γ = 1) and `v = (d/5, e)` when `5 ∣ d` (γ = 5). This is a
bijection on primitive rays (slope × 5). The C-wall with function `G` corresponds to the B-wall
with `h` where `h⁵ = G` (γ = 1) or `h(t) = G(t⁵)` (γ = 5).
-/

noncomputable section

namespace ErsConj13

open Scat MvPowerSeries

/-! ## Fifth roots -/

lemma exists_root5 (G : PowerSeries ℚ) (hG : PowerSeries.constantCoeff G = 1) :
    ∃ h : PowerSeries ℚ, PowerSeries.constantCoeff h = 1 ∧ h ^ 5 = G := by
  set I : Ideal (PowerSeries ℚ) := Ideal.span {PowerSeries.X}
  set f : Polynomial (PowerSeries ℚ) := Polynomial.X ^ 5 - Polynomial.C G with hf
  have hmon : f.Monic := by rw [hf]; monicity!
  have hmem : ∀ g : PowerSeries ℚ, PowerSeries.constantCoeff g = 0 → g ∈ I := fun g hg =>
    Ideal.mem_span_singleton.mpr ((PowerSeries.X_dvd_iff).mpr hg)
  have h1 : f.eval 1 ∈ I := by apply hmem; simp [f, hG]
  have h2 : IsUnit (Ideal.Quotient.mk I (f.derivative.eval 1)) := by
    apply IsUnit.map
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have c4 : PowerSeries.constantCoeff (4 : PowerSeries ℚ) = 4 := map_ofNat _ 4
    simp [f, c4]; norm_num
  obtain ⟨h, hroot, hsub⟩ := HenselianRing.is_henselian f hmon 1 h1 h2
  refine ⟨h, ?_, ?_⟩
  · have := Ideal.mem_span_singleton.mp hsub
    rw [PowerSeries.X_dvd_iff] at this
    simpa [sub_eq_zero] using this
  · have : h ^ 5 - G = 0 := by simpa [f] using hroot
    exact sub_eq_zero.mp this

/-- The fifth root with constant term 1. -/
def root5 (G : PowerSeries ℚ) : PowerSeries ℚ :=
  if hG : PowerSeries.constantCoeff G = 1 then (exists_root5 G hG).choose else 1

/-! ## The ray map -/

/-- The B-slope of the image of the C-ray of slope `σ` (slope × 5). -/
def Lup5 (σ : Slope) : Slope := slopeOf (ray σ).1 (5 * (ray σ).2)

/-- The inverse: the C-slope of the preimage of the B-ray of slope `τ` (slope / 5). -/
def Ldown5 (τ : Slope) : Slope :=
  if 5 ∣ (ray τ).2 then slopeOf (ray τ).1 ((ray τ).2 / 5) else slopeOf (5 * (ray τ).1) (ray τ).2

lemma slopeOf_mul {k : ℕ} (hk : 0 < k) (a b : ℕ) : slopeOf (k * a) (k * b) = slopeOf a b := by
  unfold slopeOf
  by_cases ha : a = 0
  · simp [ha]
  · rw [if_neg (by positivity), if_neg ha]
    congr 1
    push_cast
    rw [mul_div_mul_left _ _ (by exact_mod_cast hk.ne')]

lemma slopeOf_le_iff {a b a' b' : ℕ} (h : a ≠ 0 ∨ b ≠ 0) :
    slopeOf a b ≤ slopeOf a' b' ↔ b * a' ≤ b' * a := by
  unfold slopeOf
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by tauto
    rw [if_pos ha, ha, mul_zero, top_le_iff]
    by_cases ha' : a' = 0
    · simp [ha']
    · rw [if_neg ha']; simp only [WithTop.coe_ne_top, false_iff, not_le]
      exact Nat.mul_pos (Nat.pos_of_ne_zero hb) (Nat.pos_of_ne_zero ha')
  · rw [if_neg ha]
    by_cases ha' : a' = 0
    · simp [ha']
    · rw [if_neg ha', WithTop.coe_le_coe, div_le_div_iff₀ (by positivity) (by positivity)]
      constructor <;> intro h <;> exact_mod_cast h

lemma coprime5_of_not_dvd {n : ℕ} (h : ¬ 5 ∣ n) : Nat.Coprime 5 n :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr h

lemma ray_Lup5 (σ : Slope) : ray (Lup5 σ) =
    if 5 ∣ (ray σ).1 then ((ray σ).1 / 5, (ray σ).2) else ((ray σ).1, 5 * (ray σ).2) := by
  have hc := ray_coprime σ
  split_ifs with h
  · obtain ⟨d', hd'⟩ := h
    rw [Lup5, hd', slopeOf_mul (by norm_num), ray_slopeOf, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [hd'] at hc; exact Nat.Coprime.coprime_dvd_left (dvd_mul_left _ _) hc
  · rw [Lup5, ray_slopeOf]
    exact Nat.Coprime.mul_right (coprime5_of_not_dvd h).symm hc

lemma ray_Ldown5 (τ : Slope) : ray (Ldown5 τ) =
    if 5 ∣ (ray τ).2 then ((ray τ).1, (ray τ).2 / 5) else (5 * (ray τ).1, (ray τ).2) := by
  have hc := ray_coprime τ
  unfold Ldown5
  split_ifs with h
  · obtain ⟨b', hb'⟩ := h
    rw [ray_slopeOf]
    rw [hb'] at hc ⊢; rw [Nat.mul_div_cancel_left _ (by norm_num)]
    exact Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _) hc
  · rw [ray_slopeOf]
    exact Nat.Coprime.mul_left (coprime5_of_not_dvd h) hc

lemma not_dvd_of_coprime {a b : ℕ} (hc : Nat.Coprime a b) (ha : 5 ∣ a) : ¬ 5 ∣ b := by
  intro hb
  have := Nat.dvd_gcd ha hb
  rw [hc] at this; norm_num at this

lemma Ldown5_Lup5 (σ : Slope) : Ldown5 (Lup5 σ) = σ := by
  apply ray_injective
  rw [ray_Ldown5, ray_Lup5]
  have hc := ray_coprime σ
  by_cases h : 5 ∣ (ray σ).1
  · have he := not_dvd_of_coprime hc h
    simp only [if_pos h, if_neg he, Nat.mul_div_cancel' h]
  · simp only [if_neg h, dvd_mul_right, if_true, Nat.mul_div_cancel_left _ (by norm_num : 0 < 5)]

lemma Lup5_Ldown5 (τ : Slope) : Lup5 (Ldown5 τ) = τ := by
  apply ray_injective
  rw [ray_Lup5, ray_Ldown5]
  have hc := ray_coprime τ
  by_cases h : 5 ∣ (ray τ).2
  · have ha := not_dvd_of_coprime hc.symm h
    simp only [if_pos h, if_neg ha, Nat.mul_div_cancel' h]
  · simp only [if_neg h, dvd_mul_right, if_true, Nat.mul_div_cancel_left _ (by norm_num : 0 < 5)]

lemma Lup5_mono {σ σ' : Slope} (h : σ ≤ σ') : Lup5 σ ≤ Lup5 σ' := by
  rw [slope_le_iff] at h
  have hr := rlen_pos σ
  rw [Lup5, Lup5, slopeOf_le_iff (by simp only [rlen] at hr; omega)]
  nlinarith

lemma Lup5_injective : Function.Injective Lup5 := fun a b h => by
  rw [← Ldown5_Lup5 a, ← Ldown5_Lup5 b, h]

lemma rlen_Ldown5_le (τ : Slope) : rlen (Ldown5 τ) ≤ 5 * rlen τ := by
  rw [rlen, rlen, ray_Ldown5]
  split_ifs <;> simp only <;> omega

/-- The transported B-family. -/
def fam5 (φ : Slope → PowerSeries ℚ) (τ : Slope) : PowerSeries ℚ :=
  if 5 ∣ (ray τ).2 then root5 (φ (Ldown5 τ))
  else PowerSeries.expand 5 (by norm_num) (φ (Ldown5 τ))

lemma ray_five_halves : ray ((5 / 2 : ℚ≥0) : Slope) = (2, 5) := by
  rw [ray_coe', Prod.mk.injEq]
  constructor
  · rw [← NNRat.den_coe]; push_cast; norm_num
  · have h : ((5 / 2 : ℚ≥0) : ℚ).num = 5 := by push_cast; norm_num
    rw [NNRat.num_coe] at h; exact_mod_cast h

lemma fam5_52 (φ : Slope → PowerSeries ℚ) :
    fam5 φ ((5 / 2 : ℚ≥0) : Slope) = root5 (φ ((1 / 2 : ℚ≥0) : Slope)) := by
  have hd : Ldown5 ((5 / 2 : ℚ≥0) : Slope) = ((1 / 2 : ℚ≥0) : Slope) := by
    apply ray_injective
    rw [ray_Ldown5, ray_five_halves, ray_half]; norm_num
  rw [fam5, ray_five_halves, if_pos (by norm_num), hd]

lemma root5_pow (G : PowerSeries ℚ) (hG : PowerSeries.constantCoeff G = 1) :
    PowerSeries.constantCoeff (root5 G) = 1 ∧ root5 G ^ 5 = G := by
  rw [root5, dif_pos hG]; exact (exists_root5 G hG).choose_spec

/-! ## The substitution `ι5 : X ↦ x, Y ↦ y⁵` -/

def ι5v : Fin 2 → B := ![X 0, X 1 ^ 5]

lemma subVec_ι5v : SubVec ι5v := by
  intro i; fin_cases i
  · exact ord_X 0
  · show Ord 1 (X 1 ^ 5 : B); rw [pow_succ]; exact (ord_X 1).mul_left _

def ι5 (h : B) : B := subst ι5v h

lemma ι5_X0 : ι5 (X 0) = X 0 := subst_X' _ subVec_ι5v 0
lemma ι5_X1 : ι5 (X 1) = X 1 ^ 5 := subst_X' _ subVec_ι5v 1

/-- The B-wall function corresponding to the C-wall function `G` on the C-ray of slope `σ`. -/
def trans5 (σ : Slope) (G : PowerSeries ℚ) : PowerSeries ℚ :=
  if 5 ∣ (ray σ).1 then PowerSeries.expand 5 (by norm_num) G else root5 G

lemma fam5_Lup5 (φ : Slope → PowerSeries ℚ) (σ : Slope) : fam5 φ (Lup5 σ) = trans5 σ (φ σ) := by
  rw [fam5, trans5, Ldown5_Lup5, ray_Lup5]
  have hc := ray_coprime σ
  by_cases h : 5 ∣ (ray σ).1
  · simp only [if_pos h, if_neg (not_dvd_of_coprime hc h)]
  · simp only [if_neg h, dvd_mul_right, if_true]

lemma trans5_cc (σ : Slope) {G : PowerSeries ℚ} (hG : PowerSeries.constantCoeff G = 1) :
    PowerSeries.constantCoeff (trans5 σ G) = 1 := by
  unfold trans5; split_ifs
  · rw [PowerSeries.constantCoeff_expand, hG]
  · exact (root5_pow G hG).1

lemma ι5_rayMono (σ : Slope) :
    ι5 (rayMono σ) = rayMono (Lup5 σ) ^ (if 5 ∣ (ray σ).1 then 5 else 1) := by
  rw [ι5, rayMono_eq, rayMono_eq, subst_monomial' _ subVec_ι5v, monomial_pow, monomial_eq_XX,
    one_smul, one_pow, map_one (C (σ := Fin 2) (R := ℚ)), one_mul]
  simp only [ι5v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Finsupp.smul_apply, rvec_apply0, rvec_apply1, ray_Lup5, smul_eq_mul]
  split_ifs with h
  · obtain ⟨d', hd'⟩ := h
    rw [hd', Nat.mul_div_cancel_left _ (by norm_num), ← pow_mul]; try ring
  · rw [← pow_mul]; try ring

lemma ι5_rayEval (σ : Slope) (G : PowerSeries ℚ) :
    ι5 (rayEval σ G) = rayEval (Lup5 σ)
      (if 5 ∣ (ray σ).1 then PowerSeries.expand 5 (by norm_num) G else G) := by
  rw [ι5, rayEval, PowerSeries.subst_def, subst_comp_subst_apply
    (hasSubst_rayMono σ).const subVec_ι5v.hasSubst]
  have h1 : (fun _ : Unit => subst ι5v (rayMono σ)) = fun _ =>
      rayMono (Lup5 σ) ^ (if 5 ∣ (ray σ).1 then 5 else 1) := funext fun _ => ι5_rayMono σ
  rw [h1, ← PowerSeries.subst_def]
  split_ifs with h
  · rw [rayEval, PowerSeries.expand_apply, PowerSeries.subst_comp_subst_apply
      (PowerSeries.HasSubst.X_pow (by norm_num)) (hasSubst_rayMono _),
      PowerSeries.subst_pow (hasSubst_rayMono _), PowerSeries.subst_X (hasSubst_rayMono _)]
  · rw [pow_one, rayEval]

lemma inv_pow_of {a : B} (ha : a * a⁻¹ = 1) (n : ℕ) : (a ^ n)⁻¹ = (a⁻¹) ^ n :=
  inv_eq_of_mul (by rw [← mul_pow, ha, one_pow])

/-- `ι5` intertwines the C-wall `(σ, G)` with the B-wall `(Lup5 σ, trans5 σ G)`. -/
lemma ι5_wall (σ : Slope) {G : PowerSeries ℚ} (hG : PowerSeries.constantCoeff G = 1) (h : B) :
    ι5 (wall σ G h) = wall (Lup5 σ) (trans5 σ G) (ι5 h) := by
  have hH := trans5_cc σ hG
  rw [ι5, ι5, wall_eq, wall_eq, subst_comp_subst_apply (subVec_wv σ G).hasSubst
    subVec_ι5v.hasSubst, subst_comp_subst_apply subVec_ι5v.hasSubst (subVec_wv _ _).hasSubst]
  congr 1
  have hFB := (ord_rayEval_sub_one (Lup5 σ) hH).mono (rlen_pos _)
  have hu : rayEval (Lup5 σ) (trans5 σ G) * (rayEval (Lup5 σ) (trans5 σ G))⁻¹ = 1 :=
    mul_inv_of_cc hFB
  have hcc : constantCoeff (rayEval σ G ^ (ray σ).1) ≠ 0 := by
    have := ord_one_iff.mp (ord_pow_sub_one ((ord_rayEval_sub_one σ hG).mono (rlen_pos _)) (ray σ).1)
    rw [map_sub, map_one, sub_eq_zero] at this; rw [this]; norm_num
  have hcop := ray_coprime σ
  have hι : ∀ g : B, subst ι5v g = ι5 g := fun _ => rfl
  -- `ι5 (rayEval σ G) = F_B ^ γ'`
  have hF : ι5 (rayEval σ G) = rayEval (Lup5 σ) (trans5 σ G) ^ (if 5 ∣ (ray σ).1 then 1 else 5) := by
    rw [ι5_rayEval]
    unfold trans5
    split_ifs
    · rw [pow_one]
    · rw [show rayEval (Lup5 σ) G = rayEval (Lup5 σ) (root5 G ^ 5) by rw [(root5_pow G hG).2],
        rayEval, rayEval, PowerSeries.subst_pow (hasSubst_rayMono _)]
  funext i; fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [show ι5v 0 = X 0 from rfl, subst_X' _ (subVec_wv _ _)]
    simp only [wv, Matrix.cons_val_zero]
    rw [subst_mul subVec_ι5v.hasSubst, subst_pow subVec_ι5v.hasSubst, subst_X' _ subVec_ι5v, hι,
      hF, ray_Lup5]
    simp only [ι5v, Matrix.cons_val_zero]
    split_ifs <;> simp [← pow_mul, mul_comm]
  · simp only [Fin.mk_one, Fin.isValue]
    rw [show ι5v 1 = X 1 ^ 5 from rfl, subst_pow (subVec_wv _ _).hasSubst, subst_X' _ (subVec_wv _ _)]
    simp only [wv, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [subst_mul subVec_ι5v.hasSubst, subst_X' _ subVec_ι5v, subst_inv' subVec_ι5v.hasSubst hcc,
      subst_pow subVec_ι5v.hasSubst, hι, hF, ray_Lup5]
    simp only [ι5v, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    set FB := rayEval (Lup5 σ) (trans5 σ G)
    split_ifs with h5
    · obtain ⟨d', hd'⟩ := h5
      rw [hd', Nat.mul_div_cancel_left _ (by norm_num), pow_one, mul_pow]
      simp only []
      rw [← inv_pow_of (mul_inv_of_cc (ord_pow_sub_one hFB d')) 5, ← pow_mul, mul_comm d' 5]
    · rw [mul_pow]
      simp only []
      rw [← inv_pow_of (mul_inv_of_cc (ord_pow_sub_one hFB (ray σ).1)) 5, ← pow_mul, ← pow_mul,
        mul_comm 5 (ray σ).1]

lemma ι5_prodL (φ : Slope → PowerSeries ℚ) (hφ : ∀ s, PowerSeries.constantCoeff (φ s) = 1)
    (L : List Slope) (h : B) : ι5 (prodL φ L h) = prodL (fam5 φ) (L.map Lup5) (ι5 h) := by
  induction L with
  | nil => rw [prodL_nil, List.map_nil, prodL_nil]
  | cons σ L ih => rw [prodL_cons, List.map_cons, prodL_cons, ι5_wall σ (hφ σ), fam5_Lup5, ih]

lemma fam5_cc {φ : Slope → PowerSeries ℚ} (hφ : ∀ s, PowerSeries.constantCoeff (φ s) = 1)
    (τ : Slope) : PowerSeries.constantCoeff (fam5 φ τ) = 1 := by
  unfold fam5; split_ifs
  · exact (root5_pow _ (hφ _)).1
  · rw [PowerSeries.constantCoeff_expand, hφ]

/-- The transported products at C-level `5N` and the B-products at level `N` agree mod `𝔪^N`. -/
lemma lattice_compare {φ : Slope → PowerSeries ℚ} (hφ : ∀ s, PowerSeries.constantCoeff (φ s) = 1)
    (N : ℕ) {g : B} (hg : Ord 1 g) :
    EqMod N (prodL (fam5 φ) (((slopesBelow (5 * N)).sort (· ≤ ·)).map Lup5) g)
      (prodL (fam5 φ) ((slopesBelow N).sort (· ≤ ·)) g) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; intro e he; omega
  set L' := ((slopesBelow (5 * N)).sort (· ≤ ·)).map Lup5
  have hc := fam5_cc hφ
  set cN : Slope → PowerSeries ℚ := fun s => if rlen s < N then fam5 φ s else 1 with hcNdef
  have hcN : ∀ s, PowerSeries.constantCoeff (cN s) = 1 := fun s => by
    rw [hcNdef]; dsimp only; split_ifs
    · exact hc s
    · simp
  have hag : Agree N (fam5 φ) cN := by
    intro s j hj
    rw [hcNdef]; dsimp only
    split_ifs with h
    · rfl
    · have : j = 0 := by
        by_contra hj0; have : rlen s ≤ j * rlen s := Nat.le_mul_of_pos_left _ (by omega)
        omega
      subst this
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hc s]; simp
  have h1 := prodL_weak_pert hc hcN hN hag L' hg
  set p : Slope → Bool := fun s => decide (rlen s < N)
  have h2 : prodL cN L' g = prodL (fam5 φ) (L'.filter p) g :=
    prodL_filter (fam5 φ) cN p (fun s hs => by rw [hcNdef]; dsimp only; rw [if_pos (of_decide_eq_true hs)])
      (fun s hs => by rw [hcNdef]; dsimp only; rw [if_neg (of_decide_eq_false hs)]) L' g
  have h4 : L'.filter p = (slopesBelow N).sort (· ≤ ·) := by
    refine List.Perm.eq_of_pairwise' (r := fun a b : Slope => a ≤ b) ?_ ?_ ?_
    · exact List.Pairwise.filter _ (List.Pairwise.map _ (fun a b h => Lup5_mono h)
        (Finset.pairwise_sort _ _))
    · exact Finset.pairwise_sort _ _
    · rw [List.perm_ext_iff_of_nodup (((Finset.sort_nodup _ _).map Lup5_injective).filter _)
        (Finset.sort_nodup _ _)]
      intro τ
      simp only [L', p, List.mem_filter, List.mem_map, Finset.mem_sort, mem_slopesBelow,
        decide_eq_true_eq]
      constructor
      · rintro ⟨⟨σ, -, rfl⟩, h⟩; exact h
      · intro h
        refine ⟨⟨Ldown5 τ, ?_, Lup5_Ldown5 τ⟩, h⟩
        have := rlen_Ldown5_le τ; omega
  rw [← h4, ← h2]
  exact h1.mono' (by omega)

/-- From agreement on `y⁵` (at every order) to agreement on `y`. -/
lemma eqMod_y5 {c f : Slope → PowerSeries ℚ} (hc : ∀ s, PowerSeries.constantCoeff (c s) = 1)
    (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1) (L : List Slope)
    (hy5 : ∀ N, EqMod N (orderedProd c N (X 1 ^ 5)) (prodL f L (X 1 ^ 5))) (N : ℕ) :
    EqMod N (orderedProd c N (X 1)) (prodL f L (X 1)) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; intro e he; omega
  have hstab := orderedProd_stab hc (show N ≤ N + 4 by omega) 1
  refine hstab.symm'.trans' ?_
  obtain ⟨b, hb, eP⟩ := prodL_unip hc ((slopesBelow (N + 4)).sort (· ≤ ·)) 1
  obtain ⟨b', hb', eQ⟩ := prodL_unip hf L 1
  have h := eqMod_iff.mp (hy5 (N + 4))
  have e5 : (X 1 ^ 5 : B) = X 1 * (X 1 * (X 1 * (X 1 * X 1))) := by ring
  rw [e5, orderedProd_eq, prodL_mul', prodL_mul', prodL_mul', prodL_mul', prodL_mul', prodL_mul',
    prodL_mul', prodL_mul', eP, eQ] at h
  set W := (1 + b) ^ 4 + (1 + b) ^ 3 * (1 + b') + (1 + b) ^ 2 * (1 + b') ^ 2
    + (1 + b) * (1 + b') ^ 3 + (1 + b') ^ 4 with hW
  have ef : X 1 * (1 + b) * (X 1 * (1 + b) * (X 1 * (1 + b) * (X 1 * (1 + b) * (X 1 * (1 + b)))))
      - X 1 * (1 + b') * (X 1 * (1 + b') * (X 1 * (1 + b') * (X 1 * (1 + b') * (X 1 * (1 + b')))))
      = X 1 * (X 1 * (X 1 * (X 1 * (X 1 * ((b - b') * W))))) := by rw [hW]; ring
  rw [ef, show N + 4 = (N - 1) + 1 + 1 + 1 + 1 + 1 by omega] at h
  have h' := ord_of_X_mul 1 (ord_of_X_mul 1 (ord_of_X_mul 1 (ord_of_X_mul 1 (ord_of_X_mul 1 h))))
  have hWc : constantCoeff W ≠ 0 := by
    have h0 := ord_one_iff.mp hb
    have h0' := ord_one_iff.mp hb'
    rw [hW]; simp [h0, h0']; norm_num
  have hWu : W⁻¹ * W = 1 := by rw [mul_comm]; exact MvPowerSeries.mul_inv_cancel _ hWc
  have hbb : Ord (N - 1) (b - b') := by
    have : b - b' = W⁻¹ * ((b - b') * W) := by
      rw [mul_comm (b - b'), ← mul_assoc, hWu, one_mul]
    rw [this]; exact h'.mul_left _
  rw [eqMod_iff, orderedProd_eq, eP, eQ]
  have : X 1 * (1 + b) - X 1 * (1 + b') = X 1 * (b - b') := by ring
  rw [this, show N = 1 + (N - 1) by omega]
  exact (ord_X 1).mul hbb

/-! ## Consistency of the transported family -/

/-- The transported family is consistent for `D(1+x, 1+y⁵)`. -/
lemma transport5_consistent (φ : Slope → PowerSeries ℚ)
    (hφ : IsConsistentFamily ((1 + PowerSeries.X) ^ 5) (1 + PowerSeries.X) φ) :
    IsConsistentFamily (1 + PowerSeries.X) (1 + PowerSeries.X ^ 5) (fam5 φ) := by
  obtain ⟨hφcc, hφf⟩ := hφ
  have hc := fam5_cc hφcc
  -- the B-side left-hand side as a two-wall product
  set famLB : Slope → PowerSeries ℚ := fun s =>
    if s = ⊤ then 1 + PowerSeries.X ^ 5 else 1 + PowerSeries.X with hLBdef
  have hLBcc : ∀ s, PowerSeries.constantCoeff (famLB s) = 1 := fun s => by
    rw [hLBdef]; dsimp only; split_ifs <;> simp
  have hLB : ∀ h : B, prodL famLB [⊤, ((0 : ℚ≥0) : Slope)] h =
      wall ⊤ (1 + PowerSeries.X ^ 5) (wall ((0 : ℚ≥0) : Slope) (1 + PowerSeries.X) h) := by
    intro h
    rw [prodL_cons, prodL_cons, prodL_nil, hLBdef]
    dsimp only
    rw [if_pos rfl, if_neg (WithTop.coe_ne_top)]
  -- the C-side left-hand side transports to the B-side one
  have hLup_top : Lup5 ⊤ = ⊤ := by simp [Lup5, ray_top', slopeOf]
  have hLup_zero : Lup5 ((0 : ℚ≥0) : Slope) = ((0 : ℚ≥0) : Slope) := by
    simp [Lup5, ray_zero', slopeOf]
  have htr_top : trans5 ⊤ (1 + PowerSeries.X) = 1 + PowerSeries.X ^ 5 := by
    rw [trans5, ray_top', if_pos (dvd_zero 5), map_add, map_one, PowerSeries.expand_X]
  have htr_zero : trans5 ((0 : ℚ≥0) : Slope) ((1 + PowerSeries.X) ^ 5) = 1 + PowerSeries.X := by
    rw [trans5, ray_zero', if_neg (by norm_num)]
    have h := root5_pow ((1 + PowerSeries.X : PowerSeries ℚ) ^ 5) (by simp)
    exact pow5_injective h.1 (by simp) h.2
  have hLhs : ∀ h : B, ι5 (wall ⊤ (1 + PowerSeries.X)
      (wall ((0 : ℚ≥0) : Slope) ((1 + PowerSeries.X) ^ 5) h)) =
      prodL famLB [⊤, ((0 : ℚ≥0) : Slope)] (ι5 h) := by
    intro h
    rw [ι5_wall ⊤ (by simp), ι5_wall _ (by simp), hLup_top, hLup_zero, htr_top, htr_zero, hLB]
  -- (A) agreement on `ι5 X j`
  have hA : ∀ N (j : Fin 2), EqMod N (orderedProd (fam5 φ) N (ι5 (X j)))
      (prodL famLB [⊤, ((0 : ℚ≥0) : Slope)] (ι5 (X j))) := by
    intro N j
    have h1 := lattice_compare hφcc N (g := ι5 (X j)) ((ord_X j).subst subVec_ι5v)
    have h2 := ι5_prodL φ hφcc ((slopesBelow (5 * N)).sort (· ≤ ·)) (X j)
    have h3 : EqMod (5 * N) (ι5 (prodL φ ((slopesBelow (5 * N)).sort (· ≤ ·)) (X j)))
        (ι5 (wall ⊤ (1 + PowerSeries.X) (wall ((0 : ℚ≥0) : Slope) ((1 + PowerSeries.X) ^ 5) (X j)))) :=
      subst_congr_arg (by rw [← orderedProd_eq]; exact hφf (5 * N) j) subVec_ι5v
    rw [h2, hLhs] at h3
    rw [orderedProd_eq]
    exact h1.symm'.trans' (h3.mono' (by omega))
  have hx : ∀ N, EqMod N (orderedProd (fam5 φ) N (X 0))
      (prodL famLB [⊤, ((0 : ℚ≥0) : Slope)] (X 0)) := fun N => by
    have := hA N 0; rwa [ι5_X0] at this
  have hy5 : ∀ N, EqMod N (orderedProd (fam5 φ) N (X 1 ^ 5))
      (prodL famLB [⊤, ((0 : ℚ≥0) : Slope)] (X 1 ^ 5)) := fun N => by
    have := hA N 1; rwa [ι5_X1] at this
  have hy := eqMod_y5 hc hLBcc _ hy5
  refine ⟨hc, fun N i => ?_⟩
  rw [← hLB]
  fin_cases i
  · exact hx N
  · exact hy N

end ErsConj13
