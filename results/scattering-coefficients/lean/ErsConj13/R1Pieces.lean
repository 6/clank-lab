import ErsConj13.ScatDefs
import ErsConj13.Pieces
import ErsConj13.Existence
import ErsConj13.KS
import ErsConj13.KSPoisson
import ErsConj13.KSExist
import ErsConj13.R1Consistent
import ErsConj13.R1Real

/-!
# Realization: from `D₅` to the Main Lemma

Route (forward substitution `u = x`, `w = xy`):
1. the ascending factorization (Kontsevich–Soibelman) of `T⁵` on `A = ℚ⟦u,w⟧`:
   existence for Poisson, unipotent automorphisms (`factor_exists`), uniqueness for any target
   (`factor_unique`);
2. transport by `ι : u ↦ x, w ↦ xy` (exponents `(p,q) ↦ (p+q, q)`), which maps A-walls to B-walls
   on the cone `q ≤ p`, `T ↦ XZ`; with the pentagon `Y X⁵ = (XZ)⁵ Y` this gives a consistent
   family for `D₅` (`transport_consistent`), whose ray-(2,1) function is the A-diagonal function;
3. the realization of the Main Lemma's hypotheses: `g_<`, `g_>` are the (levelwise limits of the)
   products of the A-walls of slope `< 1` and `> 1` (`realization`).
-/

noncomputable section

namespace ErsConj13

open Scat MvPowerSeries

/-- `g` is factored by the family `f`: ray functions with constant term 1 and, for every `N`, the
ascending product over `r₁ + r₂ < N` agrees with `g` modulo `𝔪^N` on the generators. -/
def IsFactorization (g : B → B) (f : Slope → PowerSeries ℚ) : Prop :=
  (∀ s, PowerSeries.constantCoeff (f s) = 1) ∧
  ∀ N : ℕ, ∀ i : Fin 2, EqMod N (orderedProd f N (X i)) (g (X i))

lemma isConsistentFamily_iff (P₁ P₂ : PowerSeries ℚ) (f : Slope → PowerSeries ℚ) :
    IsConsistentFamily P₁ P₂ f ↔ IsFactorization (wall ⊤ P₂ ∘ wall (0 : ℚ≥0) P₁) f := Iff.rfl

/-! ## Walls are Poisson automorphisms -/

lemma rayEval_one_add_X (s : Slope) : rayEval s (1 + PowerSeries.X) = 1 + rayMono s := by
  rw [rayEval, ← map_one (PowerSeries.C (R := ℚ)), PowerSeries.subst_add (hasSubst_rayMono s),
    PowerSeries.subst_C, PowerSeries.subst_X (hasSubst_rayMono s)]
  simp

lemma rayMono_zero : rayMono ((0 : ℚ≥0) : Slope) = X 0 := by
  rw [rayMono, ray_zero']; simp [X_def]
lemma rayMono_top : rayMono (⊤ : Slope) = X 1 := by
  rw [rayMono, ray_top']; simp [X_def]
@[simp] lemma rayMono_zero'' : rayMono (0 : Slope) = X 0 := by
  rw [rayMono, ray_zero'']; simp [X_def]

lemma wv_zero_one_add_X :
    wv ((0 : ℚ≥0) : Slope) (1 + PowerSeries.X) = ![X 0, X 1 * (1 + X 0)⁻¹] := by
  funext i; fin_cases i <;> simp [wv, rayEval_one_add_X]

lemma wv_top_one_add_X : wv (⊤ : Slope) (1 + PowerSeries.X) = ![X 0 * (1 + X 1), X 1] := by
  funext i; fin_cases i <;> simp [wv, ray_top', rayEval_one_add_X, rayMono_top]

/-- `T = θ_u ∘ θ_w` as walls (slope 0 then `⊤`). -/
lemma Tmap_eq_walls (f : A) :
    Tmap f = wall ((0 : ℚ≥0) : Slope) (1 + PowerSeries.X) (wall ⊤ (1 + PowerSeries.X) f) := by
  show subst Ta f = _
  have hv := subVec_wv ((0 : ℚ≥0) : Slope) (1 + PowerSeries.X)
  rw [wall_eq, wall_eq, subst_comp_subst_apply (subVec_wv _ _).hasSubst hv.hasSubst]
  rw [wv_zero_one_add_X] at hv ⊢
  rw [wv_top_one_add_X]
  congr 1
  funext i
  have h1 : subst (![X 0, X 1 * (1 + X 0)⁻¹] : Fin 2 → B) (1 : A) = 1 := by
    simpa using subst_C' (![X 0, X 1 * (1 + X 0 : B)⁻¹] : Fin 2 → B) 1
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [subst_mul hv.hasSubst, subst_add hv.hasSubst, subst_X' _ hv, subst_X' _ hv, h1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    show u * (1 + u + w) * (1 + u)⁻¹ = _
    linear_combination u * hI
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [subst_X' _ hv]
    rfl

lemma Tmap_isPoisson : IsPoisson Tmap := by
  intro f g
  rw [Tmap_eq_walls, Tmap_eq_walls, Tmap_eq_walls, wall_bracket _ (by simp), wall_bracket _ (by simp)]

/-! ## Ordered factorization (Kontsevich–Soibelman) -/

/-- Uniqueness: a factorization of a given map is unique. -/
lemma factor_unique (g : B → B) (f f' : Slope → PowerSeries ℚ)
    (hf : IsFactorization g f) (hf' : IsFactorization g f') : f = f' :=
  factor_unique_aux g f f' hf.1 hf'.1 hf.2 hf'.2

/-- Existence, for a Poisson automorphism with `g x ∈ x(1 + 𝔪)` and `g y ∈ y(1 + 𝔪)`. -/
lemma factor_exists (g : B ≃+* B) (hg : IsPoisson g)
    (hx : ∃ a, constantCoeff a = 0 ∧ g (X 0) = X 0 * (1 + a))
    (hy : ∃ a, constantCoeff a = 0 ∧ g (X 1) = X 1 * (1 + a)) :
    ∃ f, IsFactorization g f := by
  obtain ⟨a0, ha0, e0⟩ := hx
  obtain ⟨a1, ha1, e1⟩ := hy
  have hG : GenHyp g := {
    h0 := ⟨a0, ord_one_iff.mpr ha0, e0⟩
    h1 := ⟨a1, ord_one_iff.mpr ha1, e1⟩
    hb := by rw [← hg, bracket_X0_X1, map_mul] }
  obtain ⟨F, hF, hFg⟩ := factor_exists_aux hG
  exact ⟨F, hF, hFg⟩

/-! ## `T⁵` -/

/-- `T⁵` as a ring automorphism. -/
def T5 : A ≃+* A := Tmap.trans (Tmap.trans (Tmap.trans (Tmap.trans Tmap)))

lemma T5_apply (f : A) : T5 f = (⇑Tmap)^[5] f := rfl

lemma T5_isPoisson : IsPoisson T5 := by
  intro f g
  simp only [T5_apply, Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
  rw [Tmap_isPoisson, Tmap_isPoisson, Tmap_isPoisson, Tmap_isPoisson, Tmap_isPoisson]

lemma Tmap_unip (i : Fin 2) {b : A} (hb : Ord 1 b) :
    ∃ b', Ord 1 b' ∧ Tmap (X i * (1 + b)) = X i * (1 + b') := by
  rw [Tmap_eq_walls]
  obtain ⟨b1, hb1, e1⟩ := wall_unip (⊤ : Slope) (f := 1 + PowerSeries.X) (by simp) (i := i) hb
  rw [e1]
  exact wall_unip _ (by simp) hb1

lemma T5_unipotent :
    (∃ a, constantCoeff a = 0 ∧ T5 (X 0) = X 0 * (1 + a)) ∧
    (∃ a, constantCoeff a = 0 ∧ T5 (X 1) = X 1 * (1 + a)) := by
  have key : ∀ i : Fin 2, ∀ n : ℕ, ∃ a, Ord 1 a ∧ (⇑Tmap)^[n] (X i) = X i * (1 + a) := by
    intro i n
    induction n with
    | zero => exact ⟨0, Ord.zero 1, by simp⟩
    | succ n ih =>
      obtain ⟨a, ha, e⟩ := ih
      rw [Function.iterate_succ_apply', e]
      exact Tmap_unip i ha
  constructor
  · obtain ⟨a, ha, e⟩ := key 0 5; exact ⟨a, ord_one_iff.mp ha, e⟩
  · obtain ⟨a, ha, e⟩ := key 1 5; exact ⟨a, ord_one_iff.mp ha, e⟩

/-! ## Transport to `D₅` -/

/-- The B-family built from an A-family: the cone ray `(P, Q)` (`Q ≤ P`) carries the A-function of
`(P − Q, Q)`, the ray `(0,1)` carries `1 + y`, the other rays carry `1`. -/
def transportFam (φ : Slope → PowerSeries ℚ) (σ : Slope) : PowerSeries ℚ :=
  if σ ≤ ((1 : ℚ≥0) : Slope) then φ (Ldown σ) else if σ = ⊤ then 1 + PowerSeries.X else 1

lemma ray_half : ray ((1 / 2 : ℚ≥0) : Slope) = (2, 1) := by
  rw [ray_coe', Prod.mk.injEq]
  constructor
  · rw [← NNRat.den_coe]; push_cast; norm_num
  · have h : ((1 / 2 : ℚ≥0) : ℚ).num = 1 := by push_cast; norm_num
    rw [NNRat.num_coe] at h; exact_mod_cast h

lemma half_le_one : ((1 / 2 : ℚ≥0) : Slope) ≤ ((1 : ℚ≥0) : Slope) := by
  rw [le_one_iff, ray_half]; norm_num

lemma transportFam_half (φ : Slope → PowerSeries ℚ) :
    transportFam φ ((1 / 2 : ℚ≥0) : Slope) = φ ((1 : ℚ≥0) : Slope) := by
  rw [transportFam, if_pos half_le_one, Ldown, ray_half]
  congr 1
  simp [slopeOf]

lemma Lup_zero : Lup ((0 : ℚ≥0) : Slope) = ((0 : ℚ≥0) : Slope) := by
  rw [Lup, ray_zero']; simp [slopeOf]

lemma Lup_top : Lup (⊤ : Slope) = ((1 : ℚ≥0) : Slope) := by
  rw [Lup, ray_top']; simp [slopeOf]

lemma ι_T (h : B) : ι (Tmap h) =
    wall ((0 : ℚ≥0) : Slope) (1 + PowerSeries.X) (wall ((1 : ℚ≥0) : Slope) (1 + PowerSeries.X) (ι h)) := by
  rw [Tmap_eq_walls, ι_wall _ (by simp), Lup_zero, ι_wall _ (by simp), Lup_top]

lemma ι_T5 (h : B) : ι (T5 h) = prodL famOne Lpent (ι h) := by
  rw [T5_apply, prodL_Lpent]
  simp only [Function.iterate_succ, Function.comp_apply, Function.iterate_zero, id]
  rw [ι_T, ι_T, ι_T, ι_T, ι_T]

lemma ι_X0 : ι (X 0) = X 0 := subst_X' _ subVec_ιv 0
lemma ι_X1 : ι (X 1) = X 0 * X 1 := subst_X' _ subVec_ιv 1

lemma not_top_le_one : ¬ (⊤ : Slope) ≤ ((1 : ℚ≥0) : Slope) := by
  rw [top_le_iff]; exact WithTop.coe_ne_top.symm ∘ Eq.symm

lemma transport_consistent (φ : Slope → PowerSeries ℚ) (hφ : IsFactorization T5 φ) :
    IsConsistentFamily ((1 + PowerSeries.X) ^ 5) (1 + PowerSeries.X) (transportFam φ) := by
  obtain ⟨hφcc, hφf⟩ := hφ
  have htf : ∀ s, PowerSeries.constantCoeff (transportFam φ s) = 1 := fun s => by
    unfold transportFam; split_ifs <;> simp [hφcc]
  refine ⟨htf, fun N i => ?_⟩
  have hc := coneFam_cc hφcc
  -- (A) agreement on `ι X j`
  have hA : ∀ N (j : Fin 2), EqMod N (orderedProd (coneFam φ) N (ι (X j)))
      (prodL famOne Lpent (ι (X j))) := by
    intro N j
    have h1 := cone_compare hφcc N (g := ι (X j)) ((ord_X j).subst subVec_ιv)
    have h2 := ι_prodL φ (coneFam φ) hφcc ((slopesBelow N).sort (· ≤ ·))
      (fun σ _ => coneFam_Lup φ σ) (X j)
    have h3 : EqMod N (ι (prodL φ ((slopesBelow N).sort (· ≤ ·)) (X j))) (ι (T5 (X j))) :=
      subst_congr_arg (by rw [← orderedProd_eq]; exact hφf N j) subVec_ιv
    rw [ι_T5, h2] at h3
    rw [orderedProd_eq]
    exact h1.symm'.trans' h3
  have hx : ∀ N, EqMod N (orderedProd (coneFam φ) N (X 0)) (prodL famOne Lpent (X 0)) :=
    fun N => by have := hA N 0; rwa [ι_X0] at this
  have hxy : ∀ N, EqMod N (orderedProd (coneFam φ) N (X 0 * X 1))
      (prodL famOne Lpent (X 0 * X 1)) := fun N => by have := hA N 1; rwa [ι_X1] at this
  have hy := eqMod_y hc famOne_cc Lpent hx hxy
  -- (C) agreement on every element
  have hC : ∀ g, EqMod N (orderedProd (coneFam φ) N g) (prodL famOne Lpent g) := by
    intro g
    have hv : SubVec (fun j => prodL (coneFam φ) ((slopesBelow N).sort (· ≤ ·)) (X j)) := fun j => by
      obtain ⟨b, -, e⟩ := prodL_unip hc ((slopesBelow N).sort (· ≤ ·)) j
      beta_reduce; rw [e]; exact (ord_X j).mul_right _
    have hv' : SubVec (fun j => prodL famOne Lpent (X j)) := fun j => by
      obtain ⟨b, -, e⟩ := prodL_unip famOne_cc Lpent j
      beta_reduce; rw [e]; exact (ord_X j).mul_right _
    rw [orderedProd_eq, prodL_eq_subst hc, prodL_eq_subst famOne_cc]
    apply subst_congr_vec g hv hv'
    intro j; fin_cases j
    · have := hx N; rwa [orderedProd_eq] at this
    · have := hy N; rwa [orderedProd_eq] at this
  -- low orders
  rcases Nat.lt_or_ge N 2 with hN | hN
  · have h1 : Ord 1 (orderedProd (transportFam φ) N (X i)) := by
      obtain ⟨b, -, e⟩ := prodL_unip htf ((slopesBelow N).sort (· ≤ ·)) i
      rw [orderedProd_eq, e]; exact (ord_X i).mul_right _
    have h2 : Ord 1 (wall ⊤ (1 + PowerSeries.X) (wall ((0 : ℚ≥0) : Slope)
        ((1 + PowerSeries.X) ^ 5) (X i))) := by
      rw [wall_eq, wall_eq]
      exact ((ord_X i).subst (subVec_wv _ _)).subst (subVec_wv _ _)
    rw [eqMod_iff]
    rcases Nat.lt_or_ge N 1 with h0 | h0
    · rw [show N = 0 by omega]; exact ord_zero_left _
    · have hN1 : N = 1 := by omega
      subst hN1; exact h1.sub h2
  -- (D) splitting off the last wall `Y`
  set S := (slopesBelow N).sort (· ≤ ·) with hSdef
  have htop : ⊤ ∈ S := by
    rw [hSdef, Finset.mem_sort, mem_slopesBelow, rlen, ray_top']; omega
  have hsplit := split_top S (Finset.pairwise_sort _ _) (Finset.sort_nodup _ _) htop
  have hD : orderedProd (transportFam φ) N (X i) =
      orderedProd (coneFam φ) N (wall ⊤ (1 + PowerSeries.X) (X i)) := by
    rw [orderedProd_eq, orderedProd_eq, ← hSdef]
    conv_lhs => rw [hsplit]
    rw [prodL_append, prodL_cons, prodL_nil]
    have htt : transportFam φ ⊤ = 1 + PowerSeries.X := by
      rw [transportFam, if_neg not_top_le_one, if_pos rfl]
    rw [htt]
    rw [prodL_congr (f' := coneFam φ) (fun s hs => by
      have hs' : s ≠ ⊤ := by simpa using (List.mem_filter.mp hs).2
      unfold transportFam coneFam
      split_ifs <;> first | rfl | (exfalso; tauto))]
    exact (prodL_filter (coneFam φ) (coneFam φ) (fun s => decide (s ≠ ⊤)) (fun _ _ => rfl)
      (fun s hs => by
        have : s = ⊤ := by simpa using hs
        rw [this, coneFam, if_neg not_top_le_one]) S _).symm
  rw [hD, Y_X5]
  exact hC _

/-! ## Realization of the Main Lemma's hypotheses -/

lemma Tmap_iter_unip (i : Fin 2) (n : ℕ) : ∃ a, Ord 1 a ∧ (⇑Tmap)^[n] (X i) = X i * (1 + a) := by
  induction n with
  | zero => exact ⟨0, Ord.zero 1, by simp⟩
  | succ n ih =>
    obtain ⟨a, ha, e⟩ := ih
    rw [Function.iterate_succ_apply', e]
    exact Tmap_unip i ha

lemma Tmap_iter_subst (n : ℕ) (f : A) :
    (⇑Tmap)^[n] f = subst (fun i => (⇑Tmap)^[n] (X i)) f := by
  induction n generalizing f with
  | zero =>
    simp only [Function.iterate_zero, id]
    rw [show (fun i => (X i : A)) = X from rfl, subst_self']
  | succ n ih =>
    have hv : SubVec (fun i => (⇑Tmap)^[n] (X i)) := fun i => by
      obtain ⟨a, -, e⟩ := Tmap_iter_unip i n
      beta_reduce; rw [e]; exact (ord_X i).mul_right _
    have hTa : SubVec Ta := fun i => ord_one_iff.mpr (Ta_cc i)
    rw [Function.iterate_succ_apply', ih, show ∀ g, Tmap g = subst Ta g from fun _ => rfl,
      subst_comp_subst_apply hv.hasSubst hTa.hasSubst]
    congr 1; funext i
    rw [Function.iterate_succ_apply']; rfl

lemma theta_eq_wall (F : PowerSeries ℚ) (hF : PowerSeries.constantCoeff F = 1) (g : A) :
    thetaMap F hF g = wall ((1 : ℚ≥0) : Slope) F g := by
  show subst (thVec F F⁻¹) g = subst (wv ((1 : ℚ≥0) : Slope) F) g
  congr 1
  have hre : rayEval ((1 : ℚ≥0) : Slope) F = diag F := by
    rw [diag_eq_subst, rayEval, rayMono_one']
  have hinv : (diag F)⁻¹ = diag F⁻¹ := inv_eq_of_mul (diag_mul_diag_inv F hF)
  have hre' : rayEval (1 : Slope) F = diag F := by rw [← WithTop.coe_one]; exact hre
  funext i; fin_cases i
  · simp [thVec, wv, hre']
  · simp [thVec, wv, hre', hinv]

lemma realization (φ : Slope → PowerSeries ℚ) (hφ : IsFactorization T5 φ) :
    ∃ gl gr : A ≃+* A,
      (∀ f g, gl (bracket f g) = bracket (gl f) (gl g)) ∧
      (∀ f g, gr (bracket f g) = bracket (gr f) (gr g)) ∧
      (∀ m : Fin 2 →₀ ℕ, ∃ a ∈ OGe 1, gr (monomial m 1) = monomial m 1 * (1 + a)) ∧
      (∀ m : Fin 2 →₀ ℕ, ∃ a ∈ OLe (-1), gl.symm (monomial m 1) = monomial m 1 * (1 + a)) ∧
      (∀ f, (⇑Tmap)^[5] f = gl (thetaMap (φ ((1 : ℚ≥0) : Slope)) (hφ.1 _) (gr f))) := by
  obtain ⟨hφcc, hφf⟩ := hφ
  have hlt : ∀ s, PowerSeries.constantCoeff (famLt φ s) = 1 := fun s => by
    unfold famLt; split_ifs <;> simp [hφcc]
  have hgt : ∀ s, PowerSeries.constantCoeff (famGt φ s) = 1 := fun s => by
    unfold famGt; split_ifs <;> simp [hφcc]
  have hsgt : ∀ s, (ray s).1 < (ray s).2 ∨ famGt φ s = 1 := fun s => by
    unfold famGt; split_ifs with h
    · exact Or.inl ((one_lt_iff' s).mp h)
    · exact Or.inr rfl
  have hslt : ∀ s, (ray s).2 < (ray s).1 ∨ invFam (famLt φ) s = 1 := fun s => by
    unfold invFam famLt; split_ifs with h
    · exact Or.inl ((lt_one_iff' s).mp h)
    · right; rw [PowerSeries.inv_eq_iff_mul_eq_one (by simp)]; simp
  set gl := limEquiv (famLt φ) hlt
  set gr := limEquiv (famGt φ) hgt
  refine ⟨gl, gr, limEquiv_poisson _ hlt, limEquiv_poisson _ hgt, ?_, ?_, ?_⟩
  · intro m
    exact subst_monomial_mem_OGe (limV_mem_OGe hgt hsgt levelwise_sort) m
  · intro m
    exact subst_monomial_mem_OLe (limV_mem_OLe (invFam_cc hlt) hslt levelwise_rev) m
  · intro f
    set F := φ ((1 : ℚ≥0) : Slope)
    have hF := hφcc ((1 : ℚ≥0) : Slope)
    have key : ∀ N, 3 ≤ N → EqMod N ((⇑Tmap)^[5] f) (gl (thetaMap F hF (gr f))) := by
      intro N hN
      set S := (slopesBelow N).sort (· ≤ ·) with hSdef
      have h1S : ((1 : ℚ≥0) : Slope) ∈ S := by
        rw [hSdef, Finset.mem_sort, mem_slopesBelow, rlen, ray_one]; omega
      -- `T⁵ ≡ Π` on every element
      have hvT : SubVec (fun i => (⇑Tmap)^[5] (X i)) := fun i => by
        obtain ⟨a, -, e⟩ := Tmap_iter_unip i 5
        beta_reduce; rw [e]; exact (ord_X i).mul_right _
      have hvP : SubVec (fun i => prodL φ S (X i)) := fun i => by
        obtain ⟨b, -, e⟩ := prodL_unip hφcc S i
        beta_reduce; rw [e]; exact (ord_X i).mul_right _
      have E1 : EqMod N (prodL φ S f) ((⇑Tmap)^[5] f) := by
        rw [prodL_eq_subst hφcc, Tmap_iter_subst]
        exact subst_congr_vec f hvP hvT (fun i => by
          have := hφf N i; rwa [orderedProd_eq] at this)
      rw [prodL_split S (Finset.pairwise_sort _ _) (Finset.sort_nodup _ _) h1S] at E1
      -- `g_< θ g_> ≡ Π_< θ Π_>`
      have hvlt : SubVec (fun i => prodL (famLt φ) S (X i)) := fun i => by
        obtain ⟨b, -, e⟩ := prodL_unip hlt S i
        beta_reduce; rw [e]; exact (ord_X i).mul_right _
      have E3 := subst_limV_eqMod hlt levelwise_sort N (thetaMap F hF (gr f))
      have E4 : EqMod N (thetaMap F hF (gr f)) (thetaMap F hF (prodL (famGt φ) S f)) := by
        rw [theta_eq_wall, theta_eq_wall, wall_eq]
        exact subst_congr_arg (subst_limV_eqMod hgt levelwise_sort N f) (subVec_wv _ _)
      have E5 : EqMod N (prodL (famLt φ) S (thetaMap F hF (gr f)))
          (prodL (famLt φ) S (thetaMap F hF (prodL (famGt φ) S f))) := by
        rw [prodL_eq_subst hlt, prodL_eq_subst hlt (g := thetaMap F hF (prodL (famGt φ) S f))]
        exact subst_congr_arg E4 hvlt
      have E3' : EqMod N (gl (thetaMap F hF (gr f))) (prodL (famLt φ) S (thetaMap F hF (gr f))) :=
        E3
      simp only [theta_eq_wall] at E3' E5 ⊢
      exact (E3'.trans' E5 |>.trans' E1).symm'
    apply sub_eq_zero.mp
    apply eq_zero_of_ord_all
    intro N
    rw [← eqMod_iff]
    exact (key (N + 3) (by omega)).mono' (by omega)


end ErsConj13
