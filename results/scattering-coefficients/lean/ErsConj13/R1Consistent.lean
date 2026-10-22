import ErsConj13.R1Transport

/-!
# The transported family is a consistent family for `D₅`
-/

noncomputable section

namespace ErsConj13.Scat

open MvPowerSeries

/-! ## General list lemmas -/

lemma prodL_congr {f f' : Slope → PowerSeries ℚ} {L : List Slope} (h : ∀ s ∈ L, f s = f' s)
    (g : B) : prodL f L g = prodL f' L g := by
  induction L with
  | nil => rw [prodL_nil, prodL_nil]
  | cons s L ih =>
    rw [prodL_cons, prodL_cons, h s List.mem_cons_self,
      ih (fun t ht => h t (List.mem_cons_of_mem _ ht))]

lemma prodL_append (f : Slope → PowerSeries ℚ) (L L' : List Slope) (g : B) :
    prodL f (L ++ L') g = prodL f L (prodL f L' g) := by
  induction L with
  | nil => rw [List.nil_append, prodL_nil]
  | cons s L ih => rw [List.cons_append, prodL_cons, prodL_cons, ih]

lemma prodL_mul' {f : Slope → PowerSeries ℚ} (L : List Slope) (a b : B) :
    prodL f L (a * b) = prodL f L a * prodL f L b := by
  induction L with
  | nil => rw [prodL_nil, prodL_nil, prodL_nil]
  | cons s L ih =>
    rw [prodL_cons, prodL_cons, prodL_cons, ih, wall_eq]
    exact subst_mul (subVec_wv s (f s)).hasSubst _ _

lemma prodL_eq_subst {f : Slope → PowerSeries ℚ} (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1)
    (L : List Slope) (g : B) : prodL f L g = subst (fun i => prodL f L (X i)) g := by
  induction L generalizing g with
  | nil =>
    rw [prodL_nil, show (fun i => prodL f [] (X i : B)) = X from funext fun i => prodL_nil f _,
      subst_self']
  | cons s L ih =>
    have hv : SubVec (fun i => prodL f L (X i)) := fun i => by
      obtain ⟨b, -, e⟩ := prodL_unip hf L i; show Ord 1 (prodL f L (X i)); rw [e]
      exact (ord_X i).mul_right _
    rw [prodL_cons, ih, wall_eq, subst_comp_subst_apply hv.hasSubst (subVec_wv s (f s)).hasSubst]
    congr 1

lemma split_top (S : List Slope) (hS : S.Pairwise (· ≤ ·)) (hnd : S.Nodup) (ht : ⊤ ∈ S) :
    S = S.filter (fun s => decide (s ≠ ⊤)) ++ [⊤] := by
  induction S with
  | nil => simp at ht
  | cons a S ih =>
    by_cases ha : a = ⊤
    · subst ha
      have hS' : S = [] := by
        rcases S with _ | ⟨b, S⟩
        · rfl
        · exfalso
          have hb : (⊤ : Slope) ≤ b := (List.pairwise_cons.mp hS).1 b List.mem_cons_self
          have : b = ⊤ := top_le_iff.mp hb
          exact (List.nodup_cons.mp hnd).1 (this ▸ List.mem_cons_self)
      subst hS'; simp
    · have ht' : ⊤ ∈ S := by
        rcases List.mem_cons.mp ht with h | h
        · exact absurd h.symm ha
        · exact h
      rw [List.filter_cons, if_pos (by simpa using ha), List.cons_append]
      congr 1
      exact ih (List.pairwise_cons.mp hS).2 (List.nodup_cons.mp hnd).2 ht'


/-! ## The cone family -/

/-- The cone part of the transported family. -/
def coneFam (φ : Slope → PowerSeries ℚ) (σ : Slope) : PowerSeries ℚ :=
  if σ ≤ ((1 : ℚ≥0) : Slope) then φ (Ldown σ) else 1

lemma coneFam_cc {φ : Slope → PowerSeries ℚ} (hφ : ∀ s, PowerSeries.constantCoeff (φ s) = 1)
    (σ : Slope) : PowerSeries.constantCoeff (coneFam φ σ) = 1 := by
  unfold coneFam; split_ifs <;> simp [hφ]

lemma coneFam_Lup (φ : Slope → PowerSeries ℚ) (σ : Slope) : coneFam φ (Lup σ) = φ σ := by
  rw [coneFam, if_pos (Lup_le_one σ), Ldown_Lup]

lemma Lup_injective : Function.Injective Lup := fun a b h => by
  rw [← Ldown_Lup a, ← Ldown_Lup b, h]

lemma rlen_Ldown_le {τ : Slope} (h : τ ≤ ((1 : ℚ≥0) : Slope)) : rlen (Ldown τ) ≤ rlen τ := by
  rw [rlen, rlen, ray_Ldown h]; simp only; omega

/-- The transported A-product and the B-product over the cone agree to order `N`. -/
lemma cone_compare {φ : Slope → PowerSeries ℚ} (hφ : ∀ s, PowerSeries.constantCoeff (φ s) = 1)
    (N : ℕ) {g : B} (hg : Ord 1 g) :
    EqMod N (prodL (coneFam φ) (((slopesBelow N).sort (· ≤ ·)).map Lup) g)
      (prodL (coneFam φ) ((slopesBelow N).sort (· ≤ ·)) g) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; intro e he; omega
  set S := (slopesBelow N).sort (· ≤ ·)
  set L' := S.map Lup
  set c := coneFam φ
  have hc := coneFam_cc hφ
  set cN : Slope → PowerSeries ℚ := fun s =>
    if s ≤ ((1 : ℚ≥0) : Slope) ∧ rlen s < N then c s else 1 with hcNdef
  have hcN : ∀ s, PowerSeries.constantCoeff (cN s) = 1 := fun s => by
    rw [hcNdef]; dsimp only; split_ifs
    · exact hc s
    · simp
  have hag : Agree N c cN := by
    intro s j hj
    rw [hcNdef]; dsimp only
    split_ifs with h
    · rfl
    · by_cases h1 : s ≤ ((1 : ℚ≥0) : Slope)
      · have hs : N ≤ rlen s := by by_contra h2; exact h ⟨h1, by omega⟩
        have : j = 0 := by
          by_contra hj0; have : rlen s ≤ j * rlen s := Nat.le_mul_of_pos_left _ (by omega)
          omega
        subst this
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hc s]; simp
      · simp only [c, coneFam, if_neg h1]
  have h1 := prodL_weak_pert hc hcN hN hag L' hg
  set p : Slope → Bool := fun s => decide (s ≤ ((1 : ℚ≥0) : Slope) ∧ rlen s < N)
  have h2 : prodL cN L' g = prodL c (L'.filter p) g :=
    prodL_filter c cN p (fun s hs => by rw [hcNdef]; dsimp only; rw [if_pos (of_decide_eq_true hs)])
      (fun s hs => by rw [hcNdef]; dsimp only; rw [if_neg (of_decide_eq_false hs)]) L' g
  set q : Slope → Bool := fun s => decide (s ≤ ((1 : ℚ≥0) : Slope))
  have h3 : prodL c S g = prodL c (S.filter q) g :=
    prodL_filter c c q (fun _ _ => rfl)
      (fun s hs => by simp only [c, coneFam, q] at hs ⊢; rw [if_neg (of_decide_eq_false hs)]) S g
  have h4 : L'.filter p = S.filter q := by
    refine List.Perm.eq_of_pairwise' (r := fun a b : Slope => a ≤ b) ?_ ?_ ?_
    · exact List.Pairwise.filter _ (List.Pairwise.map _ (fun a b h => Lup_mono h)
        (Finset.pairwise_sort _ _))
    · exact List.Pairwise.filter _ (Finset.pairwise_sort _ _)
    · rw [List.perm_ext_iff_of_nodup (((Finset.sort_nodup _ _).map Lup_injective).filter _)
        ((Finset.sort_nodup _ _).filter _)]
      intro τ
      simp only [L', S, p, q, List.mem_filter, List.mem_map, Finset.mem_sort, mem_slopesBelow,
        decide_eq_true_eq]
      constructor
      · rintro ⟨⟨σ, -, rfl⟩, h1, h2⟩; exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩
        exact ⟨⟨Ldown τ, lt_of_le_of_lt (rlen_Ldown_le h1) h2, Lup_Ldown h1⟩, h1, h2⟩
  rw [h3, ← h4, ← h2]
  exact h1.mono' (by omega)


/-- From agreement on `x` and `xy` (at every order) to agreement on `y`. -/
lemma eqMod_y {c f : Slope → PowerSeries ℚ} (hc : ∀ s, PowerSeries.constantCoeff (c s) = 1)
    (hf : ∀ s, PowerSeries.constantCoeff (f s) = 1) (L : List Slope)
    (hx : ∀ N, EqMod N (orderedProd c N (X 0)) (prodL f L (X 0)))
    (hxy : ∀ N, EqMod N (orderedProd c N (X 0 * X 1)) (prodL f L (X 0 * X 1))) (N : ℕ) :
    EqMod N (orderedProd c N (X 1)) (prodL f L (X 1)) := by
  have hstab := orderedProd_stab hc (Nat.le_succ N) 1
  refine hstab.symm'.trans' ?_
  set P := orderedProd c (N + 1)
  obtain ⟨b, hb, eP⟩ := prodL_unip hc ((slopesBelow (N + 1)).sort (· ≤ ·)) 0
  rw [← orderedProd_eq] at eP
  have h1 := eqMod_iff.mp (hx (N + 1))
  have h2 := eqMod_iff.mp (hxy (N + 1))
  rw [orderedProd_eq, prodL_mul', ← orderedProd_eq, prodL_mul'] at h2
  rw [eqMod_iff]
  set D := P (X 1) - prodL f L (X 1)
  have e : X 0 * ((1 + b) * D) =
      (P (X 0) * P (X 1) - prodL f L (X 0) * prodL f L (X 1))
        - (P (X 0) - prodL f L (X 0)) * prodL f L (X 1) := by
    simp only [D, P] at *; rw [eP]; ring
  have h3 : Ord (N + 1) (X 0 * ((1 + b) * D)) := by
    rw [e]; exact h2.sub (h1.mul_right _)
  have h4 := ord_of_X_mul 0 h3
  have hu : (1 + b)⁻¹ * (1 + b) = 1 := by
    rw [mul_comm]; exact mul_inv_of_cc (by simpa using hb)
  have : D = (1 + b)⁻¹ * ((1 + b) * D) := by rw [← mul_assoc, hu, one_mul]
  rw [this]; exact h4.mul_left _

end ErsConj13.Scat
