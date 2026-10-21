import DS243.Basic

/-!
# The multiplier theorem and the fixed translate

Hall's first multiplier theorem, in the group ring `ℤ[A]` of a finite abelian group:
a prime `p` dividing `n = k - λ`, with `p > λ` and multiplication by `p` bijective on `A`,
is a numerical multiplier: `p • D = D + g` for some `g`.
For `G` and parameters (243,121,60) with `p = 61`, a translate of `D` is fixed by `61`.
-/

namespace DS243

open Finset AddMonoidAlgebra

section Generic

set_option linter.unusedSectionVars false

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- Number of ordered pairs `(a, b) ∈ D × D` with `a - b = g`, in any group. -/
def diffCountA (D : Finset A) (g : A) : ℕ :=
  ((D ×ˢ D).filter fun q => q.1 - q.2 = g).card

lemma diffCountA_eq_card_filter (D : Finset A) (g : A) :
    diffCountA D g = (D.filter fun a => a - g ∈ D).card := by
  unfold diffCountA
  refine card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    simp only [mem_filter, mem_product] at hp ⊢
    refine ⟨hp.1.1, ?_⟩
    have : p.1 - g = p.2 := by rw [← hp.2]; abel
    rw [this]; exact hp.1.2
  · intro p hp q hq h
    simp only [mem_filter, mem_product] at hp hq
    have h1 : p.2 = p.1 - g := by rw [← hp.2]; abel
    have h2 : q.2 = q.1 - g := by rw [← hq.2]; abel
    exact Prod.ext h (by rw [h1, h2, h])
  · intro a ha
    simp only [mem_filter] at ha
    exact ⟨(a, a - g), by simp [mem_product, ha.1, ha.2], rfl⟩

/-- Difference counts transfer along an injective `f` with `f (a - g') = f a - g`. -/
lemma diffCountA_image {f : A → A} (hf : Function.Injective f) (D : Finset A) {g g' : A}
    (hfg : ∀ a, f (a - g') = f a - g) :
    diffCountA (D.image f) g = diffCountA D g' := by
  rw [diffCountA_eq_card_filter, diffCountA_eq_card_filter,
    ← card_image_of_injective (D.filter fun a => a - g' ∈ D) hf]
  congr 1
  ext y
  rw [mem_filter]
  constructor
  · rintro ⟨hy, hyg⟩
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
    rw [← hfg, hf.mem_finset_image] at hyg
    exact mem_image_of_mem f (mem_filter.2 ⟨hx, hyg⟩)
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
    rw [mem_filter] at hx
    exact ⟨mem_image_of_mem f hx.1, by rw [← hfg]; exact mem_image_of_mem f hx.2⟩

/-- The total of all difference counts is `|D|²`. -/
lemma sum_diffCountA (D : Finset A) : ∑ g, diffCountA D g = D.card * D.card := by
  rw [← card_product]
  exact (card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)).symm

/-! ### The group ring toolkit -/

/-- Indicator element of a finite set in the group ring `R[A]`. -/
noncomputable def ind (R : Type*) [CommRing R] (X : Finset A) : AddMonoidAlgebra R A :=
  ∑ x ∈ X, single x 1

lemma coeff_ind (R : Type*) [CommRing R] (X : Finset A) (g : A) :
    (ind R X).coeff g = if g ∈ X then 1 else 0 := by
  simp [ind, coeff_sum, Finsupp.single_apply, Finset.sum_ite_eq']

lemma coeff_mul_fintype {R : Type*} [CommRing R] (x y : AddMonoidAlgebra R A) (g : A) :
    (x * y).coeff g = ∑ a, x.coeff a * y.coeff (g - a) := by
  rw [coeff_mul_antidiag x y g ((univ : Finset A).image fun a => (a, g - a))]
  · rw [sum_image]
    intro a _ b _ h
    simpa using congrArg Prod.fst h
  · intro p
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨a, rfl⟩; simp
    · intro h; exact ⟨p.1, by ext <;> simp [← h]⟩

lemma coeff_intCast_mul {R : Type*} [CommRing R] (z : ℤ) (x : AddMonoidAlgebra R A) (g : A) :
    ((z : AddMonoidAlgebra R A) * x).coeff g = z * x.coeff g := by
  rw [AddMonoidAlgebra.intCast_def, coeff_single_zero_mul]

lemma coeff_natCast_mul {R : Type*} [CommRing R] (z : ℕ) (x : AddMonoidAlgebra R A) (g : A) :
    ((z : AddMonoidAlgebra R A) * x).coeff g = z * x.coeff g := by
  rw [AddMonoidAlgebra.natCast_def, coeff_single_zero_mul]

/-- `ind` is injective on finsets. -/
lemma ind_injective {X Y : Finset A} (h : ind ℤ X = ind ℤ Y) : X = Y := by
  ext x
  have := congrArg (fun z => z.coeff x) h
  simp only [coeff_ind] at this
  by_cases hX : x ∈ X <;> by_cases hY : x ∈ Y <;> simp_all

/-- Translation: `X^g * ind X = ind (X + g)`. -/
lemma single_mul_ind (R : Type*) [CommRing R] (g : A) (X : Finset A) :
    single g 1 * ind R X = ind R (X.image (· + g)) := by
  unfold ind
  rw [mul_sum, sum_image (fun a _ b _ h => add_right_cancel h)]
  refine sum_congr rfl fun x _ => ?_
  rw [single_mul_single, one_mul, add_comm]

/-- `ind X * ind A = |X| * ind A`. -/
lemma ind_mul_univ (R : Type*) [CommRing R] (X : Finset A) :
    ind R X * ind R univ = (X.card : AddMonoidAlgebra R A) * ind R univ := by
  ext g
  rw [coeff_mul_fintype, coeff_natCast_mul]
  simp [coeff_ind]

lemma pow_mul_univ (R : Type*) [CommRing R] (X : Finset A) (m : ℕ) :
    ind R X ^ m * ind R univ = (X.card : AddMonoidAlgebra R A) ^ m * ind R univ := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, mul_assoc, ind_mul_univ, mul_left_comm, ih, pow_succ]; ring

/-- Frobenius in `(ZMod p)[A]`. -/
lemma frobenius_ind (p : ℕ) [Fact p.Prime] (X : Finset A)
    (hinj : Function.Injective fun x : A => p • x) :
    (ind (ZMod p) X) ^ p = ind (ZMod p) (X.image fun x => p • x) := by
  haveI : CharP (AddMonoidAlgebra (ZMod p) A) p :=
    charP_of_injective_algebraMap (R := ZMod p)
      (by
        intro a b h
        have := congrArg (fun z : AddMonoidAlgebra (ZMod p) A => z.coeff 0) h
        simpa [AddMonoidAlgebra.coe_algebraMap] using this) p
  unfold ind
  rw [sum_pow_char, sum_image (fun a _ b _ h => hinj h)]
  simp [single_pow]

/-- The conjugation `g ↦ -g` on `ℤ[A]`. -/
noncomputable def conj : AddMonoidAlgebra ℤ A ≃+* AddMonoidAlgebra ℤ A :=
  AddMonoidAlgebra.mapDomainRingEquiv ℤ (AddEquiv.neg A)

lemma coeff_conj (x : AddMonoidAlgebra ℤ A) (g : A) : (conj x).coeff g = x.coeff (-g) := by
  simp [conj, Finsupp.equivMapDomain_apply]

lemma conj_conj (x : AddMonoidAlgebra ℤ A) : conj (conj x) = x := by
  ext g; simp [coeff_conj]

lemma conj_univ : conj (ind ℤ (univ : Finset A)) = ind ℤ univ := by
  ext g; simp [coeff_conj, coeff_ind]

/-- `ind X * conj (ind Y)` counts `a ∈ X` with `a - g ∈ Y`. -/
lemma coeff_ind_mul_conj (X Y : Finset A) (g : A) :
    (ind ℤ X * conj (ind ℤ Y)).coeff g = ((X.filter fun a => a - g ∈ Y).card : ℤ) := by
  rw [coeff_mul_fintype]
  simp only [coeff_conj, coeff_ind, neg_sub, ite_mul, one_mul, zero_mul]
  rw [sum_ite_mem, univ_inter, sum_boole]

/-- A nonnegative `T` with `T * conj T = n² • 1` equals `n X^g`. -/
lemma eq_single_of_mul_conj (T : AddMonoidAlgebra ℤ A) (n : ℤ) (hn : 0 < n)
    (hpos : ∀ g, 0 ≤ T.coeff g)
    (h : T * conj T = (n ^ 2 : ℤ) • (1 : AddMonoidAlgebra ℤ A)) :
    ∃ g, T = single g n := by
  have hc : ∀ g, (T * conj T).coeff g = ∑ a, T.coeff a * T.coeff (a - g) := by
    intro g; rw [coeff_mul_fintype]; simp [coeff_conj]
  have h1 : ∀ g, (T * conj T).coeff g = if g = 0 then n ^ 2 else 0 := by
    intro g; rw [h]; simp [AddMonoidAlgebra.one_def, Finsupp.single_apply, eq_comm]
  have horth : ∀ a b, a ≠ b → T.coeff a * T.coeff b = 0 := by
    intro a b hab
    have hz := (hc (a - b)).symm.trans (h1 (a - b))
    rw [if_neg (sub_ne_zero.mpr hab)] at hz
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hpos i) (hpos _))).1 hz
    simpa using hall a (mem_univ a)
  have hsq := (hc 0).symm.trans (h1 0)
  simp only [sub_zero, if_true] at hsq
  obtain ⟨g, hg⟩ : ∃ g, T.coeff g ≠ 0 := by
    by_contra hne
    simp only [not_exists, not_not] at hne
    simp [hne] at hsq
    exact (pow_pos hn 2).ne' hsq.symm
  have hrest : ∀ a, a ≠ g → T.coeff a = 0 := by
    intro a ha
    rcases mul_eq_zero.1 (horth a g ha) with h | h
    · exact h
    · exact absurd h hg
  have hsum : ∑ a, T.coeff a * T.coeff a = T.coeff g * T.coeff g := by
    rw [Finset.sum_eq_single g (fun a _ ha => by simp [hrest a ha]) (by simp)]
  rw [hsum] at hsq
  have hgn : T.coeff g = n := by
    have h0 := hpos g
    nlinarith [sq_nonneg (T.coeff g - n), sq_nonneg (T.coeff g + n)]
  refine ⟨g, ?_⟩
  ext a
  by_cases ha : a = g
  · subst ha; simp [hgn]
  · simp [hrest a ha, Ne.symm ha]

/-- The group-ring form of the difference-set condition. -/
lemma ind_mul_conj (D : Finset A) (k lam : ℕ) (hk : D.card = k)
    (hdiff : ∀ g : A, g ≠ 0 → diffCountA D g = lam) :
    ind ℤ D * conj (ind ℤ D) =
      ((k : AddMonoidAlgebra ℤ A) - (lam : AddMonoidAlgebra ℤ A)) +
        (lam : AddMonoidAlgebra ℤ A) * ind ℤ univ := by
  ext g
  rw [coeff_ind_mul_conj, ← diffCountA_eq_card_filter]
  simp only [coeff_add, coeff_sub, Finsupp.add_apply, Finsupp.sub_apply, coeff_natCast_mul,
    coeff_ind, mem_univ, if_true, mul_one, coeff_natCast, Finsupp.single_apply]
  by_cases hg : g = 0
  · subst hg
    rw [diffCountA_eq_card_filter]
    simp [hk]
  · rw [hdiff g hg]
    simp [Ne.symm hg]

/-- Hall's first multiplier theorem (abelian, numerical-multiplier form). -/
theorem multiplier (D : Finset A) (k lam p : ℕ) [hp : Fact p.Prime]
    (hk : D.card = k) (hdiff : ∀ g : A, g ≠ 0 → diffCountA D g = lam)
    (hlam : lam < k) (hpn : p ∣ k - lam) (hplam : lam < p)
    (hpk : ((k : ZMod p)) ^ (p - 1) = 1)
    (hbij : Function.Bijective fun x : A => p • x) :
    ∃ g : A, D.image (fun x => p • x) = D.image (· + g) := by
  have hinj : Function.Injective fun x : A => p • x := hbij.1
  -- `p • D` is again a difference set with the same parameters.
  set Dp := D.image (fun x => p • x) with hDp
  have hDpk : Dp.card = k := by rw [hDp, card_image_of_injective _ hinj, hk]
  have hDpdiff : ∀ g : A, g ≠ 0 → diffCountA Dp g = lam := by
    intro g hg
    obtain ⟨g', rfl⟩ := hbij.2 g
    have hg' : g' ≠ 0 := by rintro rfl; exact hg (smul_zero _)
    rw [hDp, diffCountA_image hinj D (g' := g') (fun a => smul_sub p a g'), hdiff g' hg']
  -- Identities in `ℤ[A]`.
  have h1 := ind_mul_conj D k lam hk hdiff
  have h2 := ind_mul_conj Dp k lam hDpk hDpdiff
  have hc : ∀ X : Finset A, conj (ind ℤ X) * ind ℤ univ =
      (X.card : AddMonoidAlgebra ℤ A) * ind ℤ univ := by
    intro X
    have := congrArg conj (ind_mul_univ ℤ X)
    rwa [map_mul, map_mul, map_natCast, conj_univ] at this
  have h3 : ind ℤ Dp * ind ℤ univ = (k : AddMonoidAlgebra ℤ A) * ind ℤ univ := by
    rw [ind_mul_univ, hDpk]
  have h4 : conj (ind ℤ Dp) * ind ℤ univ = (k : AddMonoidAlgebra ℤ A) * ind ℤ univ := by
    rw [hc, hDpk]
  have h5 : ind ℤ D * ind ℤ univ = (k : AddMonoidAlgebra ℤ A) * ind ℤ univ := by
    rw [ind_mul_univ, hk]
  have h6 : conj (ind ℤ D) * ind ℤ univ = (k : AddMonoidAlgebra ℤ A) * ind ℤ univ := by
    rw [hc, hk]
  have h7 : ind ℤ (univ : Finset A) * ind ℤ univ =
      (Fintype.card A : AddMonoidAlgebra ℤ A) * ind ℤ univ := by
    rw [ind_mul_univ, card_univ]
  have h8 : (k : AddMonoidAlgebra ℤ A) ^ 2 * ind ℤ univ =
      ((k : AddMonoidAlgebra ℤ A) - (lam : AddMonoidAlgebra ℤ A) +
        (lam : AddMonoidAlgebra ℤ A) * (Fintype.card A : AddMonoidAlgebra ℤ A)) *
          ind ℤ univ := by
    linear_combination ind ℤ univ * h1 + (lam : AddMonoidAlgebra ℤ A) * h7 -
      ind ℤ D * h6 - (k : AddMonoidAlgebra ℤ A) * h5
  -- `T = p•D * (-D) - λ A` has coefficients divisible by `p`.
  set T : AddMonoidAlgebra ℤ A :=
    ind ℤ Dp * conj (ind ℤ D) - (lam : AddMonoidAlgebra ℤ A) * ind ℤ univ with hTdef
  set ψ := AddMonoidAlgebra.mapRingHom A (Int.castRingHom (ZMod p)) with hψ
  have hψind : ∀ X : Finset A, ψ (ind ℤ X) = ind (ZMod p) X := by
    intro X; simp [hψ, ind, map_sum, mapRingHom_single]
  have hcast : ∀ m : ℕ, (m : AddMonoidAlgebra (ZMod p) A) =
      algebraMap (ZMod p) (AddMonoidAlgebra (ZMod p) A) (m : ZMod p) :=
    fun m => (map_natCast _ m).symm
  have hkl : (k : ZMod p) = lam := by
    have : ((k - lam : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpn
    rwa [Nat.cast_sub hlam.le, sub_eq_zero] at this
  have hψT : ψ T = 0 := by
    have e1 : ψ (ind ℤ Dp) = ψ (ind ℤ D) ^ (p - 1) * ψ (ind ℤ D) := by
      rw [← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le, hψind, hψind, hDp,
        frobenius_ind p D hinj]
    have e2 : ψ (ind ℤ D * conj (ind ℤ D)) =
        (lam : AddMonoidAlgebra (ZMod p) A) * ind (ZMod p) univ := by
      rw [h1, map_add, map_sub, map_mul, map_natCast, map_natCast, hψind,
        hcast k, hcast lam, hkl, sub_self, zero_add]
    have e3 : ψ (ind ℤ D) ^ (p - 1) * ind (ZMod p) univ = ind (ZMod p) univ := by
      rw [hψind, pow_mul_univ, hk, hcast k, ← map_pow, hpk, map_one, one_mul]
    rw [hTdef, map_sub, map_mul, e1, mul_assoc, ← map_mul, e2, mul_left_comm, e3, map_mul,
      map_natCast, hψind, sub_self]
  have hTcoeff : ∀ g, T.coeff g = ((Dp.filter fun a => a - g ∈ D).card : ℤ) - lam := by
    intro g
    rw [hTdef]
    simp only [coeff_sub, Finsupp.sub_apply, coeff_ind_mul_conj, coeff_natCast_mul, coeff_ind,
      mem_univ, if_true, mul_one]
  have hdvd : ∀ g, (p : ℤ) ∣ T.coeff g := by
    intro g
    have := congrArg (fun x => x.coeff g) hψT
    simp only [hψ, coeff_mapRingHom, eq_intCast, coeff_zero, Finsupp.coe_zero,
      Pi.zero_apply] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
  -- Since `λ < p`, the coefficients of `T` are nonnegative.
  have hpos : ∀ g, 0 ≤ T.coeff g := by
    intro g
    obtain ⟨m, hm⟩ := hdvd g
    have h0 := hTcoeff g
    have hc0 : (0 : ℤ) ≤ ((Dp.filter fun a => a - g ∈ D).card : ℤ) := Nat.cast_nonneg _
    have hlp : (lam : ℤ) < p := by exact_mod_cast hplam
    rw [hm] at h0 ⊢
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
    have hm1 : -1 < m := by
      by_contra hcon
      nlinarith
    exact mul_nonneg hp0.le (by omega)
  -- `T * conj T = n²`.
  have hconjT : conj T = conj (ind ℤ Dp) * ind ℤ D -
      (lam : AddMonoidAlgebra ℤ A) * ind ℤ univ := by
    rw [hTdef, map_sub, map_mul, map_mul, conj_conj, map_natCast, conj_univ]
  have hTT : T * conj T = (((k : ℤ) - lam) ^ 2 : ℤ) • (1 : AddMonoidAlgebra ℤ A) := by
    rw [hconjT, hTdef, zsmul_eq_mul, mul_one]
    push_cast
    linear_combination (ind ℤ D * conj (ind ℤ D)) * h2 +
      ((k : AddMonoidAlgebra ℤ A) - (lam : AddMonoidAlgebra ℤ A) +
        (lam : AddMonoidAlgebra ℤ A) * ind ℤ univ) * h1 -
      (lam : AddMonoidAlgebra ℤ A) * conj (ind ℤ D) * h3 -
      (lam : AddMonoidAlgebra ℤ A) * k * h6 - (lam : AddMonoidAlgebra ℤ A) * ind ℤ D * h4 -
      (lam : AddMonoidAlgebra ℤ A) * k * h5 + 2 * (lam : AddMonoidAlgebra ℤ A) ^ 2 * h7 -
      2 * (lam : AddMonoidAlgebra ℤ A) * h8
  have hn : (0 : ℤ) < (k : ℤ) - lam := by
    have : (lam : ℤ) < k := by exact_mod_cast hlam
    linarith
  obtain ⟨g, hg⟩ := eq_single_of_mul_conj T _ hn hpos hTT
  -- Cancel: `n • p•D = n • (D + g)`.
  have hnz : (k : AddMonoidAlgebra ℤ A) - (lam : AddMonoidAlgebra ℤ A) =
      (((k : ℤ) - lam : ℤ) : AddMonoidAlgebra ℤ A) := by
    push_cast; ring
  have hsing : (single g ((k : ℤ) - lam) : AddMonoidAlgebra ℤ A) =
      ((k : AddMonoidAlgebra ℤ A) - (lam : AddMonoidAlgebra ℤ A)) * single g 1 := by
    rw [hnz, AddMonoidAlgebra.intCast_def, single_mul_single, zero_add, mul_one, Int.cast_id]
  have hmain : ((k : AddMonoidAlgebra ℤ A) - (lam : AddMonoidAlgebra ℤ A)) * ind ℤ Dp =
      ((k : AddMonoidAlgebra ℤ A) - (lam : AddMonoidAlgebra ℤ A)) *
        (single g 1 * ind ℤ D) := by
    have e : ind ℤ Dp * conj (ind ℤ D) =
        ((k : AddMonoidAlgebra ℤ A) - (lam : AddMonoidAlgebra ℤ A)) * single g 1 +
          (lam : AddMonoidAlgebra ℤ A) * ind ℤ univ := by
      rw [← hsing, ← hg, hTdef]; ring
    linear_combination ind ℤ D * e - ind ℤ Dp * h1 - (lam : AddMonoidAlgebra ℤ A) * h3 +
      (lam : AddMonoidAlgebra ℤ A) * h5
  have hind : ind ℤ Dp = ind ℤ (D.image (· + g)) := by
    rw [← single_mul_ind]
    ext x
    have := congrArg (fun z => z.coeff x) hmain
    simp only [hnz, coeff_intCast_mul] at this
    exact mul_left_cancel₀ hn.ne' this
  exact ⟨g, ind_injective hind⟩

end Generic

lemma diffCountA_eq (D : Finset G) (g : G) : diffCountA D g = diffCount D g := rfl

/-- Translation preserves difference sets. -/
theorem isDiffSet_translate {D : Finset G} (hD : IsDiffSet D) (u : G) :
    IsDiffSet (D.image (· - u)) := by
  have hinj : Function.Injective fun x : G => x - u := sub_left_injective
  refine ⟨by rw [card_image_of_injective _ hinj, hD.1], fun g hg => ?_⟩
  rw [← diffCountA_eq, diffCountA_image hinj D (g' := g) (fun a => sub_right_comm a g u),
    diffCountA_eq, hD.2 g hg]

/-- Every (243,121,60) difference set in `G` has a translate fixed by the multiplier `61`. -/
theorem exists_fixed_translate {D : Finset G} (hD : IsDiffSet D) :
    ∃ u : G, Fixed (D.image (· - u)) := by
  have h9 : ∀ y : G, (9 : ℕ) • y = 0 := by decide +kernel
  have hmul : ∀ (y : G) (m : ℕ), (9 * m + 1) • y = y := by
    intro y m
    rw [add_nsmul, one_nsmul, mul_comm, ← smul_smul, h9, smul_zero, zero_add]
  have hbij : Function.Bijective fun x : G => (61 : ℕ) • x := by
    refine Function.bijective_iff_has_inverse.2
      ⟨fun x => (4 : ℕ) • x, fun x => ?_, fun x => ?_⟩
    · simp only [smul_smul]; exact hmul x 27
    · simp only [smul_smul]; exact hmul x 27
  have hpk : ((121 : ℕ) : ZMod 61) ^ (61 - 1) = 1 := by decide
  haveI : Fact (Nat.Prime 61) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := multiplier D 121 60 61 hD.1 (fun g hg => hD.2 g hg) (by norm_num)
    (by norm_num) (by norm_num) hpk hbij
  -- Sum over `D`: `61 s = s + 121 g`.
  set s := ∑ x ∈ D, x with hs
  have hsum : (61 : ℕ) • s = s + (121 : ℕ) • g := by
    have e : ∑ y ∈ D.image (fun x => (61 : ℕ) • x), y = ∑ y ∈ D.image (· + g), y := by
      rw [hg]
    rw [sum_image (fun a _ b _ h => hbij.1 h), sum_image (fun a _ b _ h => add_right_cancel h)]
      at e
    rw [hs, smul_sum, e, sum_add_distrib, sum_const, hD.1]
  have h60 : (60 : ℕ) • s = (121 : ℕ) • g := by
    rw [succ_nsmul] at hsum
    exact add_right_cancel (hsum.trans (add_comm _ _))
  have hu : (60 : ℕ) • ((7 : ℕ) • s) = g := by
    rw [smul_smul, mul_comm, ← smul_smul, h60, smul_smul]
    exact hmul g 94
  refine ⟨(7 : ℕ) • s, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
  have hx' : (61 : ℕ) • x ∈ D.image (· + g) := by
    rw [← hg]; exact mem_image_of_mem _ hx
  obtain ⟨z, hz, hzx⟩ := mem_image.1 hx'
  refine mem_image.2 ⟨z, hz, ?_⟩
  rw [smul_sub, ← hzx, ← hu]
  abel

end DS243
