import StanleySnf.Defs

/-!
# The bridge: `M n μ ν` equals the classical character formula

`bridge` proves `(M n μ ν : ℚ) = bridgeFormula n μ ν` for `n > 0`.

The proof uses one explicit model: `L n = Finset (Fin n) → ℚ`, the exterior algebra of `ℚ^n` in
the basis `e_S`. `S_n` acts by signed permutations `rho σ` (`rho σ e_S = ε(σ,S) e_{σS}`);
`E = e ∧ ·` and `I` (contraction with the all-ones form) satisfy `I E + E I = n`, so
`P = I E / n` is an equivariant projection, and `chi k σ = tr (rho σ ∘ P ∘ D k)` is the hook
character `χ^{(n-k,1^k)}` (`chi_eq_hookChar`). The commutant of `rho` on degree `k` is spanned
by `D k` and `P ∘ D k` (an orbit argument), which gives the class-sum identity
`C(n-1,k) ∑_g χ_k(a g b g⁻¹) = n! χ_k(a) χ_k(b)` (`sum_conj`). The indicator of `n`-cycles is
`(1/n) ∑_k (-1)^k χ_k` (`sum_alt_chi`), and orbit–stabiliser over the class of `rep ν` finishes.
-/

open Polynomial Equiv Finset

namespace StanleySnf
namespace Br

variable {n : ℕ}

/-! ## Signs -/

/-- The image of a finset under a permutation. -/
def pm (σ : Perm (Fin n)) (S : Finset (Fin n)) : Finset (Fin n) := S.map σ.toEmbedding

/-- `+1` if `σ` keeps the relative order of `a, b`, else `-1` (and `+1` for `a = b`). -/
def pr (σ : Perm (Fin n)) (a b : Fin n) : ℤˣ := if (σ a < σ b ↔ a < b) then 1 else -1

theorem pr_symm (σ : Perm (Fin n)) (a b : Fin n) : pr σ a b = pr σ b a := by
  rcases eq_or_ne a b with rfl | hab
  · rfl
  have hσ : σ a ≠ σ b := σ.injective.ne hab
  have h1 : (σ b < σ a ↔ b < a) ↔ (σ a < σ b ↔ a < b) := by
    rw [Fin.lt_def, Fin.lt_def, Fin.lt_def,
      Fin.lt_def]
    have := Fin.val_injective.ne hab
    have := Fin.val_injective.ne hσ
    omega
  unfold pr
  simp only [h1]

/-- `ε(σ, S)`: the sign of `σ` restricted to `S`, relative to the orders of `S` and `σ S`. -/
def eps (σ : Perm (Fin n)) (S : Finset (Fin n)) : ℤˣ :=
  ∏ z ∈ S.sym2, Sym2.lift ⟨pr σ, pr_symm σ⟩ z

theorem pr_mul (σ τ : Perm (Fin n)) (a b : Fin n) :
    pr (σ * τ) a b = pr σ (τ a) (τ b) * pr τ a b := by
  unfold pr
  simp only [Perm.mul_apply]
  by_cases h1 : σ (τ a) < σ (τ b) <;> by_cases h2 : τ a < τ b <;> by_cases h3 : a < b <;>
    simp [h1, h2, h3]

theorem pr_one (a b : Fin n) : pr 1 a b = 1 := by simp [pr]

theorem lift_mk (σ : Perm (Fin n)) (a b : Fin n) :
    Sym2.lift ⟨pr σ, pr_symm σ⟩ s(a, b) = pr σ a b := rfl

theorem pm_mul (σ τ : Perm (Fin n)) (S : Finset (Fin n)) : pm (σ * τ) S = pm σ (pm τ S) := by
  simp [pm, Finset.map_map]; rfl

theorem pm_one (S : Finset (Fin n)) : pm 1 S = S := by ext x; simp only [pm, mem_map_equiv]; rfl

theorem mem_pm {σ : Perm (Fin n)} {S : Finset (Fin n)} {x : Fin n} :
    x ∈ pm σ S ↔ σ⁻¹ x ∈ S := by
  simp only [pm, mem_map_equiv]; rfl

theorem card_pm (σ : Perm (Fin n)) (S : Finset (Fin n)) : (pm σ S).card = S.card := by
  simp [pm]

theorem pm_inv_pm (σ : Perm (Fin n)) (S : Finset (Fin n)) : pm σ⁻¹ (pm σ S) = S := by
  rw [← pm_mul, inv_mul_cancel, pm_one]

theorem pm_pm_inv (σ : Perm (Fin n)) (S : Finset (Fin n)) : pm σ (pm σ⁻¹ S) = S := by
  rw [← pm_mul, mul_inv_cancel, pm_one]

theorem pm_eq_of_mapsTo {σ : Perm (Fin n)} {S : Finset (Fin n)} (h : ∀ x ∈ S, σ x ∈ S) :
    pm σ S = S := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [mem_pm] at hx
    simpa using h _ hx
  · rw [card_pm]

theorem eps_mul (σ τ : Perm (Fin n)) (S : Finset (Fin n)) :
    eps (σ * τ) S = eps σ (pm τ S) * eps τ S := by
  unfold eps pm
  rw [Finset.sym2_map, Finset.prod_map, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun z _ => ?_
  induction z using Sym2.ind with
  | _ a b => simp [pr_mul]

theorem eps_congr {σ σ' : Perm (Fin n)} {S : Finset (Fin n)} (h : ∀ x ∈ S, σ x = σ' x) :
    eps σ S = eps σ' S := by
  unfold eps
  refine Finset.prod_congr rfl fun z hz => ?_
  induction z using Sym2.ind with
  | _ a b =>
    rw [Finset.mk_mem_sym2_iff] at hz
    simp only [lift_mk, pr, h a hz.1, h b hz.2]

theorem eps_one (S : Finset (Fin n)) : eps 1 S = 1 := by
  unfold eps
  refine Finset.prod_eq_one fun z _ => ?_
  induction z using Sym2.ind with
  | _ a b => exact pr_one a b

theorem eps_of_fix {σ : Perm (Fin n)} {S : Finset (Fin n)} (h : ∀ x ∈ S, σ x = x) :
    eps σ S = 1 := by
  rw [eps_congr (σ' := 1) (by simpa using h), eps_one]

/-- On a finset `S`, `π ↦ ε(ofSubtype π, S)` is a homomorphism. -/
def epsHom (S : Finset (Fin n)) : Perm {x // x ∈ S} →* ℤˣ where
  toFun π := eps (Perm.ofSubtype π) S
  map_one' := by simp [eps_one]
  map_mul' π₁ π₂ := by
    rw [map_mul, eps_mul]
    congr 1
    apply congrArg
    apply pm_eq_of_mapsTo
    intro x hx
    rw [Perm.ofSubtype_apply_of_mem _ hx]
    exact Subtype.property _

theorem eps_swap_min {S : Finset (Fin n)} (hS : 2 ≤ S.card) :
    ∃ x y : Fin n, x ∈ S ∧ y ∈ S ∧ x ≠ y ∧ eps (swap x y) S = -1 := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  set x := S.min' hne
  have hne' : (S.erase x).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (S.min'_mem hne)]; omega
  set y := (S.erase x).min' hne'
  have hy : y ∈ S.erase x := (S.erase x).min'_mem hne'
  have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
  have hyS : y ∈ S := (Finset.mem_erase.mp hy).2
  have hxy : x < y := lt_of_le_of_ne (S.min'_le _ hyS) hyx.symm
  have hmin : ∀ c ∈ S, c ≠ x → c ≠ y → y < c := by
    intro c hc hcx hcy
    exact lt_of_le_of_ne ((S.erase x).min'_le _ (Finset.mem_erase.mpr ⟨hcx, hc⟩)) (Ne.symm hcy)
  have hxmin : ∀ c ∈ S, x ≤ c := fun c hc => S.min'_le _ hc
  have hmin' : ∀ c ∈ S, c ≠ x → c ≠ y → x < c := fun c hc h1 h2 => hxy.trans (hmin c hc h1 h2)
  refine ⟨x, y, S.min'_mem hne, hyS, hyx.symm, ?_⟩
  unfold eps
  rw [Finset.prod_eq_single s(x, y)]
  · rw [lift_mk]; simp [pr, swap_apply_left, swap_apply_right, hxy, not_lt.mpr hxy.le]
  · intro z hz hzne
    induction z using Sym2.ind with
    | _ a b =>
      rw [Finset.mk_mem_sym2_iff] at hz
      rw [lift_mk]
      have hA : ∀ c ∈ S, c = x ∨ c = y ∨ (x < c ∧ y < c) := by
        intro c hc
        by_cases h1 : c = x
        · exact Or.inl h1
        by_cases h2 : c = y
        · exact Or.inr (Or.inl h2)
        exact Or.inr (Or.inr ⟨hmin' c hc h1 h2, hmin c hc h1 h2⟩)
      unfold pr
      rw [if_pos]
      have hfix : ∀ c, x < c → y < c → swap x y c = c := fun c h1 h2 =>
        swap_apply_of_ne_of_ne (ne_of_gt h1) (ne_of_gt h2)
      clear_value x y
      rcases hA a hz.1 with rfl | rfl | ⟨h1, h2⟩ <;> rcases hA b hz.2 with rfl | rfl | ⟨h3, h4⟩
      all_goals first
        | exact absurd rfl hzne
        | exact absurd Sym2.eq_swap hzne
        | skip
      all_goals (try rw [hfix _ h1 h2]); (try rw [hfix _ h3 h4])
      all_goals (try simp only [swap_apply_left, swap_apply_right])
      all_goals simp only [Fin.lt_def] at *
      all_goals omega
  · intro h; exact absurd (Finset.mk_mem_sym2_iff.mpr ⟨S.min'_mem hne, hyS⟩) h

theorem epsHom_eq_sign (S : Finset (Fin n)) : epsHom S = Perm.sign := by
  by_cases hS : 2 ≤ S.card
  · apply Perm.eq_sign_of_surjective_hom
    obtain ⟨x, y, hx, hy, hxy, h⟩ := eps_swap_min hS
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one _⟩
    · refine ⟨swap ⟨x, hx⟩ ⟨y, hy⟩, ?_⟩
      change eps (Perm.ofSubtype (swap ⟨x, hx⟩ ⟨y, hy⟩)) S = -1
      rw [Perm.ofSubtype_swap_eq]
      exact h
  · have hsub : Subsingleton {x // x ∈ S} := by
      rw [← Fintype.card_le_one_iff_subsingleton, Fintype.card_coe]; omega
    have : Subsingleton (Perm {x // x ∈ S}) := inferInstance
    ext π
    rw [Subsingleton.elim π 1, map_one, map_one]

/-- For `σ` preserving `S` and fixing everything outside `S`, `ε(σ,S) = sign σ`. -/
theorem eps_eq_sign {σ : Perm (Fin n)} {S : Finset (Fin n)} (h₁ : ∀ x, σ x ∈ S ↔ x ∈ S)
    (h₂ : ∀ x, σ x ≠ x → x ∈ S) : eps σ S = Perm.sign σ := by
  have := congrArg (fun f => f (σ.subtypePerm h₁)) (epsHom_eq_sign S)
  simp only [epsHom, MonoidHom.coe_mk, OneHom.coe_mk, Perm.ofSubtype_subtypePerm h₁ h₂] at this
  rw [this]
  convert Perm.sign_subtypePerm σ h₁ h₂

theorem pm_eq_iff {σ : Perm (Fin n)} {S : Finset (Fin n)} :
    pm σ S = S ↔ ∀ x, σ x ∈ S ↔ x ∈ S := by
  constructor
  · intro h x
    have := congrArg (fun T => σ x ∈ T) h
    simp only [mem_pm] at this
    simpa using this.symm
  · intro h
    ext x
    rw [mem_pm, ← h]
    simp

/-- `ε(σ,S)` is the sign of any permutation agreeing with `σ` on `S` and fixing the rest. -/
theorem eps_eq_sign_of {σ ρ' : Perm (Fin n)} {S : Finset (Fin n)} (hS : pm σ S = S)
    (hagree : ∀ x ∈ S, ρ' x = σ x) (hfix : ∀ x ∉ S, ρ' x = x) : eps σ S = Perm.sign ρ' := by
  rw [eps_congr (σ' := ρ') fun x hx => (hagree x hx).symm]
  rw [pm_eq_iff] at hS
  apply eps_eq_sign
  · intro x
    by_cases hx : x ∈ S
    · rw [hagree x hx]; exact ⟨fun _ => hx, fun _ => (hS x).mpr hx⟩
    · rw [hfix x hx]
  · intro x hx
    by_contra h
    exact hx (hfix x h)

theorem eps_sq (σ : Perm (Fin n)) (S : Finset (Fin n)) :
    ((eps σ S : ℤ) : ℚ) * ((eps σ S : ℤ) : ℚ) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp

/-- `(-1)^{#{s ∈ T, s < t}}`. -/
def sgnAt (t : Fin n) (T : Finset (Fin n)) : ℚ := (-1) ^ (T.filter (· < t)).card

/-! ## The model -/

/-- The exterior algebra of `ℚ^n`, as functions on subsets. -/
abbrev L (n : ℕ) := Finset (Fin n) → ℚ

/-- `rho σ e_S = ε(σ,S) e_{σ S}`. -/
def rho (σ : Perm (Fin n)) : L n →ₗ[ℚ] L n where
  toFun f T := ((eps σ (pm σ⁻¹ T) : ℤ) : ℚ) * f (pm σ⁻¹ T)
  map_add' f g := by ext T; simp [mul_add]
  map_smul' c f := by ext T; simp; ring

/-- `E = e ∧ ·` with `e = ∑ e_i`. -/
def E : L n →ₗ[ℚ] L n where
  toFun f T := ∑ t ∈ T, sgnAt t T * f (T.erase t)
  map_add' f g := by ext T; simp [mul_add, sum_add_distrib]
  map_smul' c f := by ext T; simp [mul_sum]; exact sum_congr rfl fun _ _ => by ring

/-- `I` = contraction with the all-ones linear form. -/
def I : L n →ₗ[ℚ] L n where
  toFun f S := ∑ t ∈ Sᶜ, sgnAt t (insert t S) * f (insert t S)
  map_add' f g := by ext T; simp [mul_add, sum_add_distrib]
  map_smul' c f := by ext T; simp [mul_sum]; exact sum_congr rfl fun _ _ => by ring

/-- The projection onto degree `k`. -/
def D (k : ℕ) : L n →ₗ[ℚ] L n where
  toFun f S := if S.card = k then f S else 0
  map_add' f g := by ext T; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c f := by ext T; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

/-- The projection onto `ker I`. -/
noncomputable def P : L n →ₗ[ℚ] L n := (n : ℚ)⁻¹ • (I ∘ₗ E)

/-- The hook character `χ^{(n-k,1^k)}(σ)`, as a trace on the model. -/
noncomputable def chi (k : ℕ) (σ : Perm (Fin n)) : ℚ :=
  LinearMap.trace ℚ (L n) (rho σ ∘ₗ P ∘ₗ D k)

/-! ## Identities in the model -/

theorem rho_apply (σ : Perm (Fin n)) (f : L n) (T : Finset (Fin n)) :
    rho σ f T = ((eps σ (pm σ⁻¹ T) : ℤ) : ℚ) * f (pm σ⁻¹ T) := rfl

theorem rho_mul (σ τ : Perm (Fin n)) : rho (σ * τ) = rho σ ∘ₗ rho τ := by
  refine LinearMap.ext fun f => funext fun T => ?_
  simp only [LinearMap.comp_apply, rho_apply, mul_inv_rev, pm_mul]
  rw [eps_mul, pm_pm_inv]
  push_cast; ring

theorem rho_one : rho (1 : Perm (Fin n)) = LinearMap.id := by
  refine LinearMap.ext fun f => funext fun T => ?_
  simp [rho_apply, pm_one, eps_one]

theorem rho_single (σ : Perm (Fin n)) (S : Finset (Fin n)) :
    rho σ (Pi.single S 1) = ((eps σ S : ℤ) : ℚ) • Pi.single (pm σ S) 1 := by
  funext T
  simp only [rho_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases h : T = pm σ S
  · subst h; simp [pm_inv_pm]
  · have h' : pm σ⁻¹ T ≠ S := fun h' => h (by rw [← h', pm_pm_inv])
    simp [h, h']

theorem sgnAt_sq (t : Fin n) (T : Finset (Fin n)) : sgnAt t T * sgnAt t T = 1 := by
  unfold sgnAt; rw [← pow_add, ← two_mul, pow_mul]; norm_num

theorem sgnAt_insert_self (t : Fin n) (S : Finset (Fin n)) : sgnAt t (insert t S) = sgnAt t S := by
  unfold sgnAt; rw [filter_insert, if_neg (lt_irrefl t)]

theorem sgnAt_insert {t u : Fin n} {S : Finset (Fin n)} (ht : t ∉ S) :
    sgnAt u (insert t S) = (if t < u then -1 else 1) * sgnAt u S := by
  unfold sgnAt; rw [filter_insert]; split_ifs with h
  · rw [card_insert_of_notMem (by simp [ht])]; ring
  · ring

theorem sgnAt_erase {t u : Fin n} {S : Finset (Fin n)} (hu : u ∈ S) :
    sgnAt t (S.erase u) = (if u < t then -1 else 1) * sgnAt t S := by
  unfold sgnAt; rw [filter_erase]; split_ifs with h
  · have hm : u ∈ S.filter (· < t) := mem_filter.mpr ⟨hu, h⟩
    rw [← card_erase_add_one hm]; ring
  · rw [erase_eq_of_notMem (by simp [h])]; ring

theorem ite_add_ite_eq_zero {t u : Fin n} (h : t ≠ u) :
    ((if t < u then -1 else 1) + (if u < t then -1 else 1) : ℚ) = 0 := by
  rcases lt_or_gt_of_ne h with h | h
  · simp [h, not_lt.mpr h.le]
  · simp [h, not_lt.mpr h.le]

theorem IE_add_EI : I ∘ₗ E + E ∘ₗ I = (n : ℚ) • (LinearMap.id : L n →ₗ[ℚ] L n) := by
  refine LinearMap.ext fun f => funext fun S => ?_
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : I (E f) S = ((Sᶜ.card : ℕ) : ℚ) * f S + ∑ t ∈ Sᶜ, ∑ u ∈ S,
      sgnAt t (insert t S) * sgnAt u (insert t S) * f (insert t (S.erase u)) := by
    simp only [I, E, LinearMap.coe_mk, AddHom.coe_mk]
    rw [card_eq_sum_ones, Nat.cast_sum, sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun t ht => ?_
    have ht' : t ∉ S := by simpa using ht
    rw [sum_insert ht', erase_insert ht', mul_add, ← mul_assoc, sgnAt_sq, mul_sum]
    congr 1
    refine sum_congr rfl fun u hu => ?_
    rw [erase_insert_of_ne (by rintro rfl; exact ht' hu)]; ring
  have h2 : E (I f) S = ((S.card : ℕ) : ℚ) * f S + ∑ u ∈ S, ∑ t ∈ Sᶜ,
      sgnAt u S * sgnAt t (insert t (S.erase u)) * f (insert t (S.erase u)) := by
    simp only [I, E, LinearMap.coe_mk, AddHom.coe_mk]
    rw [card_eq_sum_ones, Nat.cast_sum, sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun u hu => ?_
    have hc : (S.erase u)ᶜ = insert u Sᶜ := by
      ext x; by_cases hx : x = u <;> simp_all
    have hu' : u ∉ Sᶜ := by simpa using hu
    rw [hc, sum_insert hu', insert_erase hu, mul_add, ← mul_assoc, sgnAt_sq, mul_sum]
    congr 1
    refine sum_congr rfl fun t _ => ?_; ring
  rw [h1, h2, sum_comm (s := S)]
  have hcard : ((Sᶜ.card : ℕ) : ℚ) + ((S.card : ℕ) : ℚ) = n := by
    rw [← Nat.cast_add, card_compl_add_card, Fintype.card_fin]
  have cross : ∑ t ∈ Sᶜ, ∑ u ∈ S,
      sgnAt t (insert t S) * sgnAt u (insert t S) * f (insert t (S.erase u)) +
      ∑ t ∈ Sᶜ, ∑ u ∈ S,
      sgnAt u S * sgnAt t (insert t (S.erase u)) * f (insert t (S.erase u)) = 0 := by
    rw [← sum_add_distrib]
    refine sum_eq_zero fun t ht => ?_
    rw [← sum_add_distrib]
    refine sum_eq_zero fun u hu => ?_
    have ht' : t ∉ S := by simpa using ht
    have htu : t ≠ u := by rintro rfl; exact ht' hu
    rw [sgnAt_insert_self, sgnAt_insert ht', sgnAt_insert_self, sgnAt_erase hu]
    have := ite_add_ite_eq_zero htu
    linear_combination (sgnAt t S * sgnAt u S * f (insert t (S.erase u))) * this
  linear_combination f S * hcard + cross

theorem EE : E ∘ₗ E = (0 : L n →ₗ[ℚ] L n) := by
  refine LinearMap.ext fun f => funext fun T => ?_
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply, E, LinearMap.coe_mk,
    AddHom.coe_mk, mul_sum]
  set h : Fin n → Fin n → ℚ := fun t u => if u = t then 0 else
    sgnAt t T * (sgnAt u (T.erase t) * f ((T.erase t).erase u)) with hh
  have hanti : ∀ t ∈ T, ∀ u ∈ T, h u t = - h t u := by
    intro t ht u hu
    by_cases htu : t = u
    · subst htu; simp [hh]
    rw [hh]
    simp only [if_neg htu, if_neg (Ne.symm htu)]
    rw [sgnAt_erase hu, sgnAt_erase ht, erase_right_comm]
    have := ite_add_ite_eq_zero htu
    linear_combination (sgnAt t T * sgnAt u T * f ((T.erase t).erase u)) * this
  have hX : ∑ t ∈ T, ∑ u ∈ T.erase t, sgnAt t T * (sgnAt u (T.erase t) * f ((T.erase t).erase u))
      = ∑ t ∈ T, ∑ u ∈ T, h t u := by
    refine sum_congr rfl fun t ht => ?_
    rw [← add_zero (∑ u ∈ T.erase t, _), ← sum_erase_add T _ ht]
    simp only [hh, if_pos rfl, add_zero]
    exact sum_congr rfl fun u hu => by rw [if_neg (ne_of_mem_erase hu)]
  rw [hX]
  have : ∑ t ∈ T, ∑ u ∈ T, h t u = - ∑ t ∈ T, ∑ u ∈ T, h t u := by
    conv_lhs => rw [sum_comm]
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun u hu => ?_
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun t ht => hanti u hu t ht
  linarith

/-- Removing a point: `ε(σ,U) sgn(t,U) = sgn(σt,σU) ε(σ,U∖t)`. -/
theorem eps_erase_sgn (σ : Perm (Fin n)) {U : Finset (Fin n)} {t : Fin n} (ht : t ∈ U) :
    ((eps σ U : ℤ) : ℚ) * sgnAt t U = sgnAt (σ t) (pm σ U) * ((eps σ (U.erase t) : ℤ) : ℚ) := by
  set V := U.erase t with hV
  have htV : t ∉ V := by simp [hV]
  have hU : U = V.cons t htV := by rw [cons_eq_insert, hV, insert_erase ht]
  have heps : eps σ U = eps σ V * ∏ c ∈ V, pr σ t c := by
    rw [hU]
    unfold eps
    rw [Finset.sym2_cons, prod_disjUnion, prod_map, prod_cons, mul_comm]
    congr 1
    simp only [Sym2.mkEmbedding_apply, lift_mk]
    rw [show pr σ t t = 1 by simp [pr], one_mul]
  have hpr : ∀ c ∈ V, ((pr σ t c : ℤ) : ℚ) =
      (if c < t then -1 else 1) * (if σ c < σ t then -1 else 1) := by
    intro c hc
    have hct : c ≠ t := by rintro rfl; exact htV hc
    have hσ : σ c ≠ σ t := σ.injective.ne hct
    unfold pr
    rcases lt_or_gt_of_ne hct with h | h <;> rcases lt_or_gt_of_ne hσ with h' | h' <;>
      simp [h, h', not_lt.mpr h.le, not_lt.mpr h'.le]
  have h1 : sgnAt t U = ∏ c ∈ V, (if c < t then (-1 : ℚ) else 1) := by
    rw [prod_ite, prod_const, prod_const_one, mul_one, sgnAt, hV, filter_erase,
      erase_eq_of_notMem (by simp)]
  have h2 : sgnAt (σ t) (pm σ U) = ∏ c ∈ V, (if σ c < σ t then (-1 : ℚ) else 1) := by
    rw [prod_ite, prod_const, prod_const_one, mul_one, sgnAt, pm, filter_map, card_map, hV,
      filter_erase, erase_eq_of_notMem (by simp)]
    rfl
  rw [heps, Units.val_mul, Int.cast_mul, Units.coe_prod, Int.cast_prod, prod_congr rfl hpr,
    prod_mul_distrib, ← h1, ← h2]
  linear_combination ((eps σ V : ℤ) : ℚ) * sgnAt (σ t) (pm σ U) * sgnAt_sq t U

theorem rho_E (σ : Perm (Fin n)) : rho σ ∘ₗ E = E ∘ₗ rho σ := by
  refine LinearMap.ext fun f => funext fun T => ?_
  obtain ⟨U, rfl⟩ : ∃ U, T = pm σ U := ⟨pm σ⁻¹ T, (pm_pm_inv σ T).symm⟩
  simp only [LinearMap.comp_apply, rho_apply, E, LinearMap.coe_mk, AddHom.coe_mk, pm_inv_pm,
    mul_sum]
  rw [pm, sum_map]
  refine sum_congr rfl fun t ht => ?_
  have hh : pm σ⁻¹ ((U.map σ.toEmbedding).erase (σ.toEmbedding t)) = U.erase t := by
    rw [← map_erase, ← pm, pm_inv_pm]
  rw [hh, ← mul_assoc, eps_erase_sgn σ ht]
  simp only [Equiv.coe_toEmbedding, pm]
  ring

theorem sq_swap {a b c d : ℚ} (ha : a * a = 1) (hd : d * d = 1) (h : a * b = c * d) :
    d * b = c * a := by
  linear_combination (a * d) * h - (b * d) * ha + (a * c) * hd

theorem rho_I (σ : Perm (Fin n)) : rho σ ∘ₗ I = I ∘ₗ rho σ := by
  refine LinearMap.ext fun f => funext fun T => ?_
  obtain ⟨U, rfl⟩ : ∃ U, T = pm σ U := ⟨pm σ⁻¹ T, (pm_pm_inv σ T).symm⟩
  simp only [LinearMap.comp_apply, rho_apply, I, LinearMap.coe_mk, AddHom.coe_mk, pm_inv_pm,
    mul_sum]
  have hc : (pm σ U)ᶜ = pm σ Uᶜ := by
    ext x; simp [mem_pm]
  rw [hc, pm, sum_map]
  refine sum_congr rfl fun t ht => ?_
  have ht' : t ∉ U := by simpa using ht
  have hins : insert ((Equiv.toEmbedding σ) t) (pm σ U) = pm σ (insert t U) := by
    rw [pm, pm, map_insert]
  rw [hins, pm_inv_pm]
  have key := eps_erase_sgn σ (mem_insert_self t U)
  rw [erase_insert ht'] at key
  have key' := sq_swap (eps_sq _ _) (eps_sq _ _) key
  simp only [Equiv.coe_toEmbedding]
  linear_combination f (insert t U) * key'

theorem D_apply (k : ℕ) (f : L n) (S : Finset (Fin n)) :
    D k f S = if S.card = k then f S else 0 := rfl

theorem rho_D (σ : Perm (Fin n)) (k : ℕ) : rho σ ∘ₗ D k = D k ∘ₗ rho σ := by
  refine LinearMap.ext fun f => funext fun T => ?_
  simp only [LinearMap.comp_apply, rho_apply, D_apply, card_pm]
  split_ifs <;> simp

theorem E_D (k : ℕ) : E ∘ₗ D k = D (k + 1) ∘ₗ (E : L n →ₗ[ℚ] L n) := by
  refine LinearMap.ext fun f => funext fun T => ?_
  simp only [LinearMap.comp_apply, D_apply, E, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs with h
  · refine sum_congr rfl fun t ht => ?_
    rw [if_pos (by rw [card_erase_of_mem ht]; omega)]
  · refine sum_eq_zero fun t ht => ?_
    rw [if_neg (by rw [card_erase_of_mem ht]; have := card_pos.mpr ⟨t, ht⟩; omega), mul_zero]

theorem I_D (k : ℕ) : I ∘ₗ D (k + 1) = D k ∘ₗ (I : L n →ₗ[ℚ] L n) := by
  refine LinearMap.ext fun f => funext fun S => ?_
  simp only [LinearMap.comp_apply, D_apply, I, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs with h
  · refine sum_congr rfl fun t ht => ?_
    rw [if_pos (by rw [card_insert_of_notMem (by simpa using ht)]; omega)]
  · refine sum_eq_zero fun t ht => ?_
    rw [if_neg (by rw [card_insert_of_notMem (by simpa using ht)]; omega), mul_zero]

theorem I_D0 : I ∘ₗ D 0 = (0 : L n →ₗ[ℚ] L n) := by
  refine LinearMap.ext fun f => funext fun S => ?_
  simp only [LinearMap.comp_apply, D_apply, I, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.zero_apply, Pi.zero_apply]
  refine sum_eq_zero fun t ht => ?_
  rw [if_neg (by rw [card_insert_of_notMem (by simpa using ht)]; omega), mul_zero]

theorem D_eq_zero {k : ℕ} (hk : n < k) : D k = (0 : L n →ₗ[ℚ] L n) := by
  refine LinearMap.ext fun f => funext fun S => ?_
  have : S.card ≤ n := by simpa using card_le_univ S
  simp only [D_apply, LinearMap.zero_apply, Pi.zero_apply]
  rw [if_neg (by omega)]

theorem D_D (k : ℕ) : D k ∘ₗ D k = (D k : L n →ₗ[ℚ] L n) := by
  refine LinearMap.ext fun f => funext fun S => ?_
  simp only [LinearMap.comp_apply, D_apply]
  split_ifs <;> rfl

theorem trace_eq (A : L n →ₗ[ℚ] L n) :
    LinearMap.trace ℚ (L n) A = ∑ S, A (Pi.single S 1) S := by
  rw [LinearMap.trace_eq_matrix_trace ℚ (Pi.basisFun ℚ _), LinearMap.toMatrix_eq_toMatrix',
    Matrix.trace]
  simp [LinearMap.toMatrix'_apply]

/-! ## The character of `∧ ℚ^n`: a product over cycles -/

/-- `∑_{σ S = S} ε(σ,S) X^{|S|}`, the generating function of the characters of `∧^k ℚ^n`. -/
noncomputable def Phi (σ : Perm (Fin n)) : ℤ[X] :=
  ∑ S ∈ univ.filter (fun S => pm σ S = S), C ((eps σ S : ℤ)) * X ^ S.card

theorem split_sum {R : Type*} [CommRing R] (C' : Finset (Fin n)) (g1 g2 : Finset (Fin n) → R) :
    ∑ S : Finset (Fin n), g1 (S ∩ C') * g2 (S \ C') =
      (∑ A ∈ C'.powerset, g1 A) * (∑ B ∈ C'ᶜ.powerset, g2 B) := by
  rw [sum_mul_sum, ← sum_product']
  refine sum_nbij' (fun S => (S ∩ C', S \ C')) (fun p => p.1 ∪ p.2) ?_ ?_ ?_ ?_ ?_
  · intro S _
    simp only [mem_product, mem_powerset]
    exact ⟨inter_subset_right, fun x hx => by simp only [mem_sdiff] at hx; simpa using hx.2⟩
  · intro p _; simp
  · intro S _
    ext x; simp only [mem_union, mem_inter, mem_sdiff]; tauto
  · intro p hp
    simp only [mem_product, mem_powerset] at hp
    obtain ⟨h1, h2⟩ := hp
    ext x
    · simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨hx | hx, hc⟩
        · exact hx
        · exact absurd hc (by simpa using h2 hx)
      · intro hx; exact ⟨Or.inl hx, h1 hx⟩
    · simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨hx | hx, hc⟩
        · exact absurd (h1 hx) hc
        · exact hx
      · intro hx; exact ⟨Or.inr hx, by simpa using h2 hx⟩
  · intro S _; rfl

theorem pm_pow_of {σ : Perm (Fin n)} {S : Finset (Fin n)} (h : pm σ S = S) (i : ℕ) :
    pm (σ ^ i) S = S := by
  induction i with
  | zero => simp [pm_one]
  | succ i ih => rw [pow_succ, pm_mul, h, ih]

theorem inv_mul_iff {c τ : Perm (Fin n)} (hd : Perm.Disjoint c τ) (S : Finset (Fin n)) :
    pm (c * τ) S = S ↔ pm c S = S ∧ pm τ S = S := by
  constructor
  · intro h
    have hc : pm c S = S := by
      apply pm_eq_of_mapsTo
      intro x hx
      rcases hd x with h1 | h1
      · rw [h1]; exact hx
      · have := (pm_eq_iff.mp h x).mpr hx
        rwa [Perm.mul_apply, h1] at this
    refine ⟨hc, ?_⟩
    have : pm τ S = pm c⁻¹ (pm (c * τ) S) := by rw [← pm_mul, inv_mul_cancel_left]
    rw [this, h, ← hc, pm_inv_pm, hc]
  · rintro ⟨h1, h2⟩
    rw [pm_mul, h2, h1]

theorem inv_cycle_iff {c : Perm (Fin n)} (hc : c.IsCycle) (S : Finset (Fin n)) :
    pm c S = S ↔ Disjoint S c.support ∨ c.support ⊆ S := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨hnd, hns⟩ := hcon
    obtain ⟨x, hxS, hxc⟩ := Finset.not_disjoint_iff.mp hnd
    obtain ⟨y, hyc, hyS⟩ := Finset.not_subset.mp hns
    obtain ⟨i, hi⟩ := hc.exists_pow_eq (Perm.mem_support.mp hxc) (Perm.mem_support.mp hyc)
    have := (pm_eq_iff.mp (pm_pow_of h i) x).mpr hxS
    rw [hi] at this
    exact hyS this
  · rintro (h | h)
    · apply pm_eq_of_mapsTo
      intro x hx
      rw [Perm.notMem_support.mp (Finset.disjoint_left.mp h hx)]; exact hx
    · apply pm_eq_of_mapsTo
      intro x hx
      by_cases hxc : x ∈ c.support
      · exact h (Perm.apply_mem_support.mpr hxc)
      · rw [Perm.notMem_support.mp hxc]; exact hx

theorem inv_fix_iff {τ : Perm (Fin n)} {C' : Finset (Fin n)} (hτ : ∀ x ∈ C', τ x = x)
    (S : Finset (Fin n)) : pm τ S = S ↔ pm τ (S \ C') = S \ C' := by
  have hτ' : ∀ x, τ x ∈ C' → x ∈ C' := by
    intro x hx
    have := hτ _ hx
    rw [τ.injective this] at hx; exact hx
  constructor
  · intro h
    apply pm_eq_of_mapsTo
    intro x hx
    rw [mem_sdiff] at hx ⊢
    exact ⟨(pm_eq_iff.mp h x).mpr hx.1, fun h' => hx.2 (hτ' x h')⟩
  · intro h
    apply pm_eq_of_mapsTo
    intro x hx
    by_cases hxc : x ∈ C'
    · rw [hτ x hxc]; exact hx
    · have := (pm_eq_iff.mp h x).mpr (mem_sdiff.mpr ⟨hx, hxc⟩)
      exact (mem_sdiff.mp this).1

theorem eps_cycle {c : Perm (Fin n)} (hc : c.IsCycle) {S : Finset (Fin n)} (hS : pm c S = S) :
    eps c S = if c.support ⊆ S then Perm.sign c else 1 := by
  split_ifs with h
  · exact eps_eq_sign_of hS (fun _ _ => rfl) fun x hx =>
      Perm.notMem_support.mp fun hx' => hx (h hx')
  · have hd : Disjoint S c.support := by
      rcases (inv_cycle_iff hc S).mp hS with h' | h'
      · exact h'
      · exact absurd h' h
    exact eps_of_fix fun x hx => Perm.notMem_support.mp (Finset.disjoint_left.mp hd hx)

theorem eps_sdiff {τ : Perm (Fin n)} {C' S : Finset (Fin n)} (hτ : ∀ x ∈ C', τ x = x)
    (hS : pm τ S = S) : eps τ S = eps τ (S \ C') := by
  have hS' := (inv_fix_iff hτ S).mp hS
  have h₁ : ∀ x, τ x ∈ S \ C' ↔ x ∈ S \ C' := pm_eq_iff.mp hS'
  set ρ' := Perm.ofSubtype (τ.subtypePerm h₁)
  have hin : ∀ x ∈ S \ C', ρ' x = τ x := fun x hx => by
    rw [Perm.ofSubtype_apply_of_mem _ hx]; rfl
  have hout : ∀ x ∉ S \ C', ρ' x = x := fun x hx => Perm.ofSubtype_apply_of_not_mem _ hx
  rw [eps_eq_sign_of hS (ρ' := ρ') ?_ ?_, eps_eq_sign_of hS' hin hout]
  · intro x hx
    by_cases hxc : x ∈ C'
    · rw [hout x (fun h => (mem_sdiff.mp h).2 hxc), hτ x hxc]
    · exact hin x (mem_sdiff.mpr ⟨hx, hxc⟩)
  · intro x hx
    exact hout x fun h => hx (mem_sdiff.mp h).1

theorem Phi_eq_sum (σ : Perm (Fin n)) :
    Phi σ = ∑ S : Finset (Fin n), if pm σ S = S then C ((eps σ S : ℤ)) * X ^ S.card else 0 := by
  rw [Phi, sum_filter]

theorem Phi_mul_cycle {c τ : Perm (Fin n)} (hc : c.IsCycle) (hd : Perm.Disjoint c τ) :
    Phi (c * τ) * (1 + X) ^ c.support.card = (1 - (-X) ^ c.support.card) * Phi τ := by
  set C' := c.support with hC'
  have hτC : ∀ x ∈ C', τ x = x := fun x hx => (hd x).resolve_left (Perm.mem_support.mp hx)
  have hCne : C' ≠ ∅ := by
    rw [← Finset.nonempty_iff_ne_empty, ← card_pos]
    have := hc.two_le_card_support; rw [← hC'] at this; omega
  set g2 : Finset (Fin n) → ℤ[X] := fun B =>
    if pm τ B = B then C ((eps τ B : ℤ)) * X ^ B.card else 0 with hg2
  set g1 : Finset (Fin n) → ℤ[X] := fun A =>
    if A = ∅ then 1 else if A = C' then C ((Perm.sign c : ℤ)) * X ^ C'.card else 0 with hg1
  have hτsum : Phi τ = ∑ S : Finset (Fin n), X ^ (S ∩ C').card * g2 (S \ C') := by
    rw [Phi_eq_sum]
    refine sum_congr rfl fun S _ => ?_
    rw [hg2]
    simp only
    by_cases h : pm τ S = S
    · rw [if_pos h, if_pos ((inv_fix_iff hτC S).mp h), eps_sdiff hτC h,
        ← card_inter_add_card_sdiff S C', pow_add]; ring
    · rw [if_neg h, if_neg (fun h' => h ((inv_fix_iff hτC S).mpr h')), mul_zero]
  have hcτsum : Phi (c * τ) = ∑ S : Finset (Fin n), g1 (S ∩ C') * g2 (S \ C') := by
    rw [Phi_eq_sum]
    refine sum_congr rfl fun S _ => ?_
    rw [hg1, hg2]
    simp only
    have hiff : pm (c * τ) S = S ↔ pm c S = S ∧ pm τ (S \ C') = S \ C' := by
      rw [inv_mul_iff hd, inv_fix_iff hτC S]
    by_cases h0 : S ∩ C' = ∅
    · have hdis : Disjoint S C' := Finset.disjoint_iff_inter_eq_empty.mpr h0
      have hcS : pm c S = S := (inv_cycle_iff hc S).mpr (Or.inl hdis)
      rw [if_pos h0, one_mul]
      by_cases h : pm τ (S \ C') = S \ C'
      · have hτS : pm τ S = S := (inv_fix_iff hτC S).mpr h
        rw [if_pos (hiff.mpr ⟨hcS, h⟩), if_pos h, eps_mul, hτS, eps_cycle hc hcS, if_neg,
          one_mul, eps_sdiff hτC hτS, ← card_inter_add_card_sdiff S C', h0, card_empty, zero_add]
        intro hsub
        exact hCne (by rw [← h0, inter_eq_right.mpr hsub])
      · rw [if_neg (fun h' => h (hiff.mp h').2), if_neg h]
    · rw [if_neg h0]
      by_cases h1 : S ∩ C' = C'
      · have hsub : C' ⊆ S := inter_eq_right.mp h1
        have hcS : pm c S = S := (inv_cycle_iff hc S).mpr (Or.inr hsub)
        rw [if_pos h1]
        by_cases h : pm τ (S \ C') = S \ C'
        · have hτS : pm τ S = S := (inv_fix_iff hτC S).mpr h
          rw [if_pos (hiff.mpr ⟨hcS, h⟩), if_pos h, eps_mul, hτS, eps_cycle hc hcS, if_pos hsub,
            eps_sdiff hτC hτS, ← card_inter_add_card_sdiff S C', h1, pow_add, Units.val_mul,
            C_mul]
          ring
        · rw [if_neg (fun h' => h (hiff.mp h').2), if_neg h, mul_zero]
      · rw [if_neg h1, zero_mul]
        have hcS : ¬ pm c S = S := by
          rw [inv_cycle_iff hc S]
          rintro (h | h)
          · exact h0 (Finset.disjoint_iff_inter_eq_empty.mp h)
          · exact h1 (inter_eq_right.mpr h)
        rw [if_neg (fun h' => hcS (hiff.mp h').1)]
  have hg1sum : ∑ A ∈ C'.powerset, g1 A = 1 - (-X) ^ C'.card := by
    have : ∀ A ∈ C'.powerset, g1 A = (if A = ∅ then 1 else 0) +
        (if A = C' then C ((Perm.sign c : ℤ)) * X ^ C'.card else 0) := by
      intro A _
      rw [hg1]; simp only
      by_cases h : A = ∅
      · rw [if_pos h, if_pos h, if_neg (by rw [h]; exact hCne.symm), add_zero]
      · rw [if_neg h, if_neg h, zero_add]
    rw [sum_congr rfl this, sum_add_distrib, sum_ite_eq', sum_ite_eq', if_pos (empty_mem_powerset _),
      if_pos (mem_powerset_self _), hc.sign]
    rw [← hC']
    simp only [Units.val_neg, Units.val_pow_eq_pow_val, Units.val_one]
    rw [map_neg, map_pow, map_neg, map_one, neg_pow (X : ℤ[X])]
    ring
  have hXsum : ∑ A ∈ C'.powerset, (X : ℤ[X]) ^ A.card = (1 + X) ^ C'.card := by
    have := sum_pow_mul_eq_add_pow (X : ℤ[X]) 1 C'
    simp only [one_pow, mul_one] at this
    rw [this, add_comm]
  rw [hcτsum, hτsum, split_sum, split_sum C' (fun A => X ^ A.card) g2, hg1sum, hXsum]
  ring

theorem Phi_one : Phi (1 : Perm (Fin n)) = (1 + X) ^ n := by
  rw [Phi_eq_sum]
  have := sum_pow_mul_eq_add_pow (X : ℤ[X]) 1 (univ : Finset (Fin n))
  simp only [one_pow, mul_one, powerset_univ, card_univ, Fintype.card_fin] at this
  rw [add_comm, ← this]
  refine sum_congr rfl fun S _ => ?_
  simp [pm_one, eps_one]

theorem one_add_X_ne_zero : (1 + X : ℤ[X]) ≠ 0 := by
  intro h
  have := congrArg (eval 0) h
  simp at this

theorem Phi_cycleType (σ : Perm (Fin n)) :
    Phi σ = (1 + X) ^ (n - σ.support.card) * (σ.cycleType.map fun m => 1 - (-X) ^ m).prod := by
  refine Perm.cycle_induction_on
    (fun σ => Phi σ = (1 + X) ^ (n - σ.support.card) *
      (σ.cycleType.map fun m => 1 - (-X) ^ m).prod) σ ?_ ?_ ?_
  · simp [Phi_one]
  · intro c hc
    have key := Phi_mul_cycle hc (Perm.disjoint_one_right c)
    rw [mul_one, Phi_one] at key
    have hle : c.support.card ≤ n := by simpa using card_le_univ c.support
    apply mul_right_cancel₀ (pow_ne_zero c.support.card one_add_X_ne_zero)
    rw [key, hc.cycleType]
    simp only [Multiset.map_singleton, Multiset.prod_singleton]
    rw [show (1 + X : ℤ[X]) ^ n = (1 + X) ^ (n - c.support.card) * (1 + X) ^ c.support.card by
      rw [← pow_add, Nat.sub_add_cancel hle]]
    ring
  · intro c τ hd hc _ ih
    have key := Phi_mul_cycle hc hd
    rw [ih] at key
    have hle : (c * τ).support.card ≤ n := by simpa using card_le_univ (c * τ).support
    rw [hd.card_support_mul] at hle ⊢
    apply mul_right_cancel₀ (pow_ne_zero c.support.card one_add_X_ne_zero)
    rw [key, hd.cycleType_mul, hc.cycleType, Multiset.map_add, Multiset.prod_add]
    simp only [Multiset.map_singleton, Multiset.prod_singleton]
    rw [show (1 + X : ℤ[X]) ^ (n - τ.support.card) =
        (1 + X) ^ (n - (c.support.card + τ.support.card)) * (1 + X) ^ c.support.card by
      rw [← pow_add]; congr 1; omega]
    ring

theorem Phi_partition (σ : Perm (Fin n)) :
    Phi σ = (σ.partition.parts.map fun m => 1 - (-X) ^ m).prod := by
  rw [Phi_cycleType, Perm.parts_partition, Multiset.map_add, Multiset.prod_add,
    Multiset.map_replicate, Multiset.prod_replicate, Fintype.card_fin]
  ring

/-! ## The hook characters -/

/-- The character of `∧^k ℚ^n`. -/
noncomputable def psi (k : ℕ) (σ : Perm (Fin n)) : ℚ := LinearMap.trace ℚ (L n) (rho σ * D k)

theorem chi_def (k : ℕ) (σ : Perm (Fin n)) :
    chi k σ = LinearMap.trace ℚ (L n) (rho σ * (P * D k)) := rfl

theorem D_single (k : ℕ) (S : Finset (Fin n)) :
    D k (Pi.single S (1 : ℚ)) = if S.card = k then Pi.single S 1 else 0 := by
  funext T
  rw [D_apply]
  by_cases h : T = S
  · subst h; split_ifs <;> simp
  · split_ifs <;> simp [h]

theorem psi_eq_coeff (k : ℕ) (σ : Perm (Fin n)) : psi k σ = (((Phi σ).coeff k : ℤ) : ℚ) := by
  rw [psi, trace_eq, Phi, finsetSum_coeff, Int.cast_sum, sum_filter]
  refine sum_congr rfl fun S _ => ?_
  rw [coeff_C_mul_X_pow, Module.End.mul_apply, D_single]
  by_cases hk : S.card = k
  · rw [if_pos hk, rho_single, if_pos hk.symm]
    by_cases hinv : pm σ S = S
    · simp [hinv]
    · simp [hinv, Ne.symm hinv]
  · rw [if_neg hk, map_zero, if_neg (Ne.symm hk)]
    simp

theorem P_add (hn : 0 < n) : P + (n : ℚ)⁻¹ • (E * I) = (1 : L n →ₗ[ℚ] L n) := by
  have h := IE_add_EI (n := n)
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [P, ← smul_add]
  change (n : ℚ)⁻¹ • (I ∘ₗ E + E ∘ₗ I) = 1
  rw [h, smul_smul, inv_mul_cancel₀ hn', one_smul]
  rfl

theorem psi_eq (hn : 0 < n) (k : ℕ) (σ : Perm (Fin n)) :
    psi k σ = chi k σ + (n : ℚ)⁻¹ * LinearMap.trace ℚ (L n) (rho σ * (E * (I * D k))) := by
  rw [psi, chi_def]
  conv_lhs => rw [← one_mul (D k), ← P_add hn]
  rw [add_mul, mul_add, map_add, smul_mul_assoc, mul_smul_comm, map_smul, smul_eq_mul, mul_assoc E]

theorem psi_zero (hn : 0 < n) (σ : Perm (Fin n)) : psi 0 σ = chi 0 σ := by
  rw [psi_eq hn]
  have : (I * D 0 : L n →ₗ[ℚ] L n) = 0 := I_D0
  rw [this, mul_zero, mul_zero, map_zero, mul_zero, add_zero]

theorem psi_succ (hn : 0 < n) (k : ℕ) (σ : Perm (Fin n)) :
    psi (k + 1) σ = chi (k + 1) σ + chi k σ := by
  rw [psi_eq hn]
  congr 1
  have h1 : (I * D (k + 1) : L n →ₗ[ℚ] L n) = D k * I := I_D k
  have h2 : (I * rho σ : L n →ₗ[ℚ] L n) = rho σ * I := (rho_I σ).symm
  rw [h1, chi_def, P, smul_mul_assoc, mul_smul_comm, map_smul, smul_eq_mul]
  congr 1
  rw [← mul_assoc, ← mul_assoc, LinearMap.trace_mul_comm, ← mul_assoc, ← mul_assoc, h2]
  simp only [mul_assoc]
  rfl

theorem chi_eq_zero {k : ℕ} (hk : n ≤ k) (σ : Perm (Fin n)) : chi k σ = 0 := by
  have h1 : (E * D k : L n →ₗ[ℚ] L n) = D (k + 1) * E := E_D k
  rw [chi_def]
  change LinearMap.trace ℚ (L n) (rho σ * ((n : ℚ)⁻¹ • (I * E) * D k)) = 0
  rw [smul_mul_assoc, mul_assoc, h1, D_eq_zero (by omega), zero_mul, mul_zero,
    smul_zero, mul_zero, map_zero]

theorem hookPoly_mul {m : ℕ} (μ : m.Partition) (hm : 0 < m) :
    (1 + X) * hookPoly μ = (μ.parts.map fun a => 1 - (-X) ^ a).prod := by
  have hcard : 0 < μ.parts.card := by
    rw [Multiset.card_pos]
    intro h
    have := μ.parts_sum
    rw [h, Multiset.sum_zero] at this
    omega
  unfold hookPoly
  rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hcard]
  have : (1 + X : ℤ[X]) ^ μ.parts.card = (μ.parts.map fun _ => (1 + X : ℤ[X])).prod := by
    rw [Multiset.map_const', Multiset.prod_replicate]
  rw [this, ← Multiset.prod_map_mul]
  congr 1
  refine Multiset.map_congr rfl fun a _ => ?_
  rw [← mul_neg_geom_sum, sub_neg_eq_add]

theorem one_add_X_ne_zero' : (1 + X : ℚ[X]) ≠ 0 := by
  intro h
  have := congrArg (eval 0) h
  simp at this

theorem chi_eq_hookChar' {k : ℕ} (hk : k < n) (σ : Perm (Fin n)) :
    chi k σ = ((hookPoly σ.partition).coeff k : ℚ) := by
  have hn : 0 < n := by omega
  set Q : ℚ[X] := ∑ j ∈ range n, C (chi j σ) * X ^ j with hQdef
  have hQ : ∀ j, Q.coeff j = chi j σ := by
    intro j
    rw [hQdef, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [sum_ite_eq]
    split_ifs with h
    · rfl
    · rw [chi_eq_zero (by simpa using h)]
  have hmain : (1 + X) * Q = (Phi σ).map (Int.castRingHom ℚ) := by
    ext j
    rw [coeff_map, eq_intCast, ← psi_eq_coeff]
    rcases j with _ | j
    · rw [add_mul, one_mul, coeff_add, coeff_X_mul_zero, add_zero, hQ, psi_zero hn]
    · rw [add_mul, one_mul, coeff_add, coeff_X_mul, hQ, hQ, psi_succ hn]
  have hhook : (1 + X) * (hookPoly σ.partition).map (Int.castRingHom ℚ) =
      (Phi σ).map (Int.castRingHom ℚ) := by
    have h := hookPoly_mul σ.partition (by simpa using hn)
    rw [Phi_partition, ← h, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_one,
      Polynomial.map_X]
  have hQeq : Q = (hookPoly σ.partition).map (Int.castRingHom ℚ) :=
    mul_left_cancel₀ one_add_X_ne_zero' (hmain.trans hhook.symm)
  rw [← hQ k, hQeq, coeff_map, eq_intCast]

theorem chiPoly_eq (hn : 0 < n) (σ : Perm (Fin n)) :
    ∑ j ∈ range n, C (chi j σ) * X ^ j = (hookPoly σ.partition).map (Int.castRingHom ℚ) := by
  set Q : ℚ[X] := ∑ j ∈ range n, C (chi j σ) * X ^ j with hQdef
  have hQ : ∀ j, Q.coeff j = chi j σ := by
    intro j
    rw [hQdef, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [sum_ite_eq]
    split_ifs with h
    · rfl
    · rw [chi_eq_zero (by simpa using h)]
  have hmain : (1 + X) * Q = (Phi σ).map (Int.castRingHom ℚ) := by
    ext j
    rw [coeff_map, eq_intCast, ← psi_eq_coeff]
    rcases j with _ | j
    · rw [add_mul, one_mul, coeff_add, coeff_X_mul_zero, add_zero, hQ, psi_zero hn]
    · rw [add_mul, one_mul, coeff_add, coeff_X_mul, hQ, hQ, psi_succ hn]
  have hhook : (1 + X) * (hookPoly σ.partition).map (Int.castRingHom ℚ) =
      (Phi σ).map (Int.castRingHom ℚ) := by
    have h := hookPoly_mul σ.partition (by simpa using hn)
    rw [Phi_partition, ← h, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_one,
      Polynomial.map_X]
  have hQeq : Q = (hookPoly σ.partition).map (Int.castRingHom ℚ) :=
    mul_left_cancel₀ one_add_X_ne_zero' (hmain.trans hhook.symm)
  exact hQeq

/-! ## Transitivity of `S_n` on subsets -/

theorem pm_eq_of_mapsTo' {σ : Perm (Fin n)} {S S' : Finset (Fin n)} (h : ∀ x ∈ S, σ x ∈ S')
    (hc : S.card = S'.card) : pm σ S = S' := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [mem_pm] at hx
    simpa using h _ hx
  · rw [card_pm, hc]

theorem exists_pm_eq {S S' : Finset (Fin n)} (hc : S.card = S'.card) :
    ∃ σ : Perm (Fin n), pm σ S = S' := by
  have e : {x // x ∈ S} ≃ {x // x ∈ S'} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hc])
  have f : {x // ¬ x ∈ S} ≃ {x // ¬ x ∈ S'} :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, Fintype.card_coe,
        Fintype.card_coe, hc])
  refine ⟨Equiv.subtypeCongr e f, pm_eq_of_mapsTo' (fun x hx => ?_) hc⟩
  have : Equiv.subtypeCongr e f x = e ⟨x, hx⟩ := by
    simp [Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_pos hx]
  rw [this]; exact (e ⟨x, hx⟩).property

theorem pm_swap {x y : Fin n} {A : Finset (Fin n)} (h : x ∈ A ↔ y ∈ A) : pm (swap x y) A = A := by
  apply pm_eq_of_mapsTo
  intro z hz
  rw [swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact h.mp hz
  · subst h2; exact h.mpr hz
  · exact hz

theorem exists_pm_eq3 {S S' : Finset (Fin n)} (hc : S.card = S'.card) {s t s' t' : Fin n}
    (hs : s ∈ S) (ht : t ∉ S) (hs' : s' ∈ S') (ht' : t' ∉ S') :
    ∃ σ : Perm (Fin n), pm σ S = S' ∧ σ s = s' ∧ σ t = t' := by
  obtain ⟨σ₁, h₁⟩ := exists_pm_eq hc
  have ha : σ₁ s ∈ S' := by rw [← h₁]; exact Finset.mem_map_of_mem _ hs
  have hb : σ₁ t ∉ S' := by
    rw [← h₁]; intro h; rw [mem_pm] at h; apply ht; simpa using h
  refine ⟨swap (σ₁ t) t' * swap (σ₁ s) s' * σ₁, ?_, ?_, ?_⟩
  · rw [pm_mul, pm_mul, h₁, pm_swap (iff_of_true ha hs'), pm_swap (iff_of_false hb ht')]
  · simp only [Perm.mul_apply, swap_apply_left]
    exact swap_apply_of_ne_of_ne (fun h => hb (by rw [← h]; exact hs'))
      (fun h => ht' (by rw [← h]; exact hs'))
  · simp only [Perm.mul_apply]
    have e : swap (σ₁ s) s' (σ₁ t) = σ₁ t :=
      swap_apply_of_ne_of_ne (fun h : σ₁ t = σ₁ s => hb (by rw [h]; exact ha))
        (fun h : σ₁ t = s' => hb (by rw [h]; exact hs'))
    rw [e, swap_apply_left]

theorem pm_insert_erase (σ : Perm (Fin n)) (S : Finset (Fin n)) (s t : Fin n) :
    pm σ (insert t (S.erase s)) = insert (σ t) ((pm σ S).erase (σ s)) := by
  simp [pm, map_insert, map_erase]

/-! ## The commutant of `rho` in degree `k` -/

/-- `A` commutes with every `rho σ`. -/
def Equivar (A : L n →ₗ[ℚ] L n) : Prop := ∀ σ : Perm (Fin n), rho σ * A = A * rho σ

theorem entry_rel {A : L n →ₗ[ℚ] L n} (hA : Equivar A) (σ : Perm (Fin n))
    (S T : Finset (Fin n)) :
    ((eps σ T : ℤ) : ℚ) * A (Pi.single S 1) T =
      ((eps σ S : ℤ) : ℚ) * A (Pi.single (pm σ S) 1) (pm σ T) := by
  have h := congrArg (fun B : L n →ₗ[ℚ] L n => B (Pi.single S 1) (pm σ T)) (hA σ)
  simp only [Module.End.mul_apply, rho_single, map_smul, Pi.smul_apply, smul_eq_mul,
    rho_apply, pm_inv_pm] at h
  exact h

theorem entry_zero_iff {A : L n →ₗ[ℚ] L n} (hA : Equivar A) (σ : Perm (Fin n))
    (S T : Finset (Fin n)) :
    A (Pi.single (pm σ S) 1) (pm σ T) = 0 → A (Pi.single S 1) T = 0 := by
  intro h
  have := entry_rel hA σ S T
  rw [h, mul_zero] at this
  rcases mul_eq_zero.mp this with h' | h'
  · have := eps_sq σ T; rw [h', zero_mul] at this; exact absurd this zero_ne_one
  · exact h'

theorem graded_entry {k : ℕ} {A : L n →ₗ[ℚ] L n} (hD : D k * A * D k = A) (S T : Finset (Fin n))
    (h : ¬ (S.card = k ∧ T.card = k)) : A (Pi.single S 1) T = 0 := by
  rw [← hD]
  simp only [Module.End.mul_apply, D_apply, D_single]
  by_cases hS : S.card = k
  · rw [if_neg (fun hT => h ⟨hS, hT⟩)]
  · rw [if_neg hS, map_zero]; simp

theorem ext_single {A B : L n →ₗ[ℚ] L n}
    (h : ∀ S T, A (Pi.single S 1) T = B (Pi.single S 1) T) : A = B := by
  apply LinearMap.pi_ext
  intro S x
  have : Pi.single S x = x • (Pi.single S (1 : ℚ) : L n) := by
    rw [← Pi.single_smul]; simp
  rw [this, map_smul, map_smul]
  funext T
  simp only [Pi.smul_apply, h]

theorem vanish {k : ℕ} {S₀ : Finset (Fin n)} (hS₀ : S₀.card = k) {B : L n →ₗ[ℚ] L n}
    (hB : Equivar B) (hD : D k * B * D k = B) (h0 : B (Pi.single S₀ 1) S₀ = 0)
    (h1 : ∀ s₀ ∈ S₀, ∀ t₀ ∉ S₀, B (Pi.single S₀ 1) (insert t₀ (S₀.erase s₀)) = 0) : B = 0 := by
  apply ext_single
  intro S T
  simp only [LinearMap.zero_apply, Pi.zero_apply]
  by_cases hk : S.card = k ∧ T.card = k
  swap; · exact graded_entry hD S T hk
  obtain ⟨hS, hT⟩ := hk
  by_cases h2 : 2 ≤ (S \ T).card
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
    rw [mem_sdiff] at ha hb
    have hpS : pm (swap a b) S = S := pm_swap (by simp [ha.1, hb.1])
    have hpT : pm (swap a b) T = T := pm_swap (by simp [ha.2, hb.2])
    have hrel := entry_rel hB (swap a b) S T
    rw [hpS, hpT] at hrel
    have e1 : eps (swap a b) S = -1 := by
      rw [eps_eq_sign_of hpS (ρ' := swap a b) (fun _ _ => rfl), Perm.sign_swap hab]
      intro x hx
      exact swap_apply_of_ne_of_ne (fun h => hx (h ▸ ha.1)) (fun h => hx (h ▸ hb.1))
    have e2 : eps (swap a b) T = 1 := eps_of_fix fun x hx =>
      swap_apply_of_ne_of_ne (fun h => ha.2 (h ▸ hx)) (fun h => hb.2 (h ▸ hx))
    rw [e1, e2] at hrel
    push_cast at hrel
    linarith
  · have hST : (S \ T).card = (T \ S).card := by
      have h1 := card_sdiff_add_card_inter S T
      have h2 := card_sdiff_add_card_inter T S
      rw [inter_comm] at h2; omega
    by_cases h1' : (S \ T).card = 0
    · have hsub : S ⊆ T := by
        intro x hx; by_contra hxT
        have : x ∈ S \ T := mem_sdiff.mpr ⟨hx, hxT⟩
        rw [card_eq_zero] at h1'; rw [h1'] at this; simp at this
      have hEq : S = T := Finset.eq_of_subset_of_card_le hsub (by omega)
      subst hEq
      obtain ⟨σ, hσ⟩ := exists_pm_eq (hS₀.trans hS.symm)
      apply entry_zero_iff hB σ⁻¹
      rw [← hσ, pm_inv_pm]; exact h0
    · have hc1 : (S \ T).card = 1 := by omega
      obtain ⟨s, hs⟩ := card_eq_one.mp hc1
      obtain ⟨t, ht⟩ := card_eq_one.mp (hST ▸ hc1)
      have hsS : s ∈ S := (mem_sdiff.mp (hs ▸ mem_singleton_self s)).1
      have hsT : s ∉ T := (mem_sdiff.mp (hs ▸ mem_singleton_self s)).2
      have htT : t ∈ T := (mem_sdiff.mp (ht ▸ mem_singleton_self t)).1
      have htS : t ∉ S := (mem_sdiff.mp (ht ▸ mem_singleton_self t)).2
      have hTeq : T = insert t (S.erase s) := by
        ext x
        simp only [mem_insert, mem_erase]
        constructor
        · intro hx
          by_cases hxS : x ∈ S
          · right; refine ⟨fun h => hsT (h ▸ hx), hxS⟩
          · left
            have : x ∈ T \ S := mem_sdiff.mpr ⟨hx, hxS⟩
            rw [ht] at this; simpa using this
        · rintro (rfl | ⟨hxs, hxS⟩)
          · exact htT
          · by_contra hxT
            have : x ∈ S \ T := mem_sdiff.mpr ⟨hxS, hxT⟩
            rw [hs] at this; exact hxs (by simpa using this)
      have hk1 : 1 ≤ k := by rw [← hS]; exact card_pos.mpr ⟨s, hsS⟩
      obtain ⟨s₀, hs₀⟩ : S₀.Nonempty := card_pos.mp (by omega)
      have hkn : S₀.card < n := by
        have := card_lt_univ_of_notMem htS
        simp only [Fintype.card_fin] at this; omega
      obtain ⟨t₀, ht₀⟩ : ∃ t₀, t₀ ∉ S₀ := by
        by_contra hcon
        push Not at hcon
        have : S₀ = univ := eq_univ_of_forall hcon
        rw [this, card_univ, Fintype.card_fin] at hkn; omega
      obtain ⟨σ, hσ, hσs, hσt⟩ := exists_pm_eq3 (hS₀.trans hS.symm) hs₀ ht₀ hsS htS
      apply entry_zero_iff hB σ⁻¹
      have e1 : pm σ⁻¹ S = S₀ := by rw [← hσ, pm_inv_pm]
      have e2 : pm σ⁻¹ T = insert t₀ (S₀.erase s₀) := by
        rw [hTeq, ← hσ, ← hσs, ← hσt, ← pm_insert_erase, pm_inv_pm]
      rw [e1, e2]; exact h1 s₀ hs₀ t₀ ht₀

/-! ## Facts about `P` -/

theorem rho_P (σ : Perm (Fin n)) : rho σ * P = P * rho σ := by
  have h1 : (rho σ * I : L n →ₗ[ℚ] L n) = I * rho σ := rho_I σ
  have h2 : (rho σ * E : L n →ₗ[ℚ] L n) = E * rho σ := rho_E σ
  change rho σ * ((n : ℚ)⁻¹ • (I * E)) = ((n : ℚ)⁻¹ • (I * E)) * rho σ
  rw [mul_smul_comm, smul_mul_assoc, ← mul_assoc, h1, mul_assoc, h2, mul_assoc]

theorem P_D (k : ℕ) : P * D k = D k * (P : L n →ₗ[ℚ] L n) := by
  have h1 : (E * D k : L n →ₗ[ℚ] L n) = D (k + 1) * E := E_D k
  have h2 : (I * D (k + 1) : L n →ₗ[ℚ] L n) = D k * I := I_D k
  change ((n : ℚ)⁻¹ • (I * E)) * D k = D k * ((n : ℚ)⁻¹ • (I * E))
  rw [smul_mul_assoc, mul_smul_comm, mul_assoc, h1, ← mul_assoc, h2, mul_assoc]

theorem P_P (hn : 0 < n) : P * P = (P : L n →ₗ[ℚ] L n) := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hEI : (E * I : L n →ₗ[ℚ] L n) = (n : ℚ) • 1 - I * E := by
    rw [eq_sub_iff_add_eq, add_comm]; exact IE_add_EI
  have hEE : (E * E : L n →ₗ[ℚ] L n) = 0 := EE
  change ((n : ℚ)⁻¹ • (I * E)) * ((n : ℚ)⁻¹ • (I * E)) = (n : ℚ)⁻¹ • (I * E)
  rw [smul_mul_smul_comm, show I * E * (I * E) = I * (E * I) * E by simp only [mul_assoc], hEI,
    mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one,
    show I * (I * E) * E = I * I * (E * E) by simp only [mul_assoc], hEE, mul_zero, sub_zero,
    smul_smul]
  congr 1
  field_simp

theorem rho_mul' (σ τ : Perm (Fin n)) : rho (σ * τ) = rho σ * rho τ := rho_mul σ τ

theorem rho_D' (σ : Perm (Fin n)) (k : ℕ) : rho σ * D k = D k * rho σ := rho_D σ k

theorem D_D' (k : ℕ) : D k * D k = (D k : L n →ₗ[ℚ] L n) := D_D k

theorem trace_D (k : ℕ) : LinearMap.trace ℚ (L n) (D k) = (n.choose k : ℚ) := by
  rw [trace_eq]
  simp only [D_single]
  have : ∀ S : Finset (Fin n), (if S.card = k then (Pi.single S (1 : ℚ) : L n) else 0) S =
      if S.card = k then 1 else 0 := fun S => by split_ifs <;> simp
  simp only [this]
  rw [sum_boole]
  congr 1
  rw [show (univ.filter fun S : Finset (Fin n) => S.card = k) = powersetCard k univ by
      ext S; simp [mem_powersetCard]]
  rw [card_powersetCard, card_univ, Fintype.card_fin]

theorem hookPoly_one :
    hookPoly (1 : Perm (Fin n)).partition = (1 + X) ^ (n - 1) := by
  unfold hookPoly
  rw [Perm.parts_partition]
  simp

theorem chi_one {k : ℕ} (hk : k < n) : chi k (1 : Perm (Fin n)) = ((n - 1).choose k : ℚ) := by
  rw [chi_eq_hookChar' hk, hookPoly_one, coeff_one_add_X_pow]
  push_cast; rfl

theorem trace_PD {k : ℕ} (hk : k < n) :
    LinearMap.trace ℚ (L n) (P * D k) = ((n - 1).choose k : ℚ) := by
  rw [← chi_one hk, chi_def, rho_one]; rfl

/-- In degree `k`, an equivariant `A` with `A P = A` is a multiple of `P ∘ D k`. -/
theorem commutant {k : ℕ} (hk : k < n) {A : L n →ₗ[ℚ] L n} (hA : Equivar A)
    (hD : D k * A * D k = A) (hP : A * P = A) : ∃ α : ℚ, A = α • (P * D k) := by
  have hn : 0 < n := by omega
  obtain ⟨S₀, -, hS₀⟩ := exists_subset_card_eq (s := (univ : Finset (Fin n))) (n := k)
    (by simp; omega)
  have eqD : Equivar (D k : L n →ₗ[ℚ] L n) := fun σ => rho_D' σ k
  have eqPD : Equivar (P * D k : L n →ₗ[ℚ] L n) := fun σ => by
    rw [← mul_assoc, rho_P, mul_assoc, rho_D', mul_assoc]
  have gD : D k * D k * D k = (D k : L n →ₗ[ℚ] L n) := by rw [D_D', D_D']
  have gPD : D k * (P * D k) * D k = (P * D k : L n →ₗ[ℚ] L n) := by
    rw [← mul_assoc (D k) P, ← P_D]; simp only [mul_assoc, D_D']
  have eq_comb : ∀ (B C : L n →ₗ[ℚ] L n) (b c : ℚ), Equivar B → Equivar C →
      Equivar (b • B - c • C) := fun B C b c hB hC σ => by
    rw [mul_sub, sub_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, hB σ,
      hC σ]
  have g_comb : ∀ (B C : L n →ₗ[ℚ] L n) (b c : ℚ), D k * B * D k = B → D k * C * D k = C →
      D k * (b • B - c • C) * D k = b • B - c • C := fun B C b c hB hC => by
    rw [mul_sub, sub_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, hB, hC]
  have hDS₀ : (D k : L n →ₗ[ℚ] L n) (Pi.single S₀ 1) = Pi.single S₀ 1 := by
    rw [D_single, if_pos hS₀]
  have hchoose : ((n - 1).choose k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  -- `P ∘ D k` is not a multiple of `D k` when `k ≥ 1`
  have hnot : 1 ≤ k → ∀ c : ℚ, P * D k ≠ c • (D k : L n →ₗ[ℚ] L n) := by
    intro hk1 c hc
    have h1 : (P * D k : L n →ₗ[ℚ] L n) = c • (P * D k) := by
      calc (P * D k : L n →ₗ[ℚ] L n) = P * (P * D k) := by rw [← mul_assoc, P_P hn]
        _ = c • (P * D k) := by rw [hc, mul_smul_comm, ← hc]
    have ht := congrArg (LinearMap.trace ℚ (L n)) hc
    rw [trace_PD hk, map_smul, trace_D, smul_eq_mul] at ht
    have hc1 : c = 1 := by
      have := congrArg (LinearMap.trace ℚ (L n)) h1
      rw [map_smul, trace_PD hk, smul_eq_mul] at this
      have := mul_right_cancel₀ hchoose (this.symm.trans (one_mul _).symm)
      exact this
    rw [hc1, one_mul] at ht
    have hp := Nat.choose_succ_succ' (n - 1) (k - 1)
    rw [Nat.sub_add_cancel hk1, Nat.sub_add_cancel hn] at hp
    have hpos : 0 < (n - 1).choose (k - 1) := Nat.choose_pos (by omega)
    have : ((n - 1).choose k : ℚ) = ((n - 1).choose (k - 1) : ℚ) + ((n - 1).choose k : ℚ) := by
      rw [← Nat.cast_add, ← hp]; exact ht
    have : ((n - 1).choose (k - 1) : ℚ) = 0 := by linarith
    exact hpos.ne' (by exact_mod_cast this)
  by_cases hk0 : k = 0
  · subst hk0
    -- one coordinate suffices
    have hv : ∀ B : L n →ₗ[ℚ] L n, Equivar B → D 0 * B * D 0 = B →
        B (Pi.single S₀ 1) S₀ = 0 → B = 0 := fun B hB hBD h0 =>
      vanish hS₀ hB hBD h0 fun s₀ hs₀ => by simp [card_eq_zero.mp hS₀] at hs₀
    set a := A (Pi.single S₀ 1) S₀
    set c := (P * D 0 : L n →ₗ[ℚ] L n) (Pi.single S₀ 1) S₀
    have hPD : (P * D 0 : L n →ₗ[ℚ] L n) = c • D 0 := by
      have := hv (1 • (P * D 0) - c • D 0) (eq_comb _ _ _ _ eqPD eqD) (g_comb _ _ _ _ gPD gD)
        (by simp [hDS₀, c])
      rw [one_smul, sub_eq_zero] at this; exact this
    have hc : c = 1 := by
      have ht := congrArg (LinearMap.trace ℚ (L n)) hPD
      rw [trace_PD hk, map_smul, trace_D, smul_eq_mul] at ht
      simpa using ht.symm
    have hA' := hv (1 • A - a • D 0) (eq_comb _ _ _ _ hA eqD) (g_comb _ _ _ _ hD gD)
      (by simp [hDS₀, a])
    rw [one_smul, sub_eq_zero] at hA'
    exact ⟨a, by rw [hA', hPD, hc, one_smul]⟩
  have hk1 : 1 ≤ k := by omega
  obtain ⟨s₀, hs₀⟩ : S₀.Nonempty := card_pos.mp (by omega)
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, t₀ ∉ S₀ := by
    by_contra hcon
    push Not at hcon
    have : S₀ = univ := eq_univ_of_forall hcon
    rw [this, card_univ, Fintype.card_fin] at hS₀; omega
  set T₁ := insert t₀ (S₀.erase s₀)
  -- all off-diagonal coordinates of the same type are tied to `T₁`
  have hv : ∀ B : L n →ₗ[ℚ] L n, Equivar B → D k * B * D k = B →
      B (Pi.single S₀ 1) S₀ = 0 → B (Pi.single S₀ 1) T₁ = 0 → B = 0 := by
    intro B hB hBD h0 h1
    apply vanish hS₀ hB hBD h0
    intro s hs t ht
    obtain ⟨σ, hσ, hσs, hσt⟩ := exists_pm_eq3 rfl hs₀ ht₀ hs ht
    apply entry_zero_iff hB σ⁻¹
    have e1 : pm σ⁻¹ S₀ = S₀ := by rw [← hσ, pm_inv_pm, hσ]
    have e2 : pm σ⁻¹ (insert t (S₀.erase s)) = T₁ := by
      rw [← hσ, ← hσs, ← hσt, ← pm_insert_erase, pm_inv_pm]
    rw [e1, e2]; exact h1
  set p := (P * D k : L n →ₗ[ℚ] L n) (Pi.single S₀ 1) T₁
  have hT₁ : T₁ ≠ S₀ := by
    intro h
    have : t₀ ∈ T₁ := mem_insert_self _ _
    rw [h] at this; exact ht₀ this
  have hp : p ≠ 0 := by
    intro hp0
    set c := (P * D k : L n →ₗ[ℚ] L n) (Pi.single S₀ 1) S₀
    apply hnot hk1 c
    have := hv (1 • (P * D k) - c • D k) (eq_comb _ _ _ _ eqPD eqD) (g_comb _ _ _ _ gPD gD)
      (by simp [hDS₀, c]) (by
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, one_smul, Pi.sub_apply,
          Pi.smul_apply, smul_eq_mul, hDS₀, Pi.single_apply, if_neg hT₁, mul_zero, sub_zero]
        simpa [p, hDS₀] using hp0)
    rwa [one_smul, sub_eq_zero] at this
  set α := A (Pi.single S₀ 1) T₁ / p
  set B := 1 • A - α • (P * D k)
  have hB : Equivar B := eq_comb _ _ _ _ hA eqPD
  have hBD : D k * B * D k = B := g_comb _ _ _ _ hD gPD
  set β := B (Pi.single S₀ 1) S₀
  have hBeq : B = β • D k := by
    have := hv (1 • B - β • D k) (eq_comb _ _ _ _ hB eqD) (g_comb _ _ _ _ hBD gD)
      (by simp [hDS₀, β]) (by
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, one_smul, hDS₀, Pi.sub_apply,
          Pi.smul_apply, smul_eq_mul, Pi.single_apply, if_neg hT₁, mul_zero, sub_zero, B]
        simp only [α]
        field_simp; ring)
    rwa [one_smul, sub_eq_zero] at this
  have hPDP : P * D k * P = (P * D k : L n →ₗ[ℚ] L n) := by
    rw [mul_assoc, ← P_D, ← mul_assoc, P_P hn]
  have hBP : B * P = B := by
    simp only [B, one_smul, sub_mul, smul_mul_assoc, hP, hPDP]
  have hβ : β = 0 := by
    by_contra hβ
    apply hnot hk1 1
    rw [hBeq, smul_mul_assoc] at hBP
    have := congrArg (fun F => β⁻¹ • F) hBP
    simp only [smul_smul, inv_mul_cancel₀ hβ, one_smul] at this
    rw [P_D, this, one_smul]
  rw [hβ, zero_smul] at hBeq
  refine ⟨α, ?_⟩
  have : B = 0 := hBeq
  simp only [B, one_smul, sub_eq_zero] at this
  exact this

/-! ## The class-sum identity -/

theorem chi_conj (k : ℕ) (g b : Perm (Fin n)) : chi k (g * b * g⁻¹) = chi k b := by
  rw [chi_def, chi_def, rho_mul', rho_mul', mul_assoc, mul_assoc, LinearMap.trace_mul_comm]
  have h1 : rho g⁻¹ * (P * D k) = P * D k * rho g⁻¹ := by
    rw [← mul_assoc, rho_P, mul_assoc, rho_D', mul_assoc]
  rw [h1, mul_assoc, mul_assoc, ← rho_mul', inv_mul_cancel, rho_one]
  simp only [mul_assoc]
  rfl

theorem sum_conj' {k : ℕ} (hk : k < n) (a b : Perm (Fin n)) :
    ((n - 1).choose k : ℚ) * ∑ g : Perm (Fin n), chi k (a * (g * b * g⁻¹)) =
      (n.factorial : ℚ) * chi k a * chi k b := by
  set T : L n →ₗ[ℚ] L n := ∑ g : Perm (Fin n), rho (g * b * g⁻¹) with hTdef
  have hT : Equivar T := by
    intro h
    rw [hTdef, mul_sum, sum_mul]
    conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft h)]
    refine sum_congr rfl fun g _ => ?_
    simp only [Equiv.coe_mulLeft, ← rho_mul']
    congr 1
    group
  have hTD : D k * T = T * D k := by
    rw [hTdef, mul_sum, sum_mul]
    exact sum_congr rfl fun g _ => (rho_D' _ k).symm
  set A := T * (P * D k) with hAdef
  have hA : Equivar A := fun σ => by
    simp only [hAdef, ← mul_assoc]
    rw [hT σ]
    simp only [mul_assoc]
    rw [← mul_assoc (rho σ) P, rho_P, mul_assoc P, rho_D']
  have hAD : D k * A * D k = A := by
    rw [hAdef, ← mul_assoc, hTD]
    simp only [mul_assoc]
    rw [← mul_assoc (D k) P, ← P_D]
    simp only [mul_assoc, D_D']
  have hAP : A * P = A := by
    rw [hAdef, mul_assoc, mul_assoc, ← P_D, ← mul_assoc P, P_P (by omega)]
  obtain ⟨α, hα⟩ := commutant hk hA hAD hAP
  have htrA : LinearMap.trace ℚ (L n) A = (n.factorial : ℚ) * chi k b := by
    rw [hAdef, hTdef, sum_mul, map_sum]
    have : ∀ g : Perm (Fin n), LinearMap.trace ℚ (L n) (rho (g * b * g⁻¹) * (P * D k)) =
        chi k b := fun g => by rw [← chi_def, chi_conj]
    simp only [this, sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  have hα' : α * ((n - 1).choose k : ℚ) = (n.factorial : ℚ) * chi k b := by
    rw [← htrA, hα, map_smul, trace_PD hk, smul_eq_mul]
  have hsum : ∑ g : Perm (Fin n), chi k (a * (g * b * g⁻¹)) = α * chi k a := by
    have : ∑ g : Perm (Fin n), chi k (a * (g * b * g⁻¹)) =
        LinearMap.trace ℚ (L n) (rho a * A) := by
      rw [hAdef, hTdef, sum_mul, mul_sum, map_sum]
      refine sum_congr rfl fun g _ => ?_
      rw [chi_def, rho_mul', mul_assoc]
    rw [this, hα, mul_smul_comm, map_smul, smul_eq_mul, ← chi_def]
  rw [hsum, ← mul_assoc, mul_comm _ α, hα']
  ring

/-! ## The centraliser order -/

theorem zeeM_partition (τ : Perm (Fin n)) :
    zeeM τ.partition.parts = (Fintype.card (Fin n) - τ.cycleType.sum).factorial *
      τ.cycleType.prod * ∏ m ∈ τ.cycleType.toFinset, (τ.cycleType.count m).factorial := by
  set cT := τ.cycleType
  set r := Fintype.card (Fin n) - cT.sum with hr
  have hparts : τ.partition.parts = cT + Multiset.replicate r 1 := by
    rw [Perm.parts_partition, hr, Perm.sum_cycleType]
  have h1 : (1 : ℕ) ∉ cT.toFinset := by
    intro h
    have := Perm.two_le_of_mem_cycleType (Multiset.mem_toFinset.mp h)
    omega
  unfold zeeM
  rw [hparts, prod_mul_distrib, ← Finset.prod_multiset_count, Multiset.prod_add,
    Multiset.prod_replicate, one_pow, mul_one]
  have hsub : (cT + Multiset.replicate r 1).toFinset ⊆ insert 1 cT.toFinset := by
    intro k hk
    rw [Multiset.mem_toFinset, Multiset.mem_add] at hk
    rcases hk with hk | hk
    · exact mem_insert_of_mem (Multiset.mem_toFinset.mpr hk)
    · rw [Multiset.eq_of_mem_replicate hk]; exact mem_insert_self _ _
  rw [Finset.prod_subset hsub (fun k _ hk => by
      rw [Multiset.mem_toFinset, ← Multiset.count_eq_zero] at hk; rw [hk]; rfl),
    prod_insert h1]
  have hc1 : (cT + Multiset.replicate r 1).count 1 = r := by
    rw [Multiset.count_add, Multiset.count_replicate_self,
      Multiset.count_eq_zero.mpr (fun h => h1 (Multiset.mem_toFinset.mpr h)), zero_add]
  rw [hc1]
  have : ∏ k ∈ cT.toFinset, ((cT + Multiset.replicate r 1).count k).factorial =
      ∏ k ∈ cT.toFinset, (cT.count k).factorial := by
    refine prod_congr rfl fun k hk => ?_
    have hk1 : k ≠ 1 := fun h => h1 (h ▸ hk)
    rw [Multiset.count_add, Multiset.count_replicate, if_neg (Ne.symm hk1), add_zero]
  rw [this]
  ring

/-! ## The lemmas used by the assembly -/

theorem chi_eq_hookChar {k : ℕ} (hk : k < n) (σ : Perm (Fin n)) :
    chi k σ = ((hookPoly σ.partition).coeff k : ℚ) := chi_eq_hookChar' hk σ

theorem sum_conj {k : ℕ} (hk : k < n) (a b : Perm (Fin n)) :
    ((n - 1).choose k : ℚ) * ∑ g : Perm (Fin n), chi k (a * (g * b * g⁻¹)) =
      (n.factorial : ℚ) * chi k a * chi k b := sum_conj' hk a b

theorem sum_alt_chi (hn : 0 < n) (σ : Perm (Fin n)) :
    ∑ k ∈ range n, (-1 : ℚ) ^ k * chi k σ =
      if σ.partition.parts = {n} then (n : ℚ) else 0 := by
  have h := congrArg (eval (-1)) (chiPoly_eq hn σ)
  rw [eval_finsetSum] at h
  simp only [eval_mul, eval_C, eval_pow, eval_X] at h
  rw [show (-1 : ℚ) = ((-1 : ℤ) : ℚ) by norm_num, eval_intCast_map] at h
  simp only [eq_intCast, Int.cast_neg, Int.cast_one] at h
  rw [show ∑ k ∈ range n, (-1 : ℚ) ^ k * chi k σ = ∑ k ∈ range n, chi k σ * (-1) ^ k from
    sum_congr rfl fun _ _ => mul_comm _ _, h]
  have hsum : σ.partition.parts.sum = n := by
    rw [σ.partition.parts_sum, Fintype.card_fin]
  have hev : eval (-1) (hookPoly σ.partition) =
      0 ^ (σ.partition.parts.card - 1) * σ.partition.parts.prod := by
    unfold hookPoly
    rw [eval_mul, eval_pow, eval_add, eval_one, eval_X, eval_multiset_prod, Multiset.map_map]
    norm_num
    left
    congr 1
    refine Multiset.map_congr rfl fun m _ => ?_
    simp [eval_finsetSum]
  rw [hev]
  split_ifs with hp
  · rw [hp]; simp
  · have hc : σ.partition.parts.card ≠ 1 := by
      intro hc
      obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hc
      rw [ha, Multiset.sum_singleton] at hsum
      exact hp (by rw [ha, hsum])
    have hc0 : σ.partition.parts.card ≠ 0 := by
      intro hc0
      rw [Multiset.card_eq_zero.mp hc0, Multiset.sum_zero] at hsum
      omega
    rw [zero_pow (by omega)]
    simp

theorem M_eq (hn : 0 < n) (μ ν : n.Partition) :
    (M n μ ν : ℚ) = ∑ b ∈ univ.filter (fun b : Perm (Fin n) => b.partition.parts = ν.parts),
      if (rep μ * b⁻¹).partition.parts = {n} then (1 : ℚ) else 0 := by
  have hcoeff : ∀ (lam : n.Partition) (y : Perm (Fin n)),
      (classSum n lam).coeff y = if y.partition.parts = lam.parts then 1 else 0 := by
    intro lam y
    unfold classSum
    rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    simp only [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    rw [sum_ite_eq']
    simp
  unfold M
  rw [show classSum n ν = ∑ b ∈ univ.filter (fun b : Perm (Fin n) => b.partition.parts = ν.parts),
      MonoidAlgebra.single b (1 : ℤ) from rfl]
  rw [mul_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Int.cast_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [MonoidAlgebra.coeff_mul_single_apply, hcoeff, Nat.Partition.indiscrete_parts hn.ne']
  split_ifs <;> simp

theorem class_sum (τ₀ : Perm (Fin n)) (f : Perm (Fin n) → ℚ) :
    (zeeM τ₀.partition.parts : ℚ) *
        ∑ b ∈ univ.filter (fun b : Perm (Fin n) => b.partition.parts = τ₀.partition.parts), f b =
      ∑ g : Perm (Fin n), f (g * τ₀ * g⁻¹) := by
  have hsc := Finset.sum_comp (s := (univ : Finset (Perm (Fin n)))) f
    (fun g => g * τ₀ * g⁻¹)
  rw [hsc]
  have himage : univ.image (fun g : Perm (Fin n) => g * τ₀ * g⁻¹) =
      univ.filter (fun b : Perm (Fin n) => b.partition.parts = τ₀.partition.parts) := by
    ext b
    simp only [mem_image, mem_univ, true_and, mem_filter]
    rw [← Nat.Partition.ext_iff, eq_comm, ← Perm.partition_eq_of_isConj, isConj_iff]
  rw [himage, mul_sum]
  refine sum_congr rfl fun b hb => ?_
  rw [nsmul_eq_mul]
  congr 1
  rw [mem_filter] at hb
  obtain ⟨h, rfl⟩ : ∃ h : Perm (Fin n), h * τ₀ * h⁻¹ = b := by
    rw [← isConj_iff, Perm.partition_eq_of_isConj, Nat.Partition.ext_iff, hb.2]
  have hcard : #{g ∈ (univ : Finset (Perm (Fin n))) | g * τ₀ * g⁻¹ = h * τ₀ * h⁻¹} =
      #{c ∈ (univ : Finset (Perm (Fin n))) | c * τ₀ = τ₀ * c} := by
    refine Finset.card_bij (fun g _ => h⁻¹ * g) ?_ ?_ ?_
    · intro g hg
      simp only [mem_filter, mem_univ, true_and] at hg ⊢
      have : h⁻¹ * (g * τ₀ * g⁻¹) * h = τ₀ := by rw [hg]; group
      calc h⁻¹ * g * τ₀ = h⁻¹ * (g * τ₀ * g⁻¹) * h * (h⁻¹ * g) := by group
        _ = τ₀ * (h⁻¹ * g) := by rw [this]
    · intro a _ b _ hab; simpa using hab
    · intro c hc
      refine ⟨h * c, ?_, by group⟩
      simp only [mem_filter, mem_univ, true_and] at hc ⊢
      calc h * c * τ₀ * (h * c)⁻¹ = h * (c * τ₀) * c⁻¹ * h⁻¹ := by group
        _ = h * τ₀ * h⁻¹ := by rw [hc]; group
  rw [hcard]
  have hc2 : Nat.card (Subgroup.centralizer {τ₀}) =
      #{c ∈ (univ : Finset (Perm (Fin n))) | c * τ₀ = τ₀ * c} := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun c => Subgroup.mem_centralizer_singleton_iff)
  rw [← hc2, Perm.nat_card_centralizer τ₀]
  rw [zeeM_partition τ₀]

theorem chi_inv {k : ℕ} (hk : k < n) (σ : Perm (Fin n)) : chi k σ⁻¹ = chi k σ := by
  rw [chi_eq_hookChar' hk, chi_eq_hookChar' hk]
  have : σ⁻¹.partition = σ.partition :=
    Perm.partition_eq_of_isConj.mp (Perm.isConj_iff_cycleType_eq.mpr (Perm.cycleType_inv σ))
  rw [this]

theorem hookPoly_partition_eq {σ : Perm (Fin n)} {μ : n.Partition}
    (h : σ.partition.parts = μ.parts) (k : ℕ) :
    (hookPoly σ.partition).coeff k = hookChar k μ := by
  unfold hookChar hookPoly
  rw [h]

theorem zeeM_pos (s : Multiset ℕ) (hs : ∀ m ∈ s, 0 < m) : 0 < zeeM s := by
  unfold zeeM
  refine Finset.prod_pos fun k hk => ?_
  exact Nat.mul_pos (pow_pos (hs k (Multiset.mem_toFinset.mp hk)) _) (Nat.factorial_pos _)

/-! ## Assembly -/

theorem bridge_aux (hn : 0 < n) (μ ν : n.Partition) :
    (M n μ ν : ℚ) = bridgeFormula n μ ν := by
  classical
  set σ := rep μ
  set τ₀ := rep ν
  have hσ : σ.partition.parts = μ.parts := Classical.choose_spec (exists_rep μ)
  have hτ : τ₀.partition.parts = ν.parts := Classical.choose_spec (exists_rep ν)
  have hz : (zee ν : ℚ) ≠ 0 := by
    have := zeeM_pos ν.parts fun m hm => ν.parts_pos hm
    exact_mod_cast this.ne'
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  -- the indicator of `n`-cycles through the alternating sum of the `χ_k`
  have hind : ∀ y : Perm (Fin n), (if y.partition.parts = {n} then (1 : ℚ) else 0) =
      (n : ℚ)⁻¹ * ∑ k ∈ range n, (-1 : ℚ) ^ k * chi k y := by
    intro y
    rw [sum_alt_chi hn]
    split_ifs <;> simp [hn']
  rw [M_eq hn, ← hτ]
  have key := class_sum τ₀ (fun b => if (σ * b⁻¹).partition.parts = {n} then (1 : ℚ) else 0)
  rw [hτ] at key ⊢
  have hzz : (zeeM ν.parts : ℚ) = zee ν := rfl
  rw [hzz] at key
  rw [show (∑ b ∈ univ.filter (fun b : Perm (Fin n) => b.partition.parts = ν.parts),
      if (σ * b⁻¹).partition.parts = {n} then (1 : ℚ) else 0) =
      (zee ν : ℚ)⁻¹ * ∑ g : Perm (Fin n),
        (if (σ * (g * τ₀ * g⁻¹)⁻¹).partition.parts = {n} then (1 : ℚ) else 0) by
    rw [← key]; field_simp]
  simp_rw [hind, ← mul_sum]
  rw [sum_comm]
  have hconj : ∀ k ∈ range n, ∑ g : Perm (Fin n), (-1 : ℚ) ^ k * chi k (σ * (g * τ₀ * g⁻¹)⁻¹) =
      (-1 : ℚ) ^ k * ((n.factorial : ℚ) * chi k σ * chi k τ₀ / ((n - 1).choose k : ℚ)) := by
    intro k hk
    have hk' := mem_range.mp hk
    have hc : ((n - 1).choose k : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega)).ne'
    rw [← mul_sum]
    congr 1
    have := sum_conj hk' σ τ₀⁻¹
    simp only [mul_inv_rev, inv_inv, ← mul_assoc] at this ⊢
    rw [chi_inv hk'] at this
    rw [eq_div_iff hc, mul_comm, this]
  rw [sum_congr rfl hconj]
  unfold bridgeFormula
  rw [mul_sum, mul_sum, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hk' := mem_range.mp hk
  rw [chi_eq_hookChar hk', chi_eq_hookChar hk', hookPoly_partition_eq hσ,
    hookPoly_partition_eq hτ]
  have hfac : (n.factorial : ℚ) = n * (n - 1).factorial := by
    rw [← Nat.mul_factorial_pred hn.ne']; push_cast; ring
  rw [hfac]
  field_simp

end Br

theorem bridge (n : ℕ) (hn : 0 < n) (μ ν : n.Partition) :
    (M n μ ν : ℚ) = bridgeFormula n μ ν :=
  Br.bridge_aux hn μ ν

end StanleySnf
