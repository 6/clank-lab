import GR22.Spec

/-!
# Unit C: the reciprocity argument

(unit C). From the three specialization statements of `Spec.lean`
(`AtAComplete`, `AtAPlethysm`, `SchurAtA`) we prove `FullEndpoint`.

Reversal device: the two-variable Laurent ring `ℚ[ℤ × ℤ]` (`AddMonoidAlgebra`), which has no
zero divisors (`UniqueSums (ℤ × ℤ)`), with two ring maps from `ℚ[x, y]`: `unitC_E` (the
inclusion) and `unitC_I` (the inclusion composed with `x, y ↦ 1/x, 1/y`). Both are
`mapDomain` along injective exponent maps, so their coefficients are read off directly.
-/

noncomputable section
namespace GR22

open MvPolynomial

/-! ## The Laurent ring and the two embeddings -/

/-- Laurent polynomials in `x, y`. -/
abbrev unitC_L := AddMonoidAlgebra ℚ (ℤ × ℤ)

/-- Exponent vectors of `ℚ[x, y]` inside `ℤ × ℤ`. -/
def unitC_emb : (Fin 2 →₀ ℕ) →+ ℤ × ℤ where
  toFun m := ((m 0 : ℤ), (m 1 : ℤ))
  map_zero' := by simp
  map_add' m n := by simp

/-- Negated exponent vectors (the inversion `x, y ↦ 1/x, 1/y`). -/
def unitC_nemb : (Fin 2 →₀ ℕ) →+ ℤ × ℤ := -unitC_emb

lemma unitC_emb_apply (m : Fin 2 →₀ ℕ) : unitC_emb m = ((m 0 : ℤ), (m 1 : ℤ)) := rfl

lemma unitC_nemb_apply (m : Fin 2 →₀ ℕ) : unitC_nemb m = (-(m 0 : ℤ), -(m 1 : ℤ)) := rfl

lemma unitC_emb_injective : Function.Injective unitC_emb := by
  intro m n h
  simp only [unitC_emb_apply, Prod.mk.injEq, Nat.cast_inj] at h
  ext i; fin_cases i <;> simp [h.1, h.2]

lemma unitC_nemb_injective : Function.Injective unitC_nemb := by
  intro m n h
  simp only [unitC_nemb_apply, Prod.mk.injEq, neg_inj, Nat.cast_inj] at h
  ext i; fin_cases i <;> simp [h.1, h.2]

/-- The inclusion `ℚ[x, y] → ℚ[x^±, y^±]`. -/
def unitC_E : XY →+* unitC_L := AddMonoidAlgebra.mapDomainRingHom ℚ unitC_emb

/-- `p ↦ p(1/x, 1/y)`. -/
def unitC_I : XY →+* unitC_L := AddMonoidAlgebra.mapDomainRingHom ℚ unitC_nemb

lemma unitC_E_coeff (p : XY) (m : Fin 2 →₀ ℕ) : (unitC_E p).coeff (unitC_emb m) = p.coeff m := by
  simp [unitC_E, AddMonoidAlgebra.coeff_mapDomain,
    Finsupp.mapDomain_apply_of_injective unitC_emb_injective]

lemma unitC_I_coeff (p : XY) (m : Fin 2 →₀ ℕ) : (unitC_I p).coeff (unitC_nemb m) = p.coeff m := by
  simp [unitC_I, AddMonoidAlgebra.coeff_mapDomain,
    Finsupp.mapDomain_apply_of_injective unitC_nemb_injective]

lemma unitC_I_coeff_of_pos (p : XY) (n : ℤ × ℤ) (hn : 0 < n.1 ∨ 0 < n.2) :
    (unitC_I p).coeff n = 0 := by
  simp only [unitC_I, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.coeff_mapDomain]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨m, rfl⟩
  simp only [unitC_nemb_apply] at hn
  omega

lemma unitC_E_monomial (m : Fin 2 →₀ ℕ) (r : ℚ) :
    unitC_E (monomial m r) = AddMonoidAlgebra.single (unitC_emb m) r := by
  simp [unitC_E, ← single_eq_monomial, AddMonoidAlgebra.mapDomain_single]

lemma unitC_I_monomial (m : Fin 2 →₀ ℕ) (r : ℚ) :
    unitC_I (monomial m r) = AddMonoidAlgebra.single (unitC_nemb m) r := by
  simp [unitC_I, ← single_eq_monomial, AddMonoidAlgebra.mapDomain_single]

lemma unitC_I_mul_E_X (i : Fin 2) : unitC_I (X i) * unitC_E (X i) = 1 := by
  rw [X, unitC_I_monomial, unitC_E_monomial, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.one_def, unitC_nemb, AddMonoidHom.neg_apply, neg_add_cancel, one_mul]

/-- `T = x y` in the Laurent ring. -/
def unitC_T : unitC_L := unitC_E (x * y)

lemma unitC_frob_recip (k : ℕ) :
    unitC_I ((1 - x ^ k) * (1 - y ^ k)) * unitC_T ^ k = unitC_E ((1 - x ^ k) * (1 - y ^ k)) := by
  have h1 : unitC_I x ^ k * unitC_E x ^ k = 1 := by
    rw [← mul_pow, x, unitC_I_mul_E_X, one_pow]
  have h2 : unitC_I y ^ k * unitC_E y ^ k = 1 := by
    rw [← mul_pow, y, unitC_I_mul_E_X, one_pow]
  simp only [unitC_T, map_mul, map_sub, map_one, map_pow]
  linear_combination (unitC_I y ^ k * unitC_E y ^ k - unitC_E y ^ k) * h1 +
    (1 - unitC_E x ^ k) * h2

lemma unitC_Q_recip : unitC_I Q * unitC_T = unitC_E Q := by
  have h := unitC_frob_recip 1
  simp only [pow_one] at h
  exact h

lemma unitC_xy_recip : unitC_E (x - y) = -(unitC_I (x - y) * unitC_T) := by
  have h1 : unitC_I x * unitC_E x = 1 := unitC_I_mul_E_X 0
  have h2 : unitC_I y * unitC_E y = 1 := unitC_I_mul_E_X 1
  simp only [unitC_T, map_mul, map_sub]
  linear_combination unitC_E y * h1 - unitC_E x * h2

/-! ## Reciprocity of `P = g[(1 - x^k)(1 - y^k)]` -/

/-- Rescaling the value of variable `i` by `t^(i+1)` rescales a weighted-homogeneous `g` of
degree `d` by `t^d`. -/
lemma unitC_eval₂_scale {S : Type*} [CommSemiring S] (f : ℚ →+* S) (u u' : ℕ → S) (t : S)
    (h : ∀ i, u' i = u i * t ^ (i + 1)) (g : SF) (d : ℕ)
    (hg : IsWeightedHomogeneous (fun i : ℕ => i + 1) g d) :
    eval₂ f u' g = eval₂ f u g * t ^ d := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [eval₂_sum, eval₂_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw : Finsupp.weight (fun i : ℕ => i + 1) m = d := hg (mem_support_iff.mp hm)
  rw [Finsupp.weight_apply] at hw
  simp only [eval₂_monomial, Finsupp.prod, h, mul_pow, Finset.prod_mul_distrib, ← pow_mul,
    Finset.prod_pow_eq_pow_sum, mul_assoc]
  congr 3
  rw [← hw, Finsupp.sum]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]

/-- `g[h_a]` at `1 - x - y`, once `h_a ↦ Q` is known. -/
def unitC_P (g : SF) : XY := eval₂ C (fun i : ℕ => frob (i + 1) Q) g

lemma unitC_frob_Q (k : ℕ) : frob k Q = (1 - x ^ k) * (1 - y ^ k) := by
  simp [frob, Q, x, y]

lemma unitC_P_recip (g : SF) (d : ℕ) (hg : IsWeightedHomogeneous (fun i : ℕ => i + 1) g d) :
    unitC_E (unitC_P g) = unitC_I (unitC_P g) * unitC_T ^ d := by
  unfold unitC_P
  rw [eval₂_comp_left, eval₂_comp_left, Subsingleton.elim (unitC_E.comp C) (unitC_I.comp C)]
  apply unitC_eval₂_scale _ _ _ _ _ g d hg
  intro i
  simp only [Function.comp, unitC_frob_Q]
  exact (unitC_frob_recip (i + 1)).symm

lemma unitC_atXOne_x : atXOne x = 1 := by simp [atXOne, x]

lemma unitC_atXOne_Q : atXOne Q = 0 := by simp [Q, unitC_atXOne_x]

lemma unitC_P_atXOne (g : SF) (d : ℕ) (hd : 1 ≤ d)
    (hg : IsWeightedHomogeneous (fun i : ℕ => i + 1) g d) : atXOne (unitC_P g) = 0 := by
  have h0 : constantCoeff g = 0 := by
    by_contra hne
    have := hg (d := 0) hne
    simp at this
    omega
  have hv : (atXOne.toRingHom : XY →+* XY) ∘ (fun i : ℕ => frob (i + 1) Q) = fun _ => 0 := by
    funext i
    simp [unitC_frob_Q, unitC_atXOne_x]
  change atXOne.toRingHom (unitC_P g) = 0
  rw [unitC_P, eval₂_comp_left, hv, eval₂_zero'_apply, h0, map_zero]

/-! ## Partitions with second part at most `2` -/

/-- The shape `(α, 2^β, 1^γ)` (Warning 2.2: the first part is distinguished). -/
def unitC_shape (α β γ : ℕ) : List ℕ := α :: (List.replicate β 2 ++ List.replicate γ 1)

/-- The number of `2`s after the first part. -/
def unitC_beta (μ : List ℕ) : ℕ := μ.tail.count 2

/-- The number of `1`s after the first part. -/
def unitC_gamma (μ : List ℕ) : ℕ := μ.tail.count 1

/-- `μ = (α, 2^β, 1^γ)` with `α ≥ 2`. -/
def unitC_IsHook (μ : List ℕ) : Prop :=
  2 ≤ μ.headI ∧ μ = unitC_shape μ.headI (unitC_beta μ) (unitC_gamma μ)

instance : DecidablePred unitC_IsHook := fun μ => by unfold unitC_IsHook; infer_instance

lemma unitC_beta_shape (α β γ : ℕ) : unitC_beta (unitC_shape α β γ) = β := by
  simp [unitC_beta, unitC_shape, List.count_replicate]

lemma unitC_gamma_shape (α β γ : ℕ) : unitC_gamma (unitC_shape α β γ) = γ := by
  simp [unitC_gamma, unitC_shape, List.count_replicate]

lemma unitC_sum_shape (α β γ : ℕ) : (unitC_shape α β γ).sum = α + 2 * β + γ := by
  simp [unitC_shape, List.sum_replicate]; ring

lemma unitC_isHook_shape {α : ℕ} (hα : 2 ≤ α) (β γ : ℕ) : unitC_IsHook (unitC_shape α β γ) := by
  refine ⟨hα, ?_⟩
  rw [unitC_beta_shape, unitC_gamma_shape]
  rfl

/-- A weakly decreasing list with entries in `{1, 2}` is `2^β 1^γ`. -/
lemma unitC_sorted12 (l : List ℕ) (hs : l.Pairwise (fun a b => b ≤ a))
    (h : ∀ n ∈ l, 1 ≤ n ∧ n ≤ 2) :
    l = List.replicate (l.count 2) 2 ++ List.replicate (l.count 1) 1 := by
  induction l with
  | nil => rfl
  | cons z l ih =>
    rw [List.pairwise_cons] at hs
    have hl := ih hs.2 (fun n hn => h n (List.mem_cons_of_mem _ hn))
    have hz := h z List.mem_cons_self
    rcases (show z = 1 ∨ z = 2 by omega) with rfl | rfl
    · have hall : ∀ b ∈ l, b = 1 := fun b hb => by
        have := hs.1 b hb; have := h b (List.mem_cons_of_mem _ hb); omega
      have h2 : l.count 2 = 0 := List.count_eq_zero.mpr fun hm => by
        have := hall 2 hm; omega
      have hrep := List.eq_replicate_iff.mpr ⟨rfl, hall⟩
      rw [List.count_cons, List.count_cons, h2, List.count_eq_length.mpr fun b hb => (hall b hb).symm, hrep]
      simp [List.replicate_succ]
    · rw [List.count_cons, List.count_cons]
      conv_lhs => rw [hl]
      simp [List.replicate_succ]

/-- Every partition with second part at most `2` is a hook+column shape `(α, 2^β, 1^γ)`
with `α ≥ 2`, or the column `1^N`. -/
lemma unitC_classify {N : ℕ} {μ : List ℕ} (hμ : IsPartitionOf N μ) (h2 : μ.getD 1 0 ≤ 2) :
    unitC_IsHook μ ∨ μ = List.replicate N 1 := by
  obtain ⟨hs, hpos, hsum⟩ := hμ
  cases μ with
  | nil => right; simp at hsum; simp [← hsum]
  | cons α l =>
    rw [List.pairwise_cons] at hs
    have hle : ∀ b ∈ l, b ≤ 2 := by
      cases l with
      | nil => simp
      | cons b0 l' =>
        intro b hb
        simp only [List.getD_cons_succ, List.getD_cons_zero] at h2
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact h2
        · exact (List.rel_of_pairwise_cons hs.2 hb').trans h2
    have hl := unitC_sorted12 l hs.2 fun n hn =>
      ⟨hpos n (List.mem_cons_of_mem _ hn), hle n hn⟩
    by_cases hα : 2 ≤ α
    · left
      refine ⟨hα, ?_⟩
      simp only [List.headI_cons, unitC_beta, unitC_gamma, List.tail_cons, unitC_shape]
      rw [← hl]
    · right
      have hα1 : α = 1 := by have := hpos α List.mem_cons_self; omega
      subst hα1
      have hall : ∀ b ∈ (1 :: l), b = 1 := fun b hb => by
        rcases List.mem_cons.mp hb with rfl | hb'
        · rfl
        · have := hs.1 b hb'; have := hpos b hb; omega
      have hrep := List.eq_replicate_iff.mpr ⟨rfl, hall⟩
      rw [hrep] at hsum ⊢
      simp [List.sum_replicate] at hsum
      rw [← hsum, List.length_cons]

/-! ## Hook+column coefficients as sums over the support -/

/-- For given `(β, γ)`, the hook shapes in the support with these parameters contribute
exactly `hookCoeff N c β γ`, once the column coefficient is known to vanish (the column is
the `α = 1` entry of `hookCoeff`). -/
lemma unitC_hook_sum {N : ℕ} {c : List ℕ →₀ ℚ} (hc : ∀ μ ∈ c.support, IsPartitionOf N μ)
    (hcol : c (List.replicate N 1) = 0) (β γ : ℕ) :
    ∑ μ ∈ c.support,
      (if unitC_IsHook μ ∧ unitC_beta μ = β ∧ unitC_gamma μ = γ then c μ else 0) =
      hookCoeff N c β γ := by
  have key : ∀ μ ∈ c.support, (unitC_IsHook μ ∧ unitC_beta μ = β ∧ unitC_gamma μ = γ) ↔
      (2 * β + γ + 2 ≤ N ∧ μ = unitC_shape (N - 2 * β - γ) β γ) := by
    intro μ hμ
    constructor
    · rintro ⟨⟨hα, hsh⟩, rfl, rfl⟩
      have hsum := (hc μ hμ).2.2
      rw [hsh, unitC_sum_shape] at hsum
      refine ⟨?_, ?_⟩
      · omega
      · have hh : N - 2 * unitC_beta μ - unitC_gamma μ = μ.headI := by omega
        rw [hh]; exact hsh
    · rintro ⟨hN, rfl⟩
      exact ⟨unitC_isHook_shape (by omega) β γ, unitC_beta_shape .., unitC_gamma_shape ..⟩
  rw [Finset.sum_congr rfl fun μ hμ => if_congr (key μ hμ) rfl rfl]
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finsupp.mem_support_iff, ne_eq, ite_not]
  unfold hookCoeff
  dsimp only
  split_ifs with hN h0 hcond hcond <;> try rfl
  · rw [← h0]; congr 1; simp [unitC_shape]; omega
  · congr 1; simp [unitC_shape]; omega
  · omega
  · have hβ : β = 0 := by omega
    have hγ : γ + 1 = N := by omega
    subst hβ
    have : ((N : ℤ) - 2 * ((0 : ℕ) : ℤ) - (γ : ℤ)).toNat = 1 := by omega
    simp only [this, Int.toNat_natCast, List.replicate_zero, List.nil_append]
    rw [← hcol, ← hγ, List.replicate_succ]

lemma unitC_hookCoeff_neg {N : ℕ} (c : List ℕ →₀ ℚ) {β : ℤ} (hβ : β < 0) (γ : ℕ) :
    hookCoeff N c β γ = 0 := by
  unfold hookCoeff
  exact ite_eq_right_iff.mpr fun h => absurd h.1 (by omega)

/-! ## Monomials of `ℚ[x, y]` -/

/-- The exponent vector of `x^u y^v`. -/
def unitC_mono (u v : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 u + Finsupp.single 1 v

lemma unitC_mono_eq_iff {a b u v : ℕ} : unitC_mono a b = unitC_mono u v ↔ a = u ∧ b = v := by
  constructor
  · intro h
    have h0 := congrArg (· 0) h
    have h1 := congrArg (· 1) h
    simp [unitC_mono] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩; rfl

lemma unitC_xy_monomial (a b : ℕ) : x ^ a * y ^ b = monomial (unitC_mono a b) 1 := by
  simp [x, y, X_pow_eq_monomial, monomial_mul_monomial, unitC_mono]

lemma unitC_coeff_xy (a b u v : ℕ) :
    (x ^ a * y ^ b).coeff (unitC_mono u v) = if a = u ∧ b = v then 1 else 0 := by
  rw [unitC_xy_monomial, coeff_monomial]
  exact if_congr unitC_mono_eq_iff rfl rfl

lemma unitC_emb_mono (u v : ℕ) : unitC_emb (unitC_mono u v) = ((u : ℤ), (v : ℤ)) := by
  simp [unitC_emb_apply, unitC_mono]

lemma unitC_nemb_mono (u v : ℕ) : unitC_nemb (unitC_mono u v) = (-(u : ℤ), -(v : ℤ)) := by
  simp [unitC_nemb_apply, unitC_mono]

/-- Coefficient form of `x^d y^d p(1/x, 1/y) = -p`: the coefficients of `p` are
antisymmetric under `(u, v) ↦ (d - u, d - v)` and vanish outside the `d × d` box. -/
lemma unitC_coeff_recip {p : XY} {d : ℕ} (h : unitC_E p = -(unitC_I p * unitC_T ^ d))
    (u v : ℕ) :
    p.coeff (unitC_mono u v) =
      -(if u ≤ d ∧ v ≤ d then p.coeff (unitC_mono (d - u) (d - v)) else 0) := by
  have hT : unitC_T ^ d = AddMonoidAlgebra.single ((d : ℤ), (d : ℤ)) 1 := by
    rw [unitC_T, ← map_pow, mul_pow, unitC_xy_monomial, unitC_E_monomial, unitC_emb_mono]
  have h' := congrArg (fun q => q.coeff (unitC_emb (unitC_mono u v))) h
  simp only [unitC_E_coeff, AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, hT,
    AddMonoidAlgebra.coeff_mul_single_apply, mul_one] at h'
  rw [h']
  congr 1
  split_ifs with huv
  · have he : unitC_emb (unitC_mono u v) + -((d : ℤ), (d : ℤ)) =
        unitC_nemb (unitC_mono (d - u) (d - v)) := by
      rw [unitC_emb_mono, unitC_nemb_mono]
      ext <;> simp <;> omega
    rw [he, unitC_I_coeff]
  · apply unitC_I_coeff_of_pos
    rw [unitC_emb_mono]
    simp
    omega

/-! ## The hook+column part `G` and `H = (x - y) G` -/

/-- `G = ∑_(α ≥ 2) c_(α, 2^β, 1^γ) (-1)^γ (x y)^β h_γ(x, y)`. -/
def unitC_G (c : List ℕ →₀ ℚ) : XY :=
  ∑ μ ∈ c.support, if unitC_IsHook μ then
    C (c μ * (-1) ^ unitC_gamma μ) * ((x * y) ^ unitC_beta μ * twoComplete (unitC_gamma μ))
  else 0

/-- `H = (x - y) G`. -/
def unitC_H (c : List ℕ →₀ ℚ) : XY := (x - y) * unitC_G c

/-- `(x - y)(x y)^β h_γ(x, y) = x^(β+γ+1) y^β - x^β y^(β+γ+1)`. -/
lemma unitC_two_geom (β γ : ℕ) :
    (x - y) * ((x * y) ^ β * twoComplete γ) =
      x ^ (β + γ + 1) * y ^ β - x ^ β * y ^ (β + γ + 1) := by
  have h : twoComplete γ * (x - y) = x ^ (γ + 1) - y ^ (γ + 1) := by
    have := geom_sum₂_mul x y (γ + 1)
    simpa [twoComplete] using this
  calc (x - y) * ((x * y) ^ β * twoComplete γ) = (x * y) ^ β * (twoComplete γ * (x - y)) := by
        ring
    _ = _ := by rw [h]; ring

lemma unitC_coeff_H (c : List ℕ →₀ ℚ) (u v : ℕ) :
    (unitC_H c).coeff (unitC_mono u v) = ∑ μ ∈ c.support, if unitC_IsHook μ then
      c μ * (-1) ^ unitC_gamma μ *
        ((if unitC_beta μ + unitC_gamma μ + 1 = u ∧ unitC_beta μ = v then 1 else 0) -
          (if unitC_beta μ = u ∧ unitC_beta μ + unitC_gamma μ + 1 = v then 1 else 0))
    else 0 := by
  rw [unitC_H, unitC_G, Finset.mul_sum, coeff_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  by_cases hk : unitC_IsHook μ
  · simp only [hk, ite_true]
    rw [mul_left_comm, coeff_C_mul, unitC_two_geom, coeff_sub, unitC_coeff_xy, unitC_coeff_xy]
  · simp [hk]

/-- Upper monomials `x^(β+γ+1) y^β` of `H` read off `b(β, γ)`. -/
lemma unitC_coeff_H_upper {N : ℕ} {c : List ℕ →₀ ℚ} (hc : ∀ μ ∈ c.support, IsPartitionOf N μ)
    (hcol : c (List.replicate N 1) = 0) (β γ : ℕ) :
    (unitC_H c).coeff (unitC_mono (β + γ + 1) β) = (-1) ^ γ * hookCoeff N c β γ := by
  rw [unitC_coeff_H, ← unitC_hook_sum hc hcol, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  by_cases hk : unitC_IsHook μ
  · have e1 : (unitC_beta μ + unitC_gamma μ + 1 = β + γ + 1 ∧ unitC_beta μ = β) ↔
        (unitC_beta μ = β ∧ unitC_gamma μ = γ) := by
      constructor <;> intro h <;> omega
    have e2 : ¬(unitC_beta μ = β + γ + 1 ∧ unitC_beta μ + unitC_gamma μ + 1 = β) := by omega
    simp only [hk, true_and, ite_true, if_congr e1 rfl rfl, e2, ite_false]
    split_ifs with h
    · rw [h.2]; ring
    · ring
  · simp [hk]

/-- Lower monomials `x^β y^(β+γ+1)` of `H` read off `-b(β, γ)`. -/
lemma unitC_coeff_H_lower {N : ℕ} {c : List ℕ →₀ ℚ} (hc : ∀ μ ∈ c.support, IsPartitionOf N μ)
    (hcol : c (List.replicate N 1) = 0) (β γ : ℕ) :
    (unitC_H c).coeff (unitC_mono β (β + γ + 1)) = -((-1) ^ γ * hookCoeff N c β γ) := by
  rw [unitC_coeff_H, ← unitC_hook_sum hc hcol, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  by_cases hk : unitC_IsHook μ
  · have e1 : (unitC_beta μ = β ∧ unitC_beta μ + unitC_gamma μ + 1 = β + γ + 1) ↔
        (unitC_beta μ = β ∧ unitC_gamma μ = γ) := by
      constructor <;> intro h <;> omega
    have e2 : ¬(unitC_beta μ + unitC_gamma μ + 1 = β ∧ unitC_beta μ = β + γ + 1) := by omega
    simp only [hk, true_and, ite_true, if_congr e1 rfl rfl, e2, ite_false]
    split_ifs with h
    · rw [h.2]; ring
    · ring
  · simp [hk]

/-! ## Specializing the Schur expansion -/

lemma unitC_atA_C (q : ℚ) : atA (C q) = C q := by
  simp [atA, MvPolynomial.algebraMap_eq]

lemma unitC_atXOne_C (q : ℚ) : atXOne (C q) = C q := by
  simp [atXOne, MvPolynomial.algebraMap_eq]

/-- `F[1 - x - y] = Q G + c_(1^N) s_(1^N)[1 - x - y]` for a Schur expansion of `F` in
degree `N`: shapes with second part `≥ 3` vanish, and the others are hooks or the column. -/
lemma unitC_atA_expansion (hS : SchurAtA) {N : ℕ} {c : List ℕ →₀ ℚ}
    (hc : ∀ μ ∈ c.support, IsPartitionOf N μ) :
    atA (c.sum fun μ q => C q * schur μ) =
      Q * unitC_G c + C (c (List.replicate N 1)) * atA (schur (List.replicate N 1)) := by
  have hterm : ∀ μ ∈ c.support, atA (C (c μ) * schur μ) =
      Q * (if unitC_IsHook μ then
        C (c μ * (-1) ^ unitC_gamma μ) * ((x * y) ^ unitC_beta μ * twoComplete (unitC_gamma μ))
        else 0) +
      (if μ = List.replicate N 1 then C (c μ) * atA (schur (List.replicate N 1)) else 0) := by
    intro μ hμ
    rw [map_mul, unitC_atA_C]
    by_cases hk : unitC_IsHook μ
    · have hne : μ ≠ List.replicate N 1 := by
        rintro rfl
        have := hk.1
        cases N <;> simp_all [List.replicate_succ]
      simp only [hk, hne, ite_true, ite_false, add_zero]
      rw [congrArg schur hk.2, unitC_shape, hS.1 _ _ _ hk.1]
      simp only [map_mul, map_pow, map_neg, map_one]
      ring
    · by_cases hcl : μ = List.replicate N 1
      · subst hcl
        simp only [hk, ite_true, ite_false, mul_zero, zero_add]
      · simp only [hk, hcl, ite_false, mul_zero, add_zero]
        have h3 : 3 ≤ μ.getD 1 0 := by
          by_contra h
          rcases unitC_classify (hc μ hμ) (by omega) with h' | h'
          · exact hk h'
          · exact hcl h'
        rw [hS.2.1 N μ (hc μ hμ) h3, mul_zero]
  rw [Finsupp.sum, map_sum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq', ← unitC_G]
  split_ifs with hm
  · rfl
  · rw [Finsupp.notMem_support_iff.mp hm, C_0, zero_mul]

/-! ## The reciprocity argument -/

lemma unitC_Q_ne_zero : Q ≠ 0 := by
  intro h
  have := congrArg (eval fun _ => (2 : ℚ)) h
  simp [Q, x, y] at this
  norm_num at this

theorem fullEndpoint_of (hA : AtAComplete) (hP : AtAPlethysm) (hS : SchurAtA) :
    FullEndpoint := by
  intro d a g c hd ha hg hexp
  obtain ⟨hc, hF⟩ := hexp
  have hdec := unitC_atA_expansion hS hc
  rw [← hF, hP, hA.2.2 a ha] at hdec
  change unitC_P g = _ at hdec
  -- The column coefficient vanishes: evaluate at `x = 1`.
  have hcol : c (List.replicate (a * d) 1) = 0 := by
    have h1 := congrArg atXOne hdec
    rw [unitC_P_atXOne g d hd hg, map_add, map_mul, map_mul, unitC_atXOne_Q, zero_mul, zero_add,
      hS.2.2, unitC_atXOne_C] at h1
    have hy : (-y : XY) ^ (a * d) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr (X_ne_zero _))
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact C_eq_zero.mp h
    · exact absurd h hy
  rw [hcol, C_0, zero_mul, add_zero] at hdec
  -- Cancel `Q` in the Laurent ring: `x^(d-1) y^(d-1) G(1/x, 1/y) = G`, so `H` is antireciprocal.
  have hQne : unitC_I Q ≠ 0 := by
    intro h
    have h' := unitC_Q_recip
    rw [h, zero_mul] at h'
    exact unitC_Q_ne_zero ((map_eq_zero_iff unitC_E
      (AddMonoidAlgebra.mapDomain_injective unitC_emb_injective)).mp h'.symm)
  have hGrec : unitC_T * unitC_E (unitC_G c) = unitC_I (unitC_G c) * unitC_T ^ d := by
    have h := unitC_P_recip g d hg
    rw [hdec, map_mul, map_mul, ← unitC_Q_recip] at h
    apply mul_left_cancel₀ hQne
    linear_combination h
  have hHrec : unitC_E (unitC_H c) = -(unitC_I (unitC_H c) * unitC_T ^ d) := by
    simp only [unitC_H, map_mul]
    rw [unitC_xy_recip]
    linear_combination (-unitC_I (x - y)) * hGrec
  have hcoef := unitC_coeff_recip hHrec
  have hup := unitC_coeff_H_upper hc hcol
  have hlow := unitC_coeff_H_lower hc hcol
  have hs : ∀ γ : ℕ, ((-1 : ℚ) ^ γ) ≠ 0 := fun γ => pow_ne_zero _ (by norm_num)
  -- Item 2: vanishing outside `β + γ < d`.
  have item2 : ∀ (β : ℤ) (γ : ℕ), (d : ℤ) ≤ β + (γ : ℤ) → hookCoeff (a * d) c β γ = 0 := by
    intro β γ h
    rcases lt_or_ge β 0 with hb | hb
    · exact unitC_hookCoeff_neg c hb γ
    lift β to ℕ using hb
    have h' := hcoef (β + γ + 1) β
    have hout : ¬(β + γ + 1 ≤ d ∧ β ≤ d) := by omega
    simp only [hout, ite_false, neg_zero, hup] at h'
    exact (mul_eq_zero.mp h').resolve_left (hs γ)
  refine ⟨?_, item2, hcol⟩
  -- Item 1: the reflection `β ↦ d - 1 - γ - β`.
  intro β γ
  rcases lt_or_ge β 0 with hb | hb
  · rw [unitC_hookCoeff_neg c hb, item2 _ _ (by omega)]
  rcases lt_or_ge ((d : ℤ) - 1 - γ - β) 0 with hb' | hb'
  · rw [unitC_hookCoeff_neg c hb', item2 _ _ (by omega)]
  lift β to ℕ using hb
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = (d : ℤ) - 1 - γ - β := ⟨((d : ℤ) - 1 - γ - β).toNat, by omega⟩
  rw [← hn]
  have h' := hcoef (β + γ + 1) β
  have e1 : d - (β + γ + 1) = n := by omega
  have e2 : d - β = n + γ + 1 := by omega
  have hin : β + γ + 1 ≤ d ∧ β ≤ d := by omega
  simp only [hin, and_self, ite_true, e1, e2, hup, hlow] at h'
  exact mul_left_cancel₀ (hs γ) (by linear_combination h')

#print axioms fullEndpoint_of

end GR22
