import GR22.Endpoint

/-!
# Unit D: Schur expansions exist

(unit D). Every weighted-homogeneous `f` of degree `N` is a
`ℚ`-combination of Jacobi–Trudi Schur functions `s_μ`, `μ ⊢ N`.

1. Newton's identity puts every `p_n`, hence every monomial of weighted degree `N`, in the span
   of the products `h_ν = ∏ h_(ν_i)` with `∑ ν_i = N`.
2. Expanding `det (h_(λ_i - i + j))` over permutations, the identity gives `h_λ` and every other
   permutation gives `0` or `± h_ν` with `∑ ν_i = N` and `∑ ν_i² > ∑ λ_i²` (rearrangement
   inequality), so strong induction on `N² - ∑ ν_i²` puts every `h_ν` in the span of the `s_μ`.
-/

noncomputable section
namespace GR22

open MvPolynomial

/-- `h_ν = ∏ h_(ν_i)` for a multiset `ν`. -/
def unitD_hM (m : Multiset ℕ) : SF := (m.map complete).prod

/-- The span of the `h_ν` with `∑ ν_i = N`. -/
def unitD_V (N : ℕ) : Submodule ℚ SF :=
  Submodule.span ℚ {f | ∃ m : Multiset ℕ, m.sum = N ∧ f = unitD_hM m}

lemma unitD_hM_mem (m : Multiset ℕ) : unitD_hM m ∈ unitD_V m.sum :=
  Submodule.subset_span ⟨m, rfl, rfl⟩

lemma unitD_mul_mem {A B : ℕ} {a b : SF} (ha : a ∈ unitD_V A) (hb : b ∈ unitD_V B) :
    a * b ∈ unitD_V (A + B) := by
  have h := Submodule.mul_mem_mul ha hb
  rw [unitD_V, unitD_V, Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨m, rfl, rfl⟩, _, ⟨m', rfl, rfl⟩, rfl⟩
  exact ⟨m + m', Multiset.sum_add _ _, by simp [unitD_hM, Multiset.map_add, Multiset.prod_add]⟩

lemma unitD_one_mem : (1 : SF) ∈ unitD_V 0 := by
  simpa [unitD_hM] using unitD_hM_mem 0

lemma unitD_complete_mem (n : ℕ) : complete n ∈ unitD_V n := by
  simpa [unitD_hM] using unitD_hM_mem {n}

lemma unitD_newton (n : ℕ) :
    C ((n + 1 : ℚ)) * complete (n + 1) =
      ∑ k : Fin (n + 1), power (k.val + 1) * complete (n - k.val) := by
  rw [complete, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (by positivity), C_1, one_mul]

lemma unitD_power_mem (n : ℕ) : power (n + 1) ∈ unitD_V (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h := unitD_newton n
    have h0 : complete 0 = 1 := by rw [complete]
    rw [Fin.sum_univ_castSucc] at h
    simp only [Fin.val_last, Nat.sub_self, h0, mul_one, Fin.val_castSucc] at h
    have : power (n + 1) = C ((n + 1 : ℚ)) * complete (n + 1) -
        ∑ i : Fin n, power (i.val + 1) * complete (n - i.val) := by
      rw [h]; ring
    rw [this, C_mul']
    refine Submodule.sub_mem _ (Submodule.smul_mem _ _ (unitD_complete_mem _))
      (Submodule.sum_mem _ fun i _ => ?_)
    have := unitD_mul_mem (ih i.val i.isLt) (unitD_complete_mem (n - i.val))
    rwa [show i.val + 1 + (n - i.val) = n + 1 by omega] at this

lemma unitD_X_pow_mem (i b : ℕ) : (X i : SF) ^ b ∈ unitD_V (b * (i + 1)) := by
  induction b with
  | zero => simpa using unitD_one_mem
  | succ b ih =>
    have hX : (X i : SF) ∈ unitD_V (i + 1) := by
      simpa [power] using unitD_power_mem i
    rw [pow_succ, show (b + 1) * (i + 1) = b * (i + 1) + (i + 1) by ring]
    exact unitD_mul_mem ih hX

lemma unitD_monomial_mem (s : ℕ →₀ ℕ) :
    monomial s (1 : ℚ) ∈ unitD_V (Finsupp.weight (fun i : ℕ => i + 1) s) := by
  induction s using Finsupp.induction with
  | zero => simpa using unitD_one_mem
  | single_add a b f _ _ ih =>
    rw [← mul_one (1 : ℚ), ← monomial_mul_monomial, map_add, Finsupp.weight_single, smul_eq_mul,
      ← X_pow_eq_monomial]
    exact unitD_mul_mem (unitD_X_pow_mem a b) ih

lemma unitD_homogeneous_mem {N : ℕ} {f : SF}
    (hf : IsWeightedHomogeneous (fun i : ℕ => i + 1) f N) : f ∈ unitD_V N := by
  rw [f.as_sum]
  refine Submodule.sum_mem _ fun s hs => ?_
  have hw := hf (mem_support_iff.mp hs)
  rw [← hw, ← mul_one (f.coeff s), ← smul_eq_mul, ← smul_monomial]
  exact Submodule.smul_mem _ _ (unitD_monomial_mem s)

/-! ### Triangularity of Jacobi–Trudi against the `h_ν` -/

lemma unitD_complete_zero : complete 0 = 1 := by rw [complete]

/-- `∑ ν_i²`. -/
def unitD_sq (m : Multiset ℕ) : ℕ := (m.map (· ^ 2)).sum

/-- The span of the `s_μ` with `μ ⊢ N`. -/
def unitD_S (N : ℕ) : Submodule ℚ SF :=
  Submodule.span ℚ (schur '' {μ | IsPartitionOf N μ})

lemma unitD_sq_le (m : Multiset ℕ) : unitD_sq m ≤ m.sum ^ 2 := by
  induction m using Multiset.induction_on with
  | empty => simp [unitD_sq]
  | cons a m ih =>
    simp only [unitD_sq, Multiset.map_cons, Multiset.sum_cons] at ih ⊢
    nlinarith [Nat.zero_le (a * m.sum)]

lemma unitD_univ_get (l : List ℕ) :
    (Finset.univ : Finset (Fin l.length)).val.map (fun i => l.get i) = (l : Multiset ℕ) := by
  rw [Fin.univ_val_map, List.ofFn_get]

/-- The entry `λ_i - i + σ(i)` picked by `σ` in the Jacobi–Trudi matrix. -/
def unitD_e (μ : List ℕ) (σ : Equiv.Perm (Fin μ.length)) (i : Fin μ.length) : ℤ :=
  (μ.get i : ℤ) - (i.val : ℤ) + ((σ i).val : ℤ)

lemma unitD_schur_eq (μ : List ℕ) :
    schur μ = ∑ σ : Equiv.Perm (Fin μ.length),
      Equiv.Perm.sign σ • ∏ i, completeZ (unitD_e μ σ i) := by
  let M : Matrix (Fin μ.length) (Fin μ.length) SF := Matrix.of fun i j =>
    completeZ ((μ.get i : ℤ) - (i.val : ℤ) + (j.val : ℤ))
  have : schur μ = M.det := rfl
  rw [this, ← Matrix.det_transpose, Matrix.det_apply]
  rfl

lemma unitD_e_one (μ : List ℕ) (i : Fin μ.length) : unitD_e μ 1 i = μ.get i := by
  simp [unitD_e]

lemma unitD_e_sum (μ : List ℕ) (σ : Equiv.Perm (Fin μ.length)) :
    ∑ i, unitD_e μ σ i = (μ.sum : ℤ) := by
  have h1 : ∑ i : Fin μ.length, ((σ i).val : ℤ) = ∑ i : Fin μ.length, (i.val : ℤ) :=
    Equiv.sum_comp σ (fun i => (i.val : ℤ))
  have h2 : ∑ i : Fin μ.length, (μ.get i : ℤ) = (μ.sum : ℤ) := by
    rw [← Nat.cast_sum, ← Finset.sum_map_val, unitD_univ_get, Multiset.sum_coe]
  simp only [unitD_e, Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2]
  ring

lemma unitD_e_sq_lt (μ : List ℕ) (hμ : μ.Pairwise (fun a b => b ≤ a))
    (σ : Equiv.Perm (Fin μ.length)) (hσ : σ ≠ 1) :
    ∑ i, ((μ.get i : ℤ)) ^ 2 < ∑ i, (unitD_e μ σ i) ^ 2 := by
  have hpt : ∀ i, (unitD_e μ σ i) ^ 2 = (μ.get i : ℤ) ^ 2 +
      2 * ((μ.get i : ℤ) * ((σ i).val : ℤ) - (μ.get i : ℤ) * (i.val : ℤ)) +
      (((σ i).val : ℤ) - (i.val : ℤ)) ^ 2 := fun i => by simp only [unitD_e]; ring
  rw [Finset.sum_congr rfl (fun i _ => hpt i)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  have hanti : Antivary (fun i : Fin μ.length => (μ.get i : ℤ)) (fun i => (i.val : ℤ)) := by
    intro i j hij
    have hij' : i < j := Fin.lt_def.mpr (by simp only at hij; exact_mod_cast hij)
    have := List.pairwise_iff_get.mp hμ i j hij'
    show (μ.get j : ℤ) ≤ μ.get i
    exact_mod_cast this
  have hre := hanti.sum_mul_le_sum_mul_comp_perm (σ := σ)
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
    by_contra h
    push Not at h
    exact hσ (Equiv.ext h)
  have hpos : 0 < ∑ i : Fin μ.length, (((σ i).val : ℤ) - (i.val : ℤ)) ^ 2 := by
    refine Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩
    have : ((σ i).val : ℤ) - (i.val : ℤ) ≠ 0 := by
      intro h
      exact hi (Fin.ext (by omega))
    positivity
  linarith

lemma unitD_sq_coe (l : List ℕ) :
    (unitD_sq (l : Multiset ℕ) : ℤ) = ∑ i : Fin l.length, ((l.get i : ℕ) : ℤ) ^ 2 := by
  rw [← unitD_univ_get, unitD_sq, Multiset.map_map, Finset.sum_map_val]
  push_cast
  rfl

/-- A non-identity permutation contributes `0` or a `h_ν` with a larger `∑ ν_i²`. -/
lemma unitD_term_mem {N : ℕ} {μ : List ℕ} (hμ : IsPartitionOf N μ)
    (ih : ∀ m : Multiset ℕ, m.sum = N → unitD_sq μ < unitD_sq m → unitD_hM m ∈ unitD_S N)
    (σ : Equiv.Perm (Fin μ.length)) (hσ : σ ≠ 1) :
    ∏ i, completeZ (unitD_e μ σ i) ∈ unitD_S N := by
  by_cases hneg : ∃ i, unitD_e μ σ i < 0
  · obtain ⟨i, hi⟩ := hneg
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [completeZ, not_le.mpr hi])]
    exact zero_mem _
  push Not at hneg
  set ν : Multiset ℕ := Finset.univ.val.map (fun i => (unitD_e μ σ i).toNat) with hν
  have hT : ∏ i, completeZ (unitD_e μ σ i) = unitD_hM ν := by
    rw [unitD_hM, hν, Multiset.map_map, Finset.prod_map_val]
    exact Finset.prod_congr rfl fun i _ => by simp [completeZ, hneg i]
  have hsum : ν.sum = N := by
    have : (ν.sum : ℤ) = N := by
      rw [hν, Finset.sum_map_val, Nat.cast_sum]
      simp only [Int.toNat_of_nonneg (hneg _)]
      rw [unitD_e_sum, hμ.2.2]
    exact_mod_cast this
  have hsq : unitD_sq μ < unitD_sq ν := by
    have h1 : (unitD_sq ν : ℤ) = ∑ i, (unitD_e μ σ i) ^ 2 := by
      rw [hν, unitD_sq, Multiset.map_map, Finset.sum_map_val, Nat.cast_sum]
      simp only [Function.comp_apply, Nat.cast_pow, Int.toNat_of_nonneg (hneg _)]
    have h2 := unitD_e_sq_lt μ hμ.1 σ hσ
    rw [← h1, ← unitD_sq_coe] at h2
    exact_mod_cast h2
  rw [hT]
  exact ih ν hsum hsq

lemma unitD_hM_mem_S (N : ℕ) (m : Multiset ℕ) (hm : m.sum = N) : unitD_hM m ∈ unitD_S N := by
  suffices h : ∀ k, ∀ m : Multiset ℕ, m.sum = N → N ^ 2 - unitD_sq m = k →
      unitD_hM m ∈ unitD_S N from h _ m hm rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro m hm hk
  set l : List ℕ := (m.filter (· ≠ 0)).sort (· ≥ ·) with hl
  have hlm : (l : Multiset ℕ) = m.filter (· ≠ 0) := Multiset.sort_eq _ _
  have hzero : ∀ x ∈ m.filter (fun x => ¬ x ≠ 0), x = 0 := fun x hx => by
    simpa using (Multiset.mem_filter.mp hx).2
  have hsplit := Multiset.filter_add_not (fun x => x ≠ 0) m
  have hhM : unitD_hM m = unitD_hM l := by
    have h1 : unitD_hM (m.filter (fun x => ¬ x ≠ 0)) = 1 :=
      Multiset.prod_eq_one fun x hx => by
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
        rw [hzero y hy, unitD_complete_zero]
    conv_lhs => rw [← hsplit]
    rw [hlm, unitD_hM, Multiset.map_add, Multiset.prod_add, ← unitD_hM, ← unitD_hM, h1, mul_one]
  have hsq : unitD_sq m = unitD_sq l := by
    have h1 : unitD_sq (m.filter (fun x => ¬ x ≠ 0)) = 0 :=
      Multiset.sum_eq_zero fun x hx => by
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
        rw [hzero y hy]; rfl
    conv_lhs => rw [← hsplit]
    rw [hlm, unitD_sq, Multiset.map_add, Multiset.sum_add, ← unitD_sq, ← unitD_sq, h1, add_zero]
  have hpart : IsPartitionOf N l := by
    refine ⟨Multiset.pairwise_sort _ _, fun n hn => ?_, ?_⟩
    · rw [hl, Multiset.mem_sort, Multiset.mem_filter] at hn
      exact Nat.pos_of_ne_zero hn.2
    · have h1 : (m.filter (fun x => ¬ x ≠ 0)).sum = 0 :=
        Multiset.sum_eq_zero fun x hx => hzero x hx
      have h2 := congrArg Multiset.sum hsplit
      rw [Multiset.sum_add, h1, add_zero, hm] at h2
      rw [← Multiset.sum_coe, hlm, h2]
  have hschur := unitD_schur_eq l
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 1)] at hschur
  have h1 : Equiv.Perm.sign (1 : Equiv.Perm (Fin l.length)) •
      ∏ i, completeZ (unitD_e l 1 i) = unitD_hM l := by
    simp only [Equiv.Perm.sign_one, one_smul, unitD_e_one, completeZ, Nat.cast_nonneg,
      ite_true, Int.toNat_natCast]
    rw [unitD_hM, ← unitD_univ_get, Multiset.map_map, Finset.prod_map_val]
    rfl
  rw [h1] at hschur
  rw [hhM, eq_sub_of_add_eq hschur.symm]
  refine Submodule.sub_mem _ (Submodule.subset_span ⟨l, hpart, rfl⟩)
    (Submodule.sum_mem _ fun σ hσ => ?_)
  rw [Units.smul_def]
  refine Submodule.smul_of_tower_mem _ _ (unitD_term_mem hpart (fun m' hm' hlt => ?_) σ
    (Finset.ne_of_mem_erase hσ))
  have hle := unitD_sq_le m'
  rw [hm'] at hle
  exact ih _ (by omega) m' hm' rfl

lemma unitD_V_le_S (N : ℕ) : unitD_V N ≤ unitD_S N :=
  Submodule.span_le.mpr fun _ ⟨m, hm, h⟩ => h ▸ unitD_hM_mem_S N m hm

/-- Unit D deliverable: every weighted-homogeneous element of degree `N` has a Schur
expansion over the partitions of `N`. -/
theorem expansionsExist : ExpansionsExist := by
  intro N f hf
  have hS : f ∈ unitD_S N := unitD_V_le_S N (unitD_homogeneous_mem hf)
  rw [unitD_S, Finsupp.mem_span_image_iff_linearCombination] at hS
  obtain ⟨c, hc, rfl⟩ := hS
  refine ⟨c, fun μ hμ => (Finsupp.mem_supported _ _).mp hc hμ, ?_⟩
  rw [Finsupp.linearCombination_apply]
  simp only [C_mul']

/-! ### Uniqueness, by counting dimensions

The power-sum monomials `p_μ`, `μ ⊢ N`, are distinct monomials, so linearly independent, and
lie in the span of the `s_μ`; hence that span has dimension `#{μ ⊢ N}` and the `s_μ` are
linearly independent. -/

/-- The partitions of `N`, as weakly decreasing lists. -/
def unitD_T (N : ℕ) : Finset (List ℕ) :=
  (Finset.univ : Finset (Nat.Partition N)).image fun p => p.parts.sort (· ≥ ·)

lemma unitD_mem_T {N : ℕ} {μ : List ℕ} : μ ∈ unitD_T N ↔ IsPartitionOf N μ := by
  constructor
  · rw [unitD_T, Finset.mem_image]
    rintro ⟨p, _, rfl⟩
    refine ⟨Multiset.pairwise_sort _ _, fun n hn => p.parts_pos ((Multiset.mem_sort _).mp hn),
      ?_⟩
    rw [← Multiset.sum_coe, Multiset.sort_eq, p.parts_sum]
  · rintro ⟨h1, h2, h3⟩
    rw [unitD_T, Finset.mem_image]
    refine ⟨⟨μ, fun hi => h2 _ hi, by rw [Multiset.sum_coe, h3]⟩, Finset.mem_univ _, ?_⟩
    exact List.mergeSort_eq_self _ h1

/-- The exponent vector of `p_μ = ∏ p_(μ_k)`. -/
def unitD_ex (μ : List ℕ) : ℕ →₀ ℕ := (μ.map fun k => Finsupp.single (k - 1) 1).sum

lemma unitD_ex_apply (μ : List ℕ) (hμ : ∀ n ∈ μ, 0 < n) (j : ℕ) :
    unitD_ex μ j = μ.count (j + 1) := by
  induction μ with
  | nil => simp [unitD_ex]
  | cons a μ ih =>
    have ha := hμ a List.mem_cons_self
    have ih' := ih fun n hn => hμ n (List.mem_cons_of_mem _ hn)
    simp only [unitD_ex, List.map_cons, List.sum_cons, Finsupp.add_apply,
      Finsupp.single_apply, List.count_cons] at ih' ⊢
    rw [ih']
    by_cases h : a = j + 1
    · simp [h, add_comm]
    · have : a - 1 ≠ j := by omega
      simp [h, this]

lemma unitD_ex_weight (μ : List ℕ) (hμ : ∀ n ∈ μ, 0 < n) :
    Finsupp.weight (fun i : ℕ => i + 1) (unitD_ex μ) = μ.sum := by
  induction μ with
  | nil => simp [unitD_ex]
  | cons a μ ih =>
    have ha := hμ a List.mem_cons_self
    have ih' := ih fun n hn => hμ n (List.mem_cons_of_mem _ hn)
    simp only [unitD_ex, List.map_cons, List.sum_cons, map_add, Finsupp.weight_single,
      smul_eq_mul, one_mul] at ih' ⊢
    rw [ih']
    omega

lemma unitD_ex_inj {N : ℕ} {μ ν : List ℕ} (hμ : IsPartitionOf N μ) (hν : IsPartitionOf N ν)
    (h : unitD_ex μ = unitD_ex ν) : μ = ν := by
  have hc : ∀ a, μ.count a = ν.count a := by
    intro a
    rcases a with _ | j
    · rw [List.count_eq_zero.mpr fun h0 => (hμ.2.1 0 h0).false,
        List.count_eq_zero.mpr fun h0 => (hν.2.1 0 h0).false]
    · rw [← unitD_ex_apply μ hμ.2.1, ← unitD_ex_apply ν hν.2.1, h]
  exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => le_antisymm hba hab) hμ.1 hν.1
    (List.perm_iff_count.mpr hc)

lemma unitD_schur_linearIndependent (N : ℕ) :
    LinearIndependent ℚ (fun μ : unitD_T N => schur μ.1) := by
  set b : unitD_T N → SF := fun μ => schur μ.1
  set p : unitD_T N → SF := fun μ => monomial (unitD_ex μ.1) 1
  have hp : LinearIndependent ℚ p := by
    have := (basisMonomials ℕ ℚ).linearIndependent.comp (fun μ : unitD_T N => unitD_ex μ.1)
      fun μ ν h => Subtype.ext (unitD_ex_inj (unitD_mem_T.mp μ.2) (unitD_mem_T.mp ν.2) h)
    rw [coe_basisMonomials] at this
    exact this
  have hrange : Submodule.span ℚ (Set.range b) = unitD_S N := by
    rw [unitD_S]
    congr 1
    ext f
    constructor
    · rintro ⟨μ, rfl⟩
      exact ⟨μ.1, unitD_mem_T.mp μ.2, rfl⟩
    · rintro ⟨μ, hμ, rfl⟩
      exact ⟨⟨μ, unitD_mem_T.mpr hμ⟩, rfl⟩
  have hle : Submodule.span ℚ (Set.range p) ≤ Submodule.span ℚ (Set.range b) := by
    rw [hrange, Submodule.span_le]
    rintro _ ⟨μ, rfl⟩
    have hμ := unitD_mem_T.mp μ.2
    have := unitD_monomial_mem (unitD_ex μ.1)
    rw [unitD_ex_weight _ hμ.2.1, hμ.2.2] at this
    exact unitD_V_le_S N this
  have : Module.Finite ℚ (Submodule.span ℚ (Set.range b)) :=
    Module.Finite.span_of_finite ℚ (Set.finite_range b)
  rw [linearIndependent_iff_card_eq_finrank_span]
  refine le_antisymm ?_ (finrank_range_le_card b)
  rw [← finrank_span_eq_card hp]
  exact Submodule.finrank_mono hle

/-- Unit D stretch deliverable: Schur expansions are unique. -/
theorem schurExpansion_unique {N : ℕ} {f : SF} {c c' : List ℕ →₀ ℚ} :
    SchurExpansion N f c → SchurExpansion N f c' → c = c' := by
  rintro ⟨hc, hf⟩ ⟨hc', hf'⟩
  classical
  set d := c - c'
  have hd : d.support ⊆ unitD_T N := fun μ hμ => by
    rcases Finset.mem_union.mp (Finsupp.support_sub hμ) with h | h
    · exact unitD_mem_T.mpr (hc μ h)
    · exact unitD_mem_T.mpr (hc' μ h)
  have hsum : d.sum (fun μ q => C q * schur μ) = 0 := by
    rw [Finsupp.sum_sub_index (fun _ _ _ => by rw [C_sub, sub_mul]), ← hf, ← hf', sub_self]
  rw [Finsupp.sum_of_support_subset d hd _ (fun _ _ => by rw [C_0, zero_mul]),
    ← Finset.sum_coe_sort] at hsum
  simp only [C_mul'] at hsum
  have h0 := Fintype.linearIndependent_iff.mp (unitD_schur_linearIndependent N)
    (fun μ => d μ.1) hsum
  ext μ
  rw [← sub_eq_zero, ← Finsupp.sub_apply]
  by_cases hμ : μ ∈ unitD_T N
  · exact h0 ⟨μ, hμ⟩
  · exact Finsupp.notMem_support_iff.mp fun h => hμ (hd h)

end GR22

#print axioms GR22.expansionsExist
#print axioms GR22.schurExpansion_unique
