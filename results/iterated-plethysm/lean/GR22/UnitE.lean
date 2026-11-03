import GR22.Endpoint

/-!
# Unit E: `FullEndpoint → Question1`, and Schur expansions of iterated plethysms

(unit E). Plethysm identity laws and associativity, weighted degrees
of `complete`, plethysms and iterated plethysms, the reduction deleting `h₁` factors, and the
palindrome bookkeeping that turns the reflection identity of `FullEndpoint` into the source's
`NonzeroPalindrome`.
-/

noncomputable section
namespace GR22

open MvPolynomial

/-! ### Plethysm identities -/

lemma unitE_plethysm_eq_aeval (f g : SF) :
    plethysm f g = aeval (fun i => adams (i + 1) g) f := by
  rw [plethysm, aeval_def, algebraMap_eq]

lemma unitE_plethysm_X (i : ℕ) (g : SF) : plethysm (X i) g = adams (i + 1) g := by
  simp [plethysm]

lemma unitE_adams_eq (k : ℕ) (f : SF) : adams k f = rename (fun i => k * (i + 1) - 1) f := rfl

lemma unitE_adams_one (f : SF) : adams 1 f = f := by
  have h : (fun i : ℕ => 1 * (i + 1) - 1) = id := by funext i; simp
  rw [unitE_adams_eq, h, rename_id_apply]

lemma unitE_adams_adams {k m : ℕ} (hm : 1 ≤ m) (f : SF) :
    adams k (adams m f) = adams (k * m) f := by
  have h : (fun i : ℕ => k * (i + 1) - 1) ∘ (fun i : ℕ => m * (i + 1) - 1) =
      fun i => k * m * (i + 1) - 1 := by
    funext i
    have h1 : 1 ≤ m * (i + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    simp only [Function.comp_apply, Nat.sub_add_cancel h1, mul_assoc]
  rw [unitE_adams_eq, unitE_adams_eq, unitE_adams_eq, rename_rename, h]

lemma unitE_complete_one : complete 1 = power 1 := by
  simp [complete]

lemma unitE_power_one : power 1 = X 0 := by simp [power]

lemma unitE_plethysm_power_one_right (f : SF) : plethysm f (power 1) = f := by
  rw [unitE_plethysm_eq_aeval]
  have h : (fun i : ℕ => adams (i + 1) (power 1)) = X := by
    funext i; simp [unitE_power_one, unitE_adams_eq, rename_X]
  rw [h, aeval_X_left_apply]

lemma unitE_plethysm_power_one_left (g : SF) : plethysm (power 1) g = g := by
  rw [unitE_power_one, unitE_plethysm_X, unitE_adams_one]

/-- `p_k[g]` commutes with plethysm: `(p_k[g])[h] = p_k[g[h]]` for `k ≥ 1`. -/
lemma unitE_plethysm_adams {k : ℕ} (hk : 1 ≤ k) (g h : SF) :
    plethysm (adams k g) h = adams k (plethysm g h) := by
  have key : (aeval (fun i => adams (i + 1) h)).comp (rename (fun i : ℕ => k * (i + 1) - 1)) =
      (rename (R := ℚ) (fun i : ℕ => k * (i + 1) - 1)).comp (aeval (fun i => adams (i + 1) h)) := by
    apply MvPolynomial.algHom_ext
    intro i
    have h1 : k * (i + 1) - 1 + 1 = k * (i + 1) := Nat.sub_add_cancel (by nlinarith)
    simp only [AlgHom.comp_apply, rename_X, aeval_X, h1]
    rw [← unitE_adams_eq, unitE_adams_adams (by omega)]
  have := congrArg (fun φ => φ g) key
  simpa only [AlgHom.comp_apply, ← unitE_adams_eq, ← unitE_plethysm_eq_aeval] using this

lemma unitE_plethysm_assoc (f g h : SF) :
    plethysm (plethysm f g) h = plethysm f (plethysm g h) := by
  simp only [unitE_plethysm_eq_aeval]
  rw [← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext i
  rw [← unitE_plethysm_eq_aeval, ← unitE_plethysm_eq_aeval,
    unitE_plethysm_adams (by omega)]

/-! ### Degrees -/

/-- The weights of the generators: variable `i` is `p_(i+1)`. -/
abbrev unitE_w : ℕ → ℕ := fun i => i + 1

lemma unitE_aeval_isWH {f : SF} {m : ℕ} (c : ℕ) (φ : ℕ → SF)
    (hf : IsWeightedHomogeneous unitE_w f m)
    (hφ : ∀ i, IsWeightedHomogeneous unitE_w (φ i) (c * unitE_w i)) :
    IsWeightedHomogeneous unitE_w (aeval φ f) (c * m) := by
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simpa using isWeightedHomogeneous_zero ℚ unitE_w (c * m)
  | add p q _ _ hp hq => rw [map_add]; exact hp.add hq
  | monomial d r hr =>
    rw [aeval_monomial, algebraMap_eq, Finsupp.prod]
    have hprod := IsWeightedHomogeneous.prod d.support (fun i => φ i ^ d i)
      (fun i => d i • (c * unitE_w i)) (fun i _ => (hφ i).pow (d i))
    have hdeg : ∑ i ∈ d.support, d i • (c * unitE_w i) = c * m := by
      rw [← hr, Finsupp.weight_apply, Finsupp.sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [smul_eq_mul]; ring
    rw [hdeg] at hprod
    exact hprod.C_mul r

lemma unitE_adams_isWH {g : SF} {n : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (hg : IsWeightedHomogeneous unitE_w g n) :
    IsWeightedHomogeneous unitE_w (adams k g) (k * n) := by
  rw [unitE_adams_eq, rename_eq_aeval]
  refine unitE_aeval_isWH k _ hg fun i => ?_
  have h1 : k * (i + 1) - 1 + 1 = k * (i + 1) := Nat.sub_add_cancel (by nlinarith)
  have := isWeightedHomogeneous_X ℚ unitE_w (k * (i + 1) - 1)
  simpa only [Function.comp_apply, unitE_w, h1] using this

lemma unitE_plethysm_isWH {f g : SF} {m n : ℕ}
    (hf : IsWeightedHomogeneous unitE_w f m) (hg : IsWeightedHomogeneous unitE_w g n) :
    IsWeightedHomogeneous unitE_w (plethysm f g) (n * m) := by
  rw [unitE_plethysm_eq_aeval]
  refine unitE_aeval_isWH n _ hf fun i => ?_
  have := unitE_adams_isWH (i + 1) (by omega) hg
  rwa [mul_comm] at this

lemma unitE_complete_isWH (n : ℕ) : IsWeightedHomogeneous unitE_w (complete n) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simpa [complete] using isWeightedHomogeneous_one ℚ unitE_w
    | n + 1 =>
      rw [complete]
      refine IsWeightedHomogeneous.C_mul ?_ _
      refine IsWeightedHomogeneous.sum _ _ _ fun k _ => ?_
      have hk := k.isLt
      have hX : power (k.val + 1) = X k.val := by simp [power]
      rw [hX]
      have := (isWeightedHomogeneous_X ℚ unitE_w k.val).mul (ih (n - k.val) (by omega))
      have hd : unitE_w k.val + (n - k.val) = n + 1 := by simp only [unitE_w]; omega
      rwa [hd] at this

lemma unitE_iterated_isWH (ns : List ℕ) :
    IsWeightedHomogeneous unitE_w (iterated ns) ns.prod := by
  induction ns with
  | nil =>
    simpa [iterated, unitE_power_one] using isWeightedHomogeneous_X ℚ unitE_w 0
  | cons n ns ih =>
    rw [iterated, List.prod_cons, mul_comm]
    exact unitE_plethysm_isWH (unitE_complete_isWH n) ih

/-- Deliverable 2: every iterated plethysm has a Schur expansion in its degree. -/
theorem iterated_expansion_exists (hX : ExpansionsExist) (ns : List ℕ)
    (_hns : ∀ n ∈ ns, 1 ≤ n) : ∃ c, SchurExpansion ns.prod (iterated ns) c :=
  hX _ _ (unitE_iterated_isWH ns)

/-! ### Reduction to `g[h_a]` -/

lemma unitE_iterated_filter (ns : List ℕ) :
    iterated ns = iterated (ns.filter (· ≠ 1)) := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    by_cases hn : n = 1
    · subst hn
      simp [iterated, ih, unitE_complete_one, unitE_plethysm_power_one_left]
    · simp [iterated, ih, hn]

lemma unitE_prod_filter (ns : List ℕ) : ns.prod = (ns.filter (· ≠ 1)).prod := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    by_cases hn : n = 1
    · subst hn; simp [ih]
    · simp [ih, hn]

lemma unitE_iterated_concat (init : List ℕ) (a : ℕ) :
    iterated (init ++ [a]) = plethysm (iterated init) (complete a) := by
  induction init with
  | nil =>
    simp [iterated, unitE_plethysm_power_one_right, unitE_plethysm_power_one_left]
  | cons n init ih =>
    rw [List.cons_append, iterated, ih, iterated, unitE_plethysm_assoc]

/-! ### Palindromes -/

lemma unitE_filter_range_ext (b : ℕ → ℚ) {M M' : ℕ} (hM : M ≤ M')
    (hz : ∀ β, M ≤ β → β < M' → b β = 0) :
    ((List.range M').map b).filter (· ≠ 0) = ((List.range M).map b).filter (· ≠ 0) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hM
  rw [List.range_add, List.map_append, List.filter_append]
  suffices h : ((List.map (M + ·) (List.range k)).map b).filter (· ≠ 0) = [] by
    rw [h, List.append_nil]
  rw [List.filter_eq_nil_iff]
  intro x hx
  simp only [List.map_map, List.mem_map, List.mem_range, Function.comp_apply] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  simp [hz (M + j) (by omega) (by omega)]

lemma unitE_palindrome (b : ℕ → ℚ) (D : ℕ) (hz : ∀ β, D ≤ β → b β = 0)
    (hs : ∀ β, β < D → b β = b (D - 1 - β)) : NonzeroPalindrome b := by
  have hD : ((List.range D).map b).reverse = (List.range D).map b := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.length_reverse, List.length_map, List.length_range] at h1
    simp only [List.getElem_reverse, List.getElem_map, List.getElem_range, List.length_map,
      List.length_range]
    rw [hs i h1]
  have hDpal : (((List.range D).map b).filter (· ≠ 0)).reverse =
      ((List.range D).map b).filter (· ≠ 0) := by
    rw [← List.filter_reverse, hD]
  refine ⟨⟨D, hz⟩, fun M hM => ?_⟩
  rcases le_total D M with h | h
  · rw [unitE_filter_range_ext b h fun β hβ _ => hz β hβ]; exact hDpal
  · rw [← unitE_filter_range_ext b h fun β hβ _ => hM β hβ]; exact hDpal

/-! ### Question 1 -/

lemma unitE_hookCoeff_one (c : List ℕ →₀ ℚ) (β : ℤ) (γ : ℕ) (h : ¬ (β = 0 ∧ γ = 0)) :
    hookCoeff 1 c β γ = 0 := by
  simp only [hookCoeff]
  split_ifs with h'
  · omega
  · rfl

/-- Deliverable 1: the endpoint for `g[h_a]` settles Question 1 for all iterated plethysms. -/
theorem question1_of (hE : FullEndpoint) : Question1 := by
  intro ns _ hns c hc γ
  rw [unitE_prod_filter, unitE_iterated_filter] at hc
  rw [unitE_prod_filter]
  have hL : ∀ n ∈ ns.filter (· ≠ 1), 2 ≤ n := by
    intro n hn
    simp only [List.mem_filter, decide_eq_true_eq] at hn
    have := hns n hn.1
    omega
  generalize ns.filter (· ≠ 1) = L at hc hL ⊢
  rcases List.eq_nil_or_concat L with rfl | ⟨init, a, rfl⟩
  · -- no factor besides `h₁`: the function is `p₁`, of degree `1`
    refine unitE_palindrome _ (1 - γ) (fun β hβ => ?_) (fun β hβ => ?_)
    · exact unitE_hookCoeff_one c β γ (by omega)
    · congr 2; omega
  · rw [List.concat_eq_append] at hc hL ⊢
    have ha : 2 ≤ a := hL a (by simp)
    have hd : 1 ≤ init.prod := by
      rw [Nat.one_le_iff_ne_zero, Ne, List.prod_eq_zero_iff]
      intro h0
      have := hL 0 (by simp [h0])
      omega
    have hN : (init ++ [a]).prod = a * init.prod := by simp [mul_comm]
    rw [hN, unitE_iterated_concat] at hc
    rw [hN]
    obtain ⟨hrefl, hzero, -⟩ :=
      hE init.prod a (iterated init) c hd ha (unitE_iterated_isWH init) hc
    refine unitE_palindrome _ (init.prod - γ) (fun β hβ => ?_) (fun β hβ => ?_)
    · exact hzero β γ (by omega)
    · rw [hrefl]
      congr 1
      omega

end GR22

#print axioms GR22.question1_of
#print axioms GR22.iterated_expansion_exists
