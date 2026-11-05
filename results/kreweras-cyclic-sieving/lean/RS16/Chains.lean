import RS16.Defs

/-!
# Length-additive factorisations and chains (the paper, Step 2, last part)

For a length `ℓ` that is subadditive, invariant under conjugation and zero exactly at `1`,
the number `F_u(m₁)` of factorisations `u = x₁ ⋯ x_{m₁}` into elements of `C = C_G(c^{h₁})` with
`Σ ℓ(x_j) = ℓ(u)` is `Σ_k binom(m₁, k) c_k(u)` (`fcount_eq_chains`).
-/

open scoped Classical

set_option linter.unusedSectionVars false

namespace RS16

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The hypotheses on the length function (reflection length in a Weyl group). -/
structure LenHyp (ℓ : G → ℕ) : Prop where
  mul : ∀ x y, ℓ (x * y) ≤ ℓ x + ℓ y
  conj : ∀ g x, ℓ (g * x * g⁻¹) = ℓ x
  zero : ∀ x, ℓ x = 0 ↔ x = 1

namespace LenHyp

variable {ℓ : G → ℕ} (hl : LenHyp ℓ)
include hl

lemma one : ℓ 1 = 0 := (hl.zero 1).mpr rfl

lemma le_split (z u : G) : ℓ u ≤ ℓ z + ℓ (z⁻¹ * u) := by
  simpa using hl.mul z (z⁻¹ * u)

lemma absLE_trans {z y u : G} (h1 : absLE ℓ z y) (h2 : absLE ℓ y u) : absLE ℓ z u := by
  unfold absLE at *
  have a := hl.le_split z u
  have b := hl.mul (z⁻¹ * y) (y⁻¹ * u)
  rw [show z⁻¹ * y * (y⁻¹ * u) = z⁻¹ * u by group] at b
  omega

lemma absLE_le {z u : G} (h : absLE ℓ z u) : ℓ z ≤ ℓ u := by
  unfold absLE at h; omega

lemma absLE_lt {z u : G} (h : absLE ℓ z u) (hne : z ≠ u) : ℓ z < ℓ u := by
  unfold absLE at h
  have : ℓ (z⁻¹ * u) ≠ 0 := by
    rw [Ne, hl.zero, inv_mul_eq_one]; exact hne
  omega

lemma absLE_one (u : G) : absLE ℓ 1 u := by
  simp [absLE, hl.one]

lemma list_prod_le (l : List G) : ℓ l.prod ≤ (l.map ℓ).sum := by
  induction l with
  | nil => simp [hl.one]
  | cons a l ih =>
    simp only [List.prod_cons, List.map_cons, List.sum_cons]
    exact (hl.mul _ _).trans (by omega)

lemma ofFn_prod_le {m : ℕ} (B : Fin m → G) : ℓ (List.ofFn B).prod ≤ ∑ r, ℓ (B r) := by
  have := hl.list_prod_le (List.ofFn B)
  rwa [List.map_ofFn, List.sum_ofFn] at this

end LenHyp

lemma commute_ofFn_prod {m : ℕ} {a : G} (B : Fin m → G) (h : ∀ r, Commute (B r) a) :
    Commute (List.ofFn B).prod a := by
  apply Commute.list_prod_left
  intro x hx
  obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hx
  exact h r

/-- `F_u(m)`: factorisations of `u` into `m` elements of `C` with additive length. -/
noncomputable def fcount (ℓ : G → ℕ) (c : G) (h1 m : ℕ) (u : G) : ℕ :=
  (Finset.univ.filter fun B : Fin m → G =>
    (∀ r, Commute (B r) (c ^ h1)) ∧ (List.ofFn B).prod = u ∧ ∑ r, ℓ (B r) = ℓ u).card

variable {ℓ : G → ℕ} (hl : LenHyp ℓ) (c : G) (h1 : ℕ)
include hl

lemma fcount_zero (u : G) : fcount ℓ c h1 0 u = if u = 1 then 1 else 0 := by
  unfold fcount
  split_ifs with hu
  · subst hu
    rw [Finset.filter_true_of_mem (fun B _ => ⟨fun r => r.elim0, by simp, by simp [hl.one]⟩)]
    simp
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro B _ ⟨_, hp, _⟩
    exact hu (by simpa using hp.symm)

omit hl in
lemma ofFn_prod_snoc {m : ℕ} (B : Fin (m + 1) → G) :
    (List.ofFn B).prod = (List.ofFn (Fin.init B)).prod * B (Fin.last m) := by
  rw [List.ofFn_succ', List.prod_concat]; rfl

/-- the key inequality: a length-additive `(m+1)`-factorisation of `u` has its first `m` factors
length-additive with product `z ≤ u` -/
lemma split_snoc {m : ℕ} {u : G} (B : Fin (m + 1) → G) (hp : (List.ofFn B).prod = u)
    (hs : ∑ r, ℓ (B r) = ℓ u) :
    ∑ r, ℓ (Fin.init B r) = ℓ (List.ofFn (Fin.init B)).prod ∧
      absLE ℓ (List.ofFn (Fin.init B)).prod u := by
  set z := (List.ofFn (Fin.init B)).prod
  rw [ofFn_prod_snoc] at hp
  rw [Fin.sum_univ_castSucc] at hs
  have h1' := hl.ofFn_prod_le (Fin.init B)
  have h2 := hl.le_split z u
  have hlast : B (Fin.last m) = z⁻¹ * u := by rw [← hp]; exact (inv_mul_cancel_left _ _).symm
  rw [hlast] at hs
  change ∑ i : Fin m, ℓ (B i.castSucc) + ℓ (z⁻¹ * u) = ℓ u at hs
  change ℓ z ≤ ∑ i : Fin m, ℓ (B i.castSucc) at h1'
  change ∑ i : Fin m, ℓ (B i.castSucc) = ℓ z ∧ ℓ z + ℓ (z⁻¹ * u) = ℓ u
  omega

lemma fcount_succ (m : ℕ) {u : G} (hu : Commute u (c ^ h1)) :
    fcount ℓ c h1 (m + 1) u =
      ∑ z ∈ Finset.univ.filter (fun z => Commute z (c ^ h1) ∧ absLE ℓ z u), fcount ℓ c h1 m z := by
  unfold fcount
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun B : Fin (m + 1) → G => (List.ofFn (Fin.init B)).prod)]
  · apply Finset.sum_congr rfl
    intro z hz
    have hz' := (Finset.mem_filter.mp hz).2
    refine Finset.card_bij' (fun B _ => Fin.init B) (fun B' _ => Fin.snoc B' (z⁻¹ * u))
      ?_ ?_ ?_ ?_
    · intro B hB
      obtain ⟨hB1, hBz⟩ := Finset.mem_filter.mp hB
      obtain ⟨-, hC, hp, hs⟩ := Finset.mem_filter.mp hB1
      have := split_snoc hl B hp hs
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r => hC _, hBz, ?_⟩
      rw [← hBz]; exact this.1
    · intro B' hB'
      obtain ⟨-, hC, hp, hs⟩ := Finset.mem_filter.mp hB'
      have hzu : Commute (z⁻¹ * u) (c ^ h1) := hz'.1.inv_left.mul_left hu
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r => ?_, ?_, ?_⟩,
        by simp [hp]⟩
      · refine Fin.lastCases ?_ (fun i => ?_) r
        · simpa using hzu
        · simpa using hC i
      · rw [ofFn_prod_snoc]; simp [hp]
      · rw [Fin.sum_univ_castSucc]; simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rw [hs]; exact hz'.2
    · intro B hB
      obtain ⟨hB1, hBz⟩ := Finset.mem_filter.mp hB
      obtain ⟨-, -, hp, -⟩ := Finset.mem_filter.mp hB1
      have hlast : B (Fin.last m) = z⁻¹ * u := by
        rw [ofFn_prod_snoc] at hp; rw [← hp, ← hBz]; group
      rw [← hlast]; exact Fin.snoc_init_self B
    · intro B' _
      exact Fin.init_snoc _ _
  · intro B hB
    obtain ⟨-, hC, hp, hs⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hB)
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      commute_ofFn_prod _ fun r => hC _, (split_snoc hl B hp hs).2⟩)

omit hl in
lemma pascal_sum (m M : ℕ) (a : ℕ → ℕ) (ha : a (M + 1) = 0) :
    ∑ k ∈ Finset.range (M + 1), (m.choose k * a k + m.choose k * a (k + 1)) =
      ∑ k ∈ Finset.range (M + 1), (m + 1).choose k * a k := by
  rw [Finset.sum_add_distrib, Finset.sum_range_succ' (fun k => (m + 1).choose k * a k),
    Finset.sum_range_succ' (fun k => m.choose k * a k),
    Finset.sum_range_succ (fun k => m.choose k * a (k + 1)), ha]
  simp only [Nat.choose_succ_succ', add_mul, Finset.sum_add_distrib, Nat.choose_zero_right]
  ring

lemma chains_eq_zero : ∀ (k : ℕ) (u : G), ℓ u < k → chains ℓ c h1 k u = 0
  | 0, u, h => absurd h (Nat.not_lt_zero _)
  | k + 1, u, h => by
      rw [chains]
      apply Finset.sum_eq_zero
      intro z hz
      simp only [Finset.mem_filter] at hz
      exact chains_eq_zero k z (by have := hl.absLE_lt hz.2.2 hz.2.1; omega)

/-- `F_u(m) = Σ_{k ≤ M} binom(m, k) c_k(u)` for `u ∈ NC(W) ∩ C` and `M = ℓ(c)`. -/
theorem fcount_eq_chains (m : ℕ) : ∀ u ∈ ncC ℓ c h1,
    fcount ℓ c h1 m u = ∑ k ∈ Finset.range (ℓ c + 1), m.choose k * chains ℓ c h1 k u := by
  induction m with
  | zero =>
    intro u _
    rw [fcount_zero hl, Finset.sum_eq_single 0]
    · simp [chains]
    · intro k _ hk; simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hk)]
    · simp
  | succ m ih =>
    intro u hu
    have hu' := hu
    simp only [ncC, Finset.mem_filter, Finset.mem_univ, true_and] at hu'
    rw [fcount_succ hl c h1 m hu'.2]
    -- the `z ≤ u` in `C` are `u` and the `z < u` in `NC ∩ C`
    have hset : Finset.univ.filter (fun z => Commute z (c ^ h1) ∧ absLE ℓ z u) =
        insert u ((ncC ℓ c h1).filter fun z => z ≠ u ∧ absLE ℓ z u) := by
      ext z
      simp only [ncC, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨hC, hz⟩
        by_cases hzu : z = u
        · exact Or.inl hzu
        · exact Or.inr ⟨⟨hl.absLE_trans hz hu'.1, hC⟩, hzu, hz⟩
      · rintro (rfl | ⟨⟨_, hC⟩, _, hz⟩)
        · exact ⟨hu'.2, by simp [absLE, hl.one]⟩
        · exact ⟨hC, hz⟩
    rw [hset, Finset.sum_insert (by simp)]
    rw [Finset.sum_congr rfl (fun z hz => ih z (Finset.mem_filter.mp hz).1), ih u hu,
      Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    have hchain : ∀ k, ∑ z ∈ (ncC ℓ c h1).filter (fun z => z ≠ u ∧ absLE ℓ z u),
        chains ℓ c h1 k z = chains ℓ c h1 (k + 1) u := fun k => by rw [chains]
    simp_rw [hchain]
    -- Pascal's rule
    have hlu : ℓ u ≤ ℓ c := hl.absLE_le hu'.1
    exact pascal_sum m (ℓ c) (fun k => chains ℓ c h1 k u)
      (chains_eq_zero hl c h1 (ℓ c + 1) u (by omega))

end RS16
