import SpinningSwitches.Necessity

/-!
# Sufficiency: when `G` and `H` are `p`-groups the puzzle has a surjective strategy

This is Kagey's Theorem 22, reproved here through the excluded-set dynamics with the full
adversary group: the excluded set is grown through a chain of `H`-invariant normal subgroups of
the base, obtained from the upper central series of the `p`-group `(Ω → G) ⋊ H`.
-/

namespace SpinningSwitches

variable {G H Ω : Type*} [Group G] [Group H] [MulAction H Ω]

section Dynamics

variable (H) in
/-- One step of the excluded-set dynamics against the full adversary group. -/
def stepH (E : Set (Ω → G)) (k : Ω → G) : Set (Ω → G) :=
  {y | y = 1 ∨ ∀ a : H, spin G H Ω a y * k⁻¹ ∈ E}

variable (H) in
/-- States certainly excluded after the moves `ks`. -/
def exclH (ks : List (Ω → G)) : Set (Ω → G) := ks.foldl (stepH H) {1}

theorem exclH_append (ks : List (Ω → G)) (k : Ω → G) :
    exclH H (ks ++ [k]) = stepH H (exclH H ks) k := by
  simp [exclH, List.foldl_append]

/-- Soundness: a state that never reached the light is never excluded. -/
theorem not_mem_exclH (ks : List (Ω → G)) : ∀ hs : List H, hs.length = ks.length →
    ∀ x0 : Ω → G, (∀ j ≤ ks.length, x0 * ((List.zipWith turn ks hs).take j).prod.left ≠ 1) →
    spin G H Ω ((List.zipWith turn ks hs).prod.right)⁻¹
      (x0 * (List.zipWith turn ks hs).prod.left) ∉ exclH H ks := by
  induction ks using List.reverseRecOn with
  | nil =>
    intro hs hlen x0 hpre
    have : hs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst this
    have h0 := hpre 0 le_rfl
    simp only [exclH, List.foldl_nil, Set.mem_singleton_iff]
    simpa using h0
  | append_singleton ks k ih =>
    intro hs hlen x0 hpre
    obtain ⟨hs', a, rfl⟩ : ∃ hs' a, hs = hs' ++ [a] := by
      have hne : hs ≠ [] := by
        intro h; subst h; simp at hlen
      exact ⟨hs.dropLast, hs.getLast hne, (List.dropLast_append_getLast hne).symm⟩
    have hlen' : hs'.length = ks.length := by simpa using hlen
    rw [zipWith_turn_append ks hs' hlen' k a] at hpre ⊢
    have hpre' : ∀ j ≤ ks.length, x0 * ((List.zipWith turn ks hs').take j).prod.left ≠ 1 := by
      intro j hj
      have := hpre j (by simp; omega)
      rwa [List.take_append_of_le_length (by simp [hlen']; omega)] at this
    have hIH := ih hs' hlen' x0 hpre'
    set X := (List.zipWith turn ks hs').prod with hX
    have hlast := hpre (ks.length + 1) (by simp)
    have hfull : (List.zipWith turn ks hs' ++ [turn k a]).take (ks.length + 1) =
        List.zipWith turn ks hs' ++ [turn k a] := by
      apply List.take_of_length_le; simp [hlen']
    rw [hfull, List.prod_append, List.prod_singleton, ← hX] at hlast
    rw [exclH_append, List.prod_append, List.prod_singleton, ← hX]
    rintro (h1 | h2)
    · apply hlast
      have := congrArg (spin G H Ω (X * turn k a).right) h1
      simpa using this
    · apply hIH
      have := h2 a
      convert this using 1
      simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, turn_left, turn_right,
        mul_inv_rev, map_mul, MulAut.mul_apply, map_inv]
      simp [mul_assoc]

theorem strategy_of_exclH (ks : List (Ω → G)) (h : exclH H ks = Set.univ) :
    IsSurjectiveStrategy H ks := by
  intro hs hlen x
  by_contra hx
  push Not at hx
  apply not_mem_exclH ks hs hlen x⁻¹ (fun j hj hj1 => hx j hj ?_)
  · rw [h]; trivial
  · rw [← mul_left_cancel_iff (a := x⁻¹), hj1, inv_mul_cancel]

theorem stepH_mono {E F : Set (Ω → G)} (hEF : E ⊆ F) (k : Ω → G) :
    stepH H E k ⊆ stepH H F k := by
  rintro y (h | h)
  · exact Or.inl h
  · exact Or.inr fun a => hEF (h a)

theorem foldl_stepH_mono (s : List (Ω → G)) : ∀ {E F : Set (Ω → G)}, E ⊆ F →
    s.foldl (stepH H) E ⊆ s.foldl (stepH H) F := by
  induction s with
  | nil => intro E F h; simpa using h
  | cons k s ih => intro E F h; exact ih (stepH_mono h k)

/-- Moves inside `L` keep any right-`L`-invariant, `H`-invariant set `A` excluded. -/
theorem foldl_absorb (L : Subgroup (Ω → G)) (A : Set (Ω → G))
    (hAH : ∀ (a : H) y, y ∈ A → spin G H Ω a y ∈ A) (hAL : ∀ y ∈ A, ∀ l ∈ L, y * l ∈ A)
    (s : List (Ω → G)) (hs : ∀ k ∈ s, k ∈ L) : ∀ {E F : Set (Ω → G)}, F ∪ A ⊆ E →
    s.foldl (stepH H) F ∪ A ⊆ s.foldl (stepH H) E := by
  induction s with
  | nil => intro E F h; simpa using h
  | cons k s ih =>
    intro E F h
    simp only [List.foldl_cons]
    apply ih (fun k hk => hs k (List.mem_cons_of_mem _ hk))
    rintro y (hy | hy)
    · exact stepH_mono (fun z hz => h (Or.inl hz)) k hy
    · refine Or.inr fun a => h (Or.inr ?_)
      exact hAL _ (hAH a y hy) _ (L.inv_mem (hs k (List.mem_cons_self ..)))

end Dynamics

section Growth

variable (L : Subgroup (Ω → G)) [hLn : L.Normal]
  (hLH : ∀ (a : H) x, x ∈ L → spin G H Ω a x ∈ L)

include hLn in
theorem pow_mul_mem (v : Ω → G) {m : Ω → G} (hm : m ∈ L) (j : ℕ) :
    ∃ m' ∈ L, (m * v) ^ j = m' * v ^ j := by
  induction j with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ j ih =>
    obtain ⟨m', hm', he⟩ := ih
    refine ⟨m' * (v ^ j * m * (v ^ j)⁻¹), L.mul_mem hm' (hLn.conj_mem _ hm _), ?_⟩
    rw [pow_succ, he, pow_succ]; group

variable (u : Ω → G) (hu : ∀ a : H, u⁻¹ * spin G H Ω a u ∈ L)

/-- `L`-cosets of the first `i` powers of `u⁻¹`. -/
def cosets (i : ℕ) : Set (Ω → G) := {y | ∃ j < i, ∃ l ∈ L, y = l * u⁻¹ ^ j}

/-- `L`-cosets of the powers `1, …, i` of `u⁻¹`. -/
def cosets' (i : ℕ) : Set (Ω → G) := {y | ∃ j, 1 ≤ j ∧ j ≤ i ∧ ∃ l ∈ L, y = l * u⁻¹ ^ j}

include hLn hu in
theorem spin_inv_pow (a : H) (j : ℕ) : ∃ m ∈ L, spin G H Ω a (u⁻¹ ^ j) = m * u⁻¹ ^ j := by
  have hm := L.inv_mem (hu a)
  obtain ⟨m', hm', he⟩ := pow_mul_mem L u⁻¹ hm j
  refine ⟨m', hm', ?_⟩
  rw [map_pow, map_inv, ← he]
  congr 1; group

include hLn hLH hu in
theorem cosets'_spin (i : ℕ) (a : H) (y : Ω → G) (hy : y ∈ cosets' L u i) :
    spin G H Ω a y ∈ cosets' L u i := by
  obtain ⟨j, hj1, hji, l, hl, rfl⟩ := hy
  obtain ⟨m, hm, he⟩ := spin_inv_pow L u hu a j
  exact ⟨j, hj1, hji, spin G H Ω a l * m, L.mul_mem (hLH a l hl) hm, by rw [map_mul, he, mul_assoc]⟩

include hLn in
theorem cosets'_mul (i : ℕ) (y : Ω → G) (hy : y ∈ cosets' L u i) (l' : Ω → G) (hl' : l' ∈ L) :
    y * l' ∈ cosets' L u i := by
  obtain ⟨j, hj1, hji, l, hl, rfl⟩ := hy
  refine ⟨j, hj1, hji, l * (u⁻¹ ^ j * l' * (u⁻¹ ^ j)⁻¹), L.mul_mem hl (hLn.conj_mem _ hl' _), ?_⟩
  group

include hLn hLH hu in
theorem move_u (i : ℕ) {E : Set (Ω → G)} (hE : cosets L u i ⊆ E) :
    {1} ∪ cosets' L u i ⊆ stepH H E u⁻¹ := by
  rintro y (hy | ⟨j, hj1, hji, l, hl, rfl⟩)
  · exact Or.inl hy
  · refine Or.inr fun a => hE ?_
    obtain ⟨m, hm, he⟩ := spin_inv_pow L u hu a j
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    refine ⟨j', by omega, spin G H Ω a l * m, L.mul_mem (hLH a l hl) hm, ?_⟩
    rw [map_mul, he, inv_inv, pow_succ]; group

/-- The interleaved tour `s, u⁻¹, s, u⁻¹, …, s` with `i + 1` copies of `s`. -/
def tour (s : List (Ω → G)) : ℕ → List (Ω → G)
  | 0 => s
  | i + 1 => tour s i ++ [u⁻¹] ++ s

omit hLn in
theorem tour_mem (s : List (Ω → G)) (hs : ∀ k ∈ s, k ∈ L) (i : ℕ) :
    ∀ k ∈ tour u s i, k ∈ L ∨ k = u⁻¹ := by
  induction i with
  | zero => intro k hk; exact Or.inl (hs k hk)
  | succ i ih =>
    intro k hk
    simp only [tour, List.mem_append, List.mem_singleton] at hk
    rcases hk with (hk | hk) | hk
    · exact ih k hk
    · exact Or.inr hk
    · exact Or.inl (hs k hk)

include hLn hLH hu in
theorem cosets_subset_tour (s : List (Ω → G)) (hs : ∀ k ∈ s, k ∈ L)
    (hsL : (L : Set (Ω → G)) ⊆ exclH H s) (i : ℕ) :
    cosets L u (i + 1) ⊆ exclH H (tour u s i) := by
  induction i with
  | zero =>
    rintro y ⟨j, hj, l, hl, rfl⟩
    obtain rfl : j = 0 := by omega
    simpa [tour] using hsL hl
  | succ i ih =>
    have hstep := move_u (H := H) L hLH u hu (i + 1) ih
    have habs := foldl_absorb (H := H) L (cosets' L u (i + 1))
      (fun a y hy => cosets'_spin L hLH u hu (i + 1) a y hy)
      (fun y hy l hl => cosets'_mul L u (i + 1) y hy l hl) s hs hstep
    have heq : exclH H (tour u s (i + 1)) =
        s.foldl (stepH H) (stepH H (exclH H (tour u s i)) u⁻¹) := by
      simp [tour, exclH, List.foldl_append]
    rw [heq]
    rintro y ⟨j, hj, l, hl, rfl⟩
    apply habs
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · left; simpa [exclH] using hsL hl
    · right; exact ⟨j, hj0, by omega, l, hl, rfl⟩

end Growth

section Chain

variable [Finite G] [Finite Ω]

theorem inv_pow_eq (v : Ω → G) (j : ℕ) : (v ^ j)⁻¹ = v ^ (j * (orderOf v - 1)) := by
  have hpos : 0 < orderOf v := orderOf_pos v
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_add, show j + j * (orderOf v - 1) = orderOf v * j by
    rw [Nat.mul_sub, mul_one, mul_comm]
    have : j ≤ orderOf v * j := Nat.le_mul_of_pos_left j hpos
    omega, pow_mul, pow_orderOf_eq_one, one_pow]

/-- The subgroup `L ⟨u⟩`, for `L` normal. -/
def extend (L : Subgroup (Ω → G)) [hLn : L.Normal] (u : Ω → G) : Subgroup (Ω → G) where
  carrier := {x | ∃ l ∈ L, ∃ j : ℕ, x = l * u⁻¹ ^ j}
  one_mem' := ⟨1, L.one_mem, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨l, hl, i, rfl⟩ ⟨l', hl', j, rfl⟩
    refine ⟨l * (u⁻¹ ^ i * l' * (u⁻¹ ^ i)⁻¹), L.mul_mem hl (hLn.conj_mem _ hl' _), i + j, ?_⟩
    rw [pow_add]; group
  inv_mem' := by
    rintro _ ⟨l, hl, i, rfl⟩
    refine ⟨(u⁻¹ ^ i)⁻¹ * l⁻¹ * ((u⁻¹ ^ i)⁻¹)⁻¹, hLn.conj_mem _ (L.inv_mem hl) _,
      i * (orderOf u⁻¹ - 1), ?_⟩
    rw [← inv_pow_eq]; group

theorem extend_props (L : Subgroup (Ω → G)) [hLn : L.Normal]
    (hLH : ∀ (a : H) x, x ∈ L → spin G H Ω a x ∈ L) (u : Ω → G)
    (hu : ∀ a : H, u⁻¹ * spin G H Ω a u ∈ L) (hcomm : ∀ x, u * x * u⁻¹ * x⁻¹ ∈ L) :
    (extend L u).Normal ∧ (∀ (a : H) x, x ∈ extend L u → spin G H Ω a x ∈ extend L u) ∧
      L ≤ extend L u ∧ u ∈ extend L u ∧
      ∀ s : List (Ω → G), (∀ k ∈ s, k ∈ L) → (L : Set (Ω → G)) ⊆ exclH H s →
        ∃ s', (∀ k ∈ s', k ∈ extend L u) ∧ (extend L u : Set (Ω → G)) ⊆ exclH H s' := by
  have hu1 : u⁻¹ ∈ extend L u := ⟨1, L.one_mem, 1, by simp⟩
  refine ⟨⟨?_⟩, ?_, fun l hl => ⟨l, hl, 0, by simp⟩, ?_, ?_⟩
  · rintro _ ⟨l, hl, j, rfl⟩ x
    -- x u⁻¹ x⁻¹ = m u⁻¹ with m ∈ L
    have hm : x * u⁻¹ * x⁻¹ * u ∈ L := by
      have := hLn.conj_mem _ (hcomm x) u⁻¹
      convert this using 1; group
    obtain ⟨m', hm', he⟩ := pow_mul_mem L u⁻¹ hm j
    refine ⟨x * l * x⁻¹ * m', L.mul_mem (hLn.conj_mem _ hl x) hm', j, ?_⟩
    have h1 : x * u⁻¹ ^ j * x⁻¹ = (x * u⁻¹ * x⁻¹ * u * u⁻¹) ^ j := by
      rw [mul_inv_cancel_right, conj_pow]
    calc x * (l * u⁻¹ ^ j) * x⁻¹ = x * l * x⁻¹ * (x * u⁻¹ ^ j * x⁻¹) := by group
      _ = x * l * x⁻¹ * (m' * u⁻¹ ^ j) := by rw [h1, he]
      _ = _ := by group
  · rintro a _ ⟨l, hl, j, rfl⟩
    obtain ⟨m, hm, he⟩ := spin_inv_pow L u hu a j
    exact ⟨spin G H Ω a l * m, L.mul_mem (hLH a l hl) hm, j, by rw [map_mul, he, mul_assoc]⟩
  · have := (extend L u).inv_mem hu1
    simpa using this
  · intro s hs hsL
    set n := orderOf u⁻¹ with hn
    have hpos : 0 < n := orderOf_pos _
    refine ⟨tour u s (n - 1), fun k hk => ?_, ?_⟩
    · rcases tour_mem L u s hs (n - 1) k hk with h | h
      · exact ⟨k, h, 0, by simp⟩
      · rw [h]; exact hu1
    · rintro _ ⟨l, hl, j, rfl⟩
      apply cosets_subset_tour (H := H) L hLH u hu s hs hsL (n - 1)
      refine ⟨j % n, by rw [Nat.sub_add_cancel hpos]; exact Nat.mod_lt _ hpos, l, hl, ?_⟩
      rw [hn, pow_mod_orderOf]

theorem exists_exclH_univ {p : ℕ} [Fact p.Prime] [Finite H]
    (hW : IsPGroup p ((Ω → G) ⋊[spin G H Ω] H)) : ∃ s : List (Ω → G), exclH H s = Set.univ := by
  classical
  have : Finite ((Ω → G) ⋊[spin G H Ω] H) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  have hnil := hW.isNilpotent
  obtain ⟨n, hn⟩ := Group.IsNilpotent.nilpotent' (G := (Ω → G) ⋊[spin G H Ω] H)
  let Lc : ℕ → Subgroup (Ω → G) := fun i =>
    (Subgroup.upperCentralSeries ((Ω → G) ⋊[spin G H Ω] H) i).comap SemidirectProduct.inl
  have main : ∀ c : ℕ, ∀ M : Subgroup (Ω → G), M.Normal →
      (∀ (a : H) x, x ∈ M → spin G H Ω a x ∈ M) →
      Nat.card (Ω → G) - Nat.card M ≤ c →
      (∃ s, (∀ k ∈ s, k ∈ M) ∧ (M : Set (Ω → G)) ⊆ exclH H s) →
      ∃ s : List (Ω → G), exclH H s = Set.univ := by
    intro c
    induction c with
    | zero =>
      intro M _ _ hc ⟨s, _, hs⟩
      have hMtop : M = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        have := Subgroup.card_le_card_group M
        omega
      refine ⟨s, Set.eq_univ_of_univ_subset ?_⟩
      simpa [hMtop] using hs
    | succ c ih =>
      intro M hMn hMH hc ⟨s, hsM, hs⟩
      by_cases hMtop : M = ⊤
      · refine ⟨s, Set.eq_univ_of_univ_subset ?_⟩
        simpa [hMtop] using hs
      have hex : ∃ i, ¬ Lc i ≤ M := by
        refine ⟨n, fun h => hMtop (eq_top_iff.mpr fun x _ => h ?_)⟩
        rw [Subgroup.mem_comap, hn]; trivial
      have h0 : Nat.find hex ≠ 0 := by
        intro h0
        apply Nat.find_spec hex
        rw [h0]
        intro x hx
        have : (SemidirectProduct.inl x : (Ω → G) ⋊[spin G H Ω] H) = 1 := by
          rw [Subgroup.mem_comap, Subgroup.upperCentralSeries_zero, Subgroup.mem_bot] at hx
          exact hx
        rw [show x = 1 from SemidirectProduct.inl_injective (by simpa using this)]
        exact M.one_mem
      obtain ⟨i, hi⟩ : ∃ i, Nat.find hex = i + 1 := ⟨Nat.find hex - 1, by omega⟩
      have hle : Lc i ≤ M := by
        have := Nat.find_min hex (show i < Nat.find hex by omega)
        simpa using this
      have hnot := Nat.find_spec hex
      rw [hi] at hnot
      obtain ⟨u, huL, huM⟩ := Set.not_subset.mp hnot
      have huL' : (SemidirectProduct.inl u : (Ω → G) ⋊[spin G H Ω] H) ∈
          Subgroup.upperCentralSeries ((Ω → G) ⋊[spin G H Ω] H) (i + 1) := huL
      have hcent := Subgroup.mem_upperCentralSeries_succ_iff.mp huL'
      have hcomm : ∀ x, u * x * u⁻¹ * x⁻¹ ∈ M := by
        intro x
        apply hle
        rw [Subgroup.mem_comap]
        have := hcent (SemidirectProduct.inl x)
        simpa [commutatorElement_def] using this
      have hu : ∀ a : H, u⁻¹ * spin G H Ω a u ∈ M := by
        intro a
        have h1 : u * (spin G H Ω a u)⁻¹ ∈ M := by
          apply hle
          rw [Subgroup.mem_comap]
          have := hcent (SemidirectProduct.inr a)
          rw [commutatorElement_def] at this
          convert this using 1
          have key : (SemidirectProduct.inl (spin G H Ω a u⁻¹) : (Ω → G) ⋊[spin G H Ω] H) =
              SemidirectProduct.inr a * SemidirectProduct.inl u⁻¹ * SemidirectProduct.inr a⁻¹ :=
            SemidirectProduct.inl_aut a u⁻¹
          rw [map_mul, ← map_inv (spin G H Ω a) u, key, map_inv, map_inv]
          group
        have := hMn.conj_mem _ (M.inv_mem h1) u⁻¹
        convert this using 1; group
      obtain ⟨hN, hNH, hle', huN, hcov⟩ := extend_props M hMH u hu hcomm
      obtain ⟨s', hs'M, hs'⟩ := hcov s hsM hs
      have hlt : M < extend M u := lt_of_le_of_ne hle' (fun h => huM (h ▸ huN))
      have hcard := Subgroup.card_lt_of_lt hlt
      exact ih (extend M u) hN hNH (by omega) ⟨s', hs'M, hs'⟩
  refine main _ ⊥ inferInstance (fun a x hx => ?_) le_rfl ⟨[], by simp, ?_⟩
  · rw [Subgroup.mem_bot] at hx ⊢; rw [hx, map_one]
  · intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hx
    simp [exclH, hx]

end Chain

end SpinningSwitches
