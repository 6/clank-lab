import SpinningSwitches.Defs

/-!
# Necessity: a solvable puzzle forces `G` to be a `q`-group for every adversary of order `q`

Fix `h : H` with `h ^ q = 1` and a switch position `ω` that `h` moves.  We follow the set
`excl` of states the solver has certainly excluded, with the adversary restricted to powers of
`h`, and show it always consists of tuples whose values on the `h`-orbit of `ω` lie in one left
coset of a `q`-subgroup of `G`.
-/

namespace SpinningSwitches

variable {G H Ω : Type*} [Group G] [Group H] [MulAction H Ω]

section Necessity

variable (h : H) (ω : Ω)

/-- The orbit of `ω` under the powers of `h`. -/
def orb : Set Ω := {o | ∃ n : ℕ, h ^ n • ω = o}

/-- `x` is `P`-aligned on the orbit: its values there lie in one left coset of `P`. -/
def Aligned (P : Subgroup G) (x : Ω → G) : Prop :=
  ∀ o ∈ orb h ω, ∀ o' ∈ orb h ω, (x o)⁻¹ * x o' ∈ P

/-- One step of the excluded-set dynamics, adversary restricted to powers of `h`. -/
def step (E : Set (Ω → G)) (k : Ω → G) : Set (Ω → G) :=
  {y | y = 1 ∨ ∀ n : ℕ, (fun o => y (h ^ n • o)) * k⁻¹ ∈ E}

/-- The states certainly excluded after the moves `ks`. -/
def excl (ks : List (Ω → G)) : Set (Ω → G) := ks.foldl (step h) {1}

theorem excl_nil : excl (G := G) h ([] : List (Ω → G)) = {1} := rfl

theorem excl_append (ks : List (Ω → G)) (k : Ω → G) :
    excl h (ks ++ [k]) = step h (excl h ks) k := by
  simp [excl, List.foldl_append]

theorem zipWith_turn_append (ks : List (Ω → G)) (hs : List H) (hlen : hs.length = ks.length)
    (k : Ω → G) (a : H) :
    List.zipWith turn (ks ++ [k]) (hs ++ [a]) = List.zipWith turn ks hs ++ [turn k a] := by
  rw [List.zipWith_append (by simp [hlen])]
  rfl

/-- Tracing an unexcluded state back gives an adversary and an initial state that never wins. -/
theorem chain (ks : List (Ω → G)) :
    ∀ z ∉ excl h ks, ∃ hs : List H, hs.length = ks.length ∧ ∃ x0 : Ω → G,
      (∀ j ≤ ks.length, x0 * ((List.zipWith turn ks hs).take j).prod.left ≠ 1) ∧
      z = spin G H Ω ((List.zipWith turn ks hs).prod.right)⁻¹
        (x0 * (List.zipWith turn ks hs).prod.left) := by
  induction ks using List.reverseRecOn with
  | nil =>
    intro z hz
    refine ⟨[], rfl, z, ?_, ?_⟩
    · intro j _
      simpa [excl_nil] using hz
    · simp
  | append_singleton ks k ih =>
    intro z hz
    rw [excl_append] at hz
    simp only [step, Set.mem_ofPred_eq, not_or, not_forall] at hz
    obtain ⟨hz1, n, hn⟩ := hz
    obtain ⟨hs, hlen, x0, hpre, hw⟩ := ih _ hn
    set X := (List.zipWith turn ks hs).prod with hX
    refine ⟨hs ++ [(h ^ n)⁻¹], by simp [hlen], x0, ?_, ?_⟩
    · intro j hj
      rw [zipWith_turn_append ks hs hlen]
      rcases Nat.lt_or_ge j (ks.length + 1) with hjl | hjl
      · have hj' : j ≤ (List.zipWith turn ks hs).length := by simp [hlen]; omega
        rw [List.take_append_of_le_length hj']
        exact hpre j (by omega)
      · have hjeq : j = (List.zipWith turn ks hs ++ [turn k (h ^ n)⁻¹]).length := by
          simp [hlen] at hj ⊢; omega
        rw [hjeq, List.take_length, List.prod_append, List.prod_singleton, ← hX]
        intro hcontra
        apply hz1
        have key : x0 * X.left = spin G H Ω X.right
            ((fun o => z (h ^ n • o)) * k⁻¹) := by
          rw [hw]; simp
        rw [SemidirectProduct.mul_left, ← mul_assoc, key, ← map_mul] at hcontra
        have h2 : (fun o => z (h ^ n • o)) * k⁻¹ * (turn k (h ^ n)⁻¹ : _).left =
            fun o => z (h ^ n • o) := by
          simp
        rw [h2] at hcontra
        have h3 : (fun o => z (h ^ n • o)) = 1 :=
          (MulEquiv.map_eq_one_iff _).mp hcontra
        funext o
        have := congrFun h3 ((h ^ n)⁻¹ • o)
        simpa using this
    · rw [zipWith_turn_append ks hs hlen, List.prod_append, List.prod_singleton, ← hX]
      rw [SemidirectProduct.mul_left, SemidirectProduct.mul_right, ← mul_assoc]
      have key : x0 * X.left = spin G H Ω X.right
          ((fun o => z (h ^ n • o)) * k⁻¹) := by
        rw [hw]; simp
      rw [key, ← map_mul]
      funext o
      simp only [turn_left, turn_right, map_inv, mul_inv_rev, inv_inv, map_mul,
        MulAut.mul_apply]
      simp
      rw [← map_pow, spin_apply, smul_inv_smul]

theorem not_strategy_of_not_mem (ks : List (Ω → G)) (z : Ω → G) (hz : z ∉ excl h ks) :
    ¬ IsSurjectiveStrategy H ks := by
  intro hS
  obtain ⟨hs, hlen, x0, hpre, -⟩ := chain h ks z hz
  obtain ⟨j, hj, hx⟩ := hS hs hlen x0⁻¹
  exact hpre j hj (by rw [hx]; simp)

end Necessity

section Invariant

variable {h : H} {ω : Ω} {q : ℕ}

theorem smul_mem_orb {o : Ω} (ho : o ∈ orb h ω) : h • o ∈ orb h ω := by
  obtain ⟨n, rfl⟩ := ho
  exact ⟨n + 1, by rw [pow_succ', mul_smul]⟩

theorem self_mem_orb : ω ∈ orb h ω := ⟨0, by simp⟩

theorem exists_pow_smul (hq : 0 < q) (hhq : h ^ q = 1) {o a : Ω} (ho : o ∈ orb h ω)
    (ha : a ∈ orb h ω) : ∃ n : ℕ, h ^ n • o = a := by
  obtain ⟨i, rfl⟩ := ho
  obtain ⟨j, rfl⟩ := ha
  refine ⟨j + (q - 1) * i, ?_⟩
  rw [smul_smul, ← pow_add]
  have : j + (q - 1) * i + i = j + q * i := by
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    simp [add_mul]; ring
  rw [this, pow_add, pow_mul, hhq, one_pow, mul_one]

theorem pow_smul_mem_orb {o : Ω} (ho : o ∈ orb h ω) (n : ℕ) : h ^ n • o ∈ orb h ω := by
  induction n with
  | zero => simpa using ho
  | succ n ih => rw [pow_succ', mul_smul]; exact smul_mem_orb ih

/-- The key closure step: the twisted intersection is a coset `R c`, and `⟨R, c⟩` is a
`q`-group. -/
theorem step_aligned (hq : q.Prime) (hhq : h ^ q = 1) (E : Set (Ω → G)) (k : Ω → G)
    (P : Subgroup G) (hP : IsPGroup q P) (hE : ∀ y ∈ E, Aligned h ω P y) :
    ∃ P' : Subgroup G, IsPGroup q P' ∧ ∀ y ∈ step h E k, Aligned h ω P' y := by
  classical
  -- consecutive differences of a surviving state lie in the twisted intersection
  have hdiff : ∀ y : Ω → G, (∀ n : ℕ, (fun o => y (h ^ n • o)) * k⁻¹ ∈ E) →
      ∀ a ∈ orb h ω, ∀ t ∈ orb h ω, k t * ((y a)⁻¹ * y (h • a)) * (k (h • t))⁻¹ ∈ P := by
    intro y hy a ha t ht
    obtain ⟨n, hn⟩ := exists_pow_smul hq.pos hhq ht ha
    have hal := hE _ (hy n) t ht (h • t) (smul_mem_orb ht)
    have e1 : h ^ n • h • t = h • a := by
      rw [← hn, smul_smul, smul_smul, ← pow_succ, ← pow_succ']
    simp only [Pi.mul_apply, Pi.inv_apply, e1, hn] at hal
    convert hal using 1
    group
  by_cases hex : ∃ y ∈ step h E k, y ≠ 1
  swap
  · push_neg at hex
    refine ⟨⊥, IsPGroup.of_bot, fun y hy => ?_⟩
    rw [hex y hy]
    intro o _ o' _
    simp
  obtain ⟨y0, hy0, hy01⟩ := hex
  have hy0' : ∀ n : ℕ, (fun o => y0 (h ^ n • o)) * k⁻¹ ∈ E := hy0.resolve_left hy01
  set c : G := (y0 ω)⁻¹ * y0 (h • ω) with hc
  have hcC : ∀ t ∈ orb h ω, k t * c * (k (h • t))⁻¹ ∈ P := fun t ht =>
    hdiff y0 hy0' ω self_mem_orb t ht
  -- the subgroup R = ⋂ conjugates of P
  let R : Subgroup G :=
    { carrier := {r | ∀ t ∈ orb h ω, k t * r * (k t)⁻¹ ∈ P}
      one_mem' := fun t _ => by simp
      mul_mem' := fun {a b} ha hb t ht => by
        have := P.mul_mem (ha t ht) (hb t ht)
        convert this using 1; group
      inv_mem' := fun {a} ha t ht => by
        have := P.inv_mem (ha t ht)
        convert this using 1; group }
  have memR : ∀ r, r ∈ R ↔ ∀ t ∈ orb h ω, k t * r * (k t)⁻¹ ∈ P := fun r => Iff.rfl
  -- c normalizes R
  have conjR : ∀ r ∈ R, c * r * c⁻¹ ∈ R := by
    intro r hr t ht
    have := P.mul_mem (P.mul_mem (hcC t ht) (hr _ (smul_mem_orb ht))) (P.inv_mem (hcC t ht))
    convert this using 1; group
  have conjR' : ∀ r ∈ R, c⁻¹ * r * c ∈ R := by
    intro r hr t ht
    set s := h ^ (q - 1) • t with hs
    have hsO : s ∈ orb h ω := pow_smul_mem_orb ht _
    have hst : h • s = t := by
      rw [hs, smul_smul, ← pow_succ', Nat.sub_add_cancel hq.one_lt.le, hhq, one_smul]
    have := P.mul_mem (P.mul_mem (P.inv_mem (hcC s hsO)) (hr s hsO)) (hcC s hsO)
    rw [hst] at this
    convert this using 1; group
  have conjZ : ∀ i : ℤ, ∀ r ∈ R, c ^ i * r * c ^ (-i) ∈ R := by
    intro i
    induction i using Int.induction_on with
    | zero => intro r hr; simpa using hr
    | succ i ih =>
      intro r hr
      have := conjR _ (ih r hr)
      convert this using 1
      simp only [zpow_add, zpow_one, zpow_neg, neg_add, mul_inv_rev]; group
    | pred i ih =>
      intro r hr
      have := conjR' _ (ih r hr)
      convert this using 1
      simp only [zpow_sub, zpow_one, zpow_neg, neg_sub, mul_inv_rev]; group
  -- c ^ q ∈ R
  have hcpow : ∀ m : ℕ, ∀ t ∈ orb h ω, k t * c ^ m * (k (h ^ m • t))⁻¹ ∈ P := by
    intro m
    induction m with
    | zero => intro t _; simp
    | succ m ih =>
      intro t ht
      have := P.mul_mem (ih t ht) (hcC _ (pow_smul_mem_orb ht m))
      rw [pow_succ c m, pow_succ' h m, mul_smul]
      convert this using 1; group
  have hcq : c ^ q ∈ R := by
    intro t ht
    have := hcpow q t ht
    rwa [hhq, one_smul] at this
  have hcqZ : ∀ i : ℤ, (c ^ q) ^ i ∈ R := fun i => R.zpow_mem hcq i
  -- elements of R are q-elements
  have hRq : ∀ r ∈ R, ∃ e : ℕ, r ^ q ^ e = 1 := by
    intro r hr
    obtain ⟨e, he⟩ := hP ⟨_, hr ω self_mem_orb⟩
    refine ⟨e, ?_⟩
    have he' : (k ω * r * (k ω)⁻¹) ^ q ^ e = 1 := by
      have := congrArg Subtype.val he
      simpa using this
    rw [conj_pow] at he'
    simpa using he'
  -- the q-group P' = R ⟨c⟩
  let P' : Subgroup G :=
    { carrier := {x | ∃ r ∈ R, ∃ i : ℤ, x = r * c ^ i}
      one_mem' := ⟨1, R.one_mem, 0, by simp⟩
      mul_mem' := fun {a b} ha hb => by
        obtain ⟨r, hr, i, rfl⟩ := ha
        obtain ⟨r', hr', j, rfl⟩ := hb
        refine ⟨r * (c ^ i * r' * c ^ (-i)), R.mul_mem hr (conjZ i r' hr'), i + j, ?_⟩
        rw [zpow_add, zpow_neg]; group
      inv_mem' := fun {a} ha => by
        obtain ⟨r, hr, i, rfl⟩ := ha
        refine ⟨c ^ (-i) * r⁻¹ * c ^ (-(-i)), conjZ (-i) _ (R.inv_mem hr), -i, ?_⟩
        rw [zpow_neg, neg_neg]; group }
  have powform : ∀ r ∈ R, ∀ i : ℤ, ∀ m : ℕ, ∃ r' ∈ R, (r * c ^ i) ^ m = r' * c ^ (i * m) := by
    intro r hr i m
    induction m with
    | zero => exact ⟨1, R.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨r', hr', he⟩ := ih
      refine ⟨r' * (c ^ (i * m) * r * c ^ (-(i * m))), R.mul_mem hr' (conjZ _ r hr), ?_⟩
      rw [pow_succ, he]
      push_cast
      rw [mul_add, mul_one, zpow_add, zpow_neg]; group
  have hP'q : IsPGroup q P' := by
    rintro ⟨x, r, hr, i, rfl⟩
    obtain ⟨r', hr', he⟩ := powform r hr i q
    have hmem : (r * c ^ i) ^ q ∈ R := by
      rw [he, mul_comm i, zpow_mul, zpow_natCast]
      exact R.mul_mem hr' (hcqZ i)
    obtain ⟨e, he'⟩ := hRq _ hmem
    refine ⟨e + 1, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_succ', pow_mul, he']
  have hCP' : ∀ d : G, (∀ t ∈ orb h ω, k t * d * (k (h • t))⁻¹ ∈ P) → d ∈ P' := by
    intro d hd
    refine ⟨d * c⁻¹, fun t ht => ?_, 1, by simp⟩
    have := P.mul_mem (hd t ht) (P.inv_mem (hcC t ht))
    convert this using 1; group
  refine ⟨P', hP'q, fun y hy => ?_⟩
  rcases hy with rfl | hy
  · intro o _ o' _; simp
  have hcons : ∀ a ∈ orb h ω, (y a)⁻¹ * y (h • a) ∈ P' := fun a ha =>
    hCP' _ (fun t ht => hdiff y hy a ha t ht)
  have hpath : ∀ o ∈ orb h ω, ∀ n : ℕ, (y o)⁻¹ * y (h ^ n • o) ∈ P' := by
    intro o ho n
    induction n with
    | zero => simp
    | succ n ih =>
      have := P'.mul_mem ih (hcons _ (pow_smul_mem_orb ho n))
      rw [pow_succ', mul_smul]
      convert this using 1; group
  intro o ho o' ho'
  obtain ⟨n, rfl⟩ := exists_pow_smul hq.pos hhq ho ho'
  exact hpath o ho n

theorem excl_aligned (hq : q.Prime) (hhq : h ^ q = 1) (ks : List (Ω → G)) :
    ∃ P : Subgroup G, IsPGroup q P ∧ ∀ y ∈ excl h ks, Aligned h ω P y := by
  induction ks using List.reverseRecOn with
  | nil =>
    refine ⟨⊥, IsPGroup.of_bot, fun y hy => ?_⟩
    rw [excl_nil, Set.mem_singleton_iff] at hy
    subst hy
    intro o _ o' _; simp
  | append_singleton ks k ih =>
    obtain ⟨P, hP, hal⟩ := ih
    rw [excl_append]
    exact step_aligned hq hhq _ k P hP hal

/-- **Theorem A.** If an adversary element `h` of prime order `q` moves some switch, a
surjective strategy forces `G` to be a `q`-group. -/
theorem isPGroup_of_strategy (hq : q.Prime) (hhq : h ^ q = 1) (hω : h • ω ≠ ω)
    (ks : List (Ω → G)) (hS : IsSurjectiveStrategy H ks) : IsPGroup q G := by
  classical
  by_contra hG
  simp only [IsPGroup, not_forall] at hG
  obtain ⟨g, hg⟩ := hG
  obtain ⟨P, hP, hal⟩ := excl_aligned (ω := ω) hq hhq ks
  let z : Ω → G := Function.update 1 (h • ω) g
  apply not_strategy_of_not_mem h ks z _ hS
  intro hz
  have := hal z hz ω self_mem_orb (h • ω) (smul_mem_orb self_mem_orb)
  have hz1 : z ω = 1 := by simp [z, Function.update_of_ne hω.symm]
  have hz2 : z (h • ω) = g := by simp [z]
  rw [hz1, hz2, inv_one, one_mul] at this
  obtain ⟨e, he⟩ := hP ⟨g, this⟩
  exact hg ⟨e, by simpa using congrArg Subtype.val he⟩

end Invariant

end SpinningSwitches
