import GCG.Game

namespace GCG

open Finset

/-! ### Auxiliary lemmas for the minimum-degree lemma -/

/-- The degree sum inside `S`: twice the number of edges of `G` inside `S`. -/
def dsum {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  ∑ v ∈ S, (S.filter (fun u => G.Adj v u)).card

/-- Deleting `v` from `S` lowers the degree sum by twice the degree of `v` in `S`. -/
lemma dsum_erase {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) (hv : v ∈ S) :
    dsum G (S.erase v) + 2 * (S.filter (fun u => G.Adj v u)).card = dsum G S := by
  unfold dsum
  rw [← Finset.add_sum_erase S _ hv]
  have h1 : ∀ w ∈ S.erase v, (S.filter (fun u => G.Adj w u)).card
      = ((S.erase v).filter (fun u => G.Adj w u)).card + (if G.Adj v w then 1 else 0) := by
    intro w _
    rw [Finset.filter_erase]
    split_ifs with h
    · rw [Finset.card_erase_add_one]
      rw [Finset.mem_filter]
      exact ⟨hv, h.symm⟩
    · rw [Finset.erase_eq_of_notMem]
      · rfl
      · rw [Finset.mem_filter]
        exact fun h' => h h'.2.symm
  have h2 : ∑ w ∈ S.erase v, (if G.Adj v w then 1 else 0)
      = (S.filter (fun u => G.Adj v u)).card := by
    rw [← Finset.card_filter]
    congr 1
    ext u
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨-, h⟩, h'⟩
      exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩
      refine ⟨⟨?_, h⟩, h'⟩
      rintro rfl
      exact G.irrefl h'
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, h2]
  ring

/-- **Minimum degree.** If the degree sum of a finite graph is at least `t * |V|` with
`t > 0` and `V` nonempty, some nonempty vertex set `S` has every vertex of `S` adjacent to
at least `t / 2` vertices of `S` (stated as `t ≤ 2 * ...`). -/
theorem exists_minDegree_subset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ) (ht : 0 < t) [Nonempty V]
    (h : t * Fintype.card V ≤ ∑ v, G.degree v) :
    ∃ S : Finset V, S.Nonempty ∧ ∀ v ∈ S, t ≤ 2 * (S.filter (fun u => G.Adj v u)).card := by
  have hdsum : dsum G univ = ∑ v, G.degree v := by
    unfold dsum
    apply Finset.sum_congr rfl
    intro v _
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1
    ext u
    simp
  have key : ∀ n, ∀ S : Finset V, S.card = n → S.Nonempty → t * S.card ≤ dsum G S →
      ∃ T : Finset V, T.Nonempty ∧
        ∀ v ∈ T, t ≤ 2 * (T.filter (fun u => G.Adj v u)).card := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro S hn hne hS
      by_cases hgood : ∀ v ∈ S, t ≤ 2 * (S.filter (fun u => G.Adj v u)).card
      · exact ⟨S, hne, hgood⟩
      · push Not at hgood
        obtain ⟨v, hv, hlt⟩ := hgood
        have he := dsum_erase G S v hv
        have hc : (S.erase v).card + 1 = S.card := Finset.card_erase_add_one hv
        have hmul : t * S.card = t * (S.erase v).card + t := by
          rw [← hc]
          ring
        have hS' : t * (S.erase v).card ≤ dsum G (S.erase v) := by omega
        have hne' : (S.erase v).Nonempty := by
          by_contra hemp
          rw [Finset.not_nonempty_iff_eq_empty] at hemp
          have h0 : dsum G (S.erase v) = 0 := by
            rw [hemp]
            simp [dsum]
          have hc0 : (S.erase v).card = 0 := by
            rw [hemp]
            rfl
          rw [hc0] at hmul
          have := ht
          omega
        exact ih (S.erase v).card (by omega) (S.erase v) rfl hne' hS'
  exact key _ univ rfl Finset.univ_nonempty (by rw [hdsum, Finset.card_univ]; exact h)

/-! ### Auxiliary lemmas for the extraction lemma -/

/-- Bernoulli-type inequality: `2 * m ^ (m + 1) ≤ (m + 1) ^ (m + 1)`. -/
lemma two_mul_pow_le (m : ℕ) : 2 * m ^ (m + 1) ≤ (m + 1) ^ (m + 1) := by
  have key : ∀ k : ℕ, m ^ (k + 1) + (k + 1) * m ^ k ≤ (m + 1) ^ (k + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc m ^ (k + 1 + 1) + (k + 1 + 1) * m ^ (k + 1)
          ≤ m ^ (k + 1 + 1) + (k + 1 + 1) * m ^ (k + 1) + (k + 1) * m ^ k :=
            Nat.le_add_right _ _
        _ = (m + 1) * (m ^ (k + 1) + (k + 1) * m ^ k) := by ring
        _ ≤ (m + 1) * (m + 1) ^ (k + 1) := Nat.mul_le_mul_left _ ih
        _ = (m + 1) ^ (k + 1 + 1) := by ring
  have h1 := key m
  have h2 : m ^ (m + 1) ≤ (m + 1) * m ^ m := by
    rw [pow_succ, mul_comm]
    exact Nat.mul_le_mul_right _ (Nat.le_succ m)
  omega

/-- The number of elements of `Fin N` with value below `K ≤ N` is `K`. -/
lemma card_filter_val_lt {N K : ℕ} (h : K ≤ N) :
    (univ.filter (fun j : Fin N => j.val < K)).card = K := by
  have himg : (univ.filter (fun j : Fin N => j.val < K))
      = (univ : Finset (Fin K)).image (Fin.castLE h) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hj
      exact ⟨⟨j.val, hj⟩, by ext; rfl⟩
    · rintro ⟨i, rfl⟩
      exact i.isLt
  rw [himg, Finset.card_image_of_injective _ (Fin.castLE_injective h), card_univ,
    Fintype.card_fin]

/-- Counting labellings `V → Fin N` whose values on `D` are constrained by `P`. -/
lemma card_constrained {V : Type*} [Fintype V] [DecidableEq V] (N : ℕ) (D : Finset V)
    (P : Fin N → Prop) [DecidablePred P] :
    (univ.filter (fun ℓ : V → Fin N => ∀ u ∈ D, P (ℓ u))).card * N ^ D.card
      = (univ.filter P).card ^ D.card * N ^ Fintype.card V := by
  have h1 : (univ.filter (fun ℓ : V → Fin N => ∀ u ∈ D, P (ℓ u)))
      = Fintype.piFinset (fun u => if u ∈ D then univ.filter P else univ) := by
    ext ℓ
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h u
      split_ifs with hu
      · simp [h u hu]
      · simp
    · intro h u hu
      have := h u
      rw [ite_eq_left hu] at this
      simpa using this
  have h2 : ∀ u, (if u ∈ D then univ.filter P else (univ : Finset (Fin N))).card
      = if u ∈ D then (univ.filter P).card else N := by
    intro u
    split_ifs <;> simp
  have h3 : (univ.filter (fun u : V => u ∈ D)) = D := by
    ext u
    simp
  have h4 : (univ.filter (fun u : V => ¬ u ∈ D)).card + D.card = Fintype.card V := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset V))
      (fun u : V => u ∈ D)
    rw [h3, card_univ] at this
    omega
  rw [h1, Fintype.card_piFinset]
  simp_rw [h2]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, h3, ← h4, pow_add]
  ring

/-- Swapping the order of summation in a count of incidences. -/
lemma sum_card_filter_comm {α β : Type*} [Fintype α] (S : Finset β) (r : α → β → Prop)
    [∀ a b, Decidable (r a b)] :
    ∑ a : α, (S.filter (fun b => r a b)).card
      = ∑ b ∈ S, (univ.filter (fun a => r a b)).card := by
  simp_rw [Finset.card_filter]
  exact Finset.sum_comm

/-- The count for one vertex `x`: among the labellings `V → Fin N`, those putting `x` in
the set `A` outnumber `M` times those putting `x` in a class. -/
lemma extract_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (K M N : ℕ) (hK : 0 < K)
    (hN : N = 2 * (M + 1) * K) (S : Finset V) (x : V)
    (hdeg : N * (K + 1) ≤ (S.filter (fun u => G.Adj x u)).card) :
    M * (univ.filter (fun ℓ : V → Fin N => (ℓ x).val < K)).card
      < (univ.filter (fun ℓ : V → Fin N => K ≤ (ℓ x).val ∧
          ∀ i : Fin K, ∃ u ∈ S, G.Adj x u ∧ (ℓ u).val = i.val)).card := by
  have hMK : 1 ≤ (M + 1) * K := Nat.mul_pos (Nat.succ_pos M) hK
  have hN2 : 2 ≤ N := by
    rw [hN, mul_assoc]
    omega
  have hKN : K ≤ N := by
    rw [hN]
    calc K = 1 * K := (one_mul K).symm
      _ ≤ 2 * (M + 1) * K := Nat.mul_le_mul_right K (by omega)
  have hTpos : 0 < N ^ Fintype.card V := Nat.pow_pos (by omega)
  -- (1) the labellings with `x` in a class
  have hu : (univ.filter (fun ℓ : V → Fin N => (ℓ x).val < K)).card * N
      = K * N ^ Fintype.card V := by
    have h := card_constrained (V := V) N {x} (fun j : Fin N => j.val < K)
    simp only [Finset.mem_singleton, forall_eq, Finset.card_singleton, pow_one] at h
    rw [h, card_filter_val_lt hKN]
  -- (2) the labellings in which no neighbour of `x` in `S` has label `i`
  obtain ⟨D, hDsub, hDcard⟩ := Finset.exists_subset_card_eq hdeg
  have hpow : 2 ^ (K + 1) * (N - 1) ^ (N * (K + 1)) ≤ N ^ (N * (K + 1)) := by
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_mul, pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (two_mul_pow_le m) _
  have hb : ∀ i : Fin N,
      2 ^ (K + 1) * (univ.filter (fun ℓ : V → Fin N => ∀ u ∈ S, G.Adj x u → ℓ u ≠ i)).card
        ≤ N ^ Fintype.card V := by
    intro i
    have h := card_constrained (V := V) N D (fun j : Fin N => j ≠ i)
    have hc : (univ.filter (fun j : Fin N => j ≠ i)).card = N - 1 := by
      rw [Finset.filter_ne' univ i, Finset.card_erase_of_mem (mem_univ i), card_univ,
        Fintype.card_fin]
    rw [hDcard, hc] at h
    have hle : (univ.filter (fun ℓ : V → Fin N => ∀ u ∈ S, G.Adj x u → ℓ u ≠ i)).card
        ≤ (univ.filter (fun ℓ : V → Fin N => ∀ u ∈ D, ℓ u ≠ i)).card := by
      apply Finset.card_le_card
      intro ℓ
      simp only [mem_filter, mem_univ, true_and]
      intro hℓ u hu
      have hmem := hDsub hu
      rw [mem_filter] at hmem
      exact hℓ u hmem.1 hmem.2
    have hpos : 0 < (N - 1) ^ (N * (K + 1)) := Nat.pow_pos (by omega)
    apply Nat.le_of_mul_le_mul_right _ hpos
    calc 2 ^ (K + 1) * (univ.filter (fun ℓ : V → Fin N => ∀ u ∈ S, G.Adj x u → ℓ u ≠ i)).card
          * (N - 1) ^ (N * (K + 1))
        = (univ.filter (fun ℓ : V → Fin N => ∀ u ∈ S, G.Adj x u → ℓ u ≠ i)).card
          * (2 ^ (K + 1) * (N - 1) ^ (N * (K + 1))) := by ring
      _ ≤ (univ.filter (fun ℓ : V → Fin N => ∀ u ∈ D, ℓ u ≠ i)).card
          * N ^ (N * (K + 1)) := Nat.mul_le_mul hle hpow
      _ = (N - 1) ^ (N * (K + 1)) * N ^ Fintype.card V := h
      _ = N ^ Fintype.card V * (N - 1) ^ (N * (K + 1)) := by ring
  -- (3) union bound: every labelling is in one of the three kinds of sets
  have hcover : N ^ Fintype.card V
      ≤ (univ.filter (fun ℓ : V → Fin N => K ≤ (ℓ x).val ∧
          ∀ i : Fin K, ∃ u ∈ S, G.Adj x u ∧ (ℓ u).val = i.val)).card
        + (univ.filter (fun ℓ : V → Fin N => (ℓ x).val < K)).card
        + ∑ i : Fin K, (univ.filter (fun ℓ : V → Fin N =>
            ∀ u ∈ S, G.Adj x u → ℓ u ≠ Fin.castLE hKN i)).card := by
    have hsub : (univ : Finset (V → Fin N))
        ⊆ (univ.filter (fun ℓ : V → Fin N => K ≤ (ℓ x).val ∧
            ∀ i : Fin K, ∃ u ∈ S, G.Adj x u ∧ (ℓ u).val = i.val))
          ∪ (univ.filter (fun ℓ : V → Fin N => (ℓ x).val < K))
          ∪ (univ : Finset (Fin K)).biUnion (fun i => univ.filter (fun ℓ : V → Fin N =>
            ∀ u ∈ S, G.Adj x u → ℓ u ≠ Fin.castLE hKN i)) := by
      intro ℓ _
      simp only [mem_union, mem_filter, mem_univ, true_and, mem_biUnion]
      by_cases h1 : (ℓ x).val < K
      · exact Or.inl (Or.inr h1)
      · by_cases h2 : ∀ i : Fin K, ∃ u ∈ S, G.Adj x u ∧ (ℓ u).val = i.val
        · exact Or.inl (Or.inl ⟨by omega, h2⟩)
        · push Not at h2
          obtain ⟨i, hi⟩ := h2
          refine Or.inr ⟨i, fun u hu hadj heq => hi u hu hadj ?_⟩
          rw [heq]
          rfl
    have hcard := Finset.card_le_card hsub
    rw [card_univ, Fintype.card_fun, Fintype.card_fin] at hcard
    refine hcard.trans ((Finset.card_union_le _ _).trans ?_)
    exact Nat.add_le_add (Finset.card_union_le _ _) Finset.card_biUnion_le
  -- arithmetic
  have hsumb : 2 ^ (K + 1) * ∑ i : Fin K, (univ.filter (fun ℓ : V → Fin N =>
      ∀ u ∈ S, G.Adj x u → ℓ u ≠ Fin.castLE hKN i)).card ≤ K * N ^ Fintype.card V := by
    rw [Finset.mul_sum]
    calc ∑ i : Fin K, 2 ^ (K + 1) * (univ.filter (fun ℓ : V → Fin N =>
          ∀ u ∈ S, G.Adj x u → ℓ u ≠ Fin.castLE hKN i)).card
        ≤ ∑ _i : Fin K, N ^ Fintype.card V := Finset.sum_le_sum (fun i _ => hb _)
      _ = K * N ^ Fintype.card V := by
        rw [Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  have hu2 : 2 * (M + 1) * (univ.filter (fun ℓ : V → Fin N => (ℓ x).val < K)).card
      = N ^ Fintype.card V := by
    have hu' : (univ.filter (fun ℓ : V → Fin N => (ℓ x).val < K)).card * (2 * (M + 1) * K)
        = K * N ^ Fintype.card V := by
      rw [← hN]
      exact hu
    apply Nat.eq_of_mul_eq_mul_right hK
    rw [mul_comm (N ^ Fintype.card V) K, ← hu']
    ring
  have hB2 : 2 * ∑ i : Fin K, (univ.filter (fun ℓ : V → Fin N =>
      ∀ u ∈ S, G.Adj x u → ℓ u ≠ Fin.castLE hKN i)).card < N ^ Fintype.card V := by
    have hK2 : K < 2 ^ K := Nat.lt_two_pow_self
    have h3 : K * N ^ Fintype.card V < 2 ^ K * N ^ Fintype.card V :=
      Nat.mul_lt_mul_of_pos_right hK2 hTpos
    apply Nat.lt_of_mul_lt_mul_left (a := 2 ^ K)
    calc 2 ^ K * (2 * ∑ i : Fin K, (univ.filter (fun ℓ : V → Fin N =>
          ∀ u ∈ S, G.Adj x u → ℓ u ≠ Fin.castLE hKN i)).card)
        = 2 ^ (K + 1) * ∑ i : Fin K, (univ.filter (fun ℓ : V → Fin N =>
          ∀ u ∈ S, G.Adj x u → ℓ u ≠ Fin.castLE hKN i)).card := by ring
      _ ≤ K * N ^ Fintype.card V := hsumb
      _ < 2 ^ K * N ^ Fintype.card V := h3
  have hexp : 2 * (M + 1) * (univ.filter (fun ℓ : V → Fin N => (ℓ x).val < K)).card
      = 2 * (M * (univ.filter (fun ℓ : V → Fin N => (ℓ x).val < K)).card)
        + 2 * (univ.filter (fun ℓ : V → Fin N => (ℓ x).val < K)).card := by ring
  omega

/-- **Extraction by counting labellings.** If every vertex of a nonempty set `S` has at
least `2 * (M + 1) * K * (K + 1)` neighbours in `S`, there are a set `A ⊆ S`, classes
`cls : V → Option (Fin K)` and, for each `a ∈ A` and each class `i`, a neighbour `nb a i`
of `a` in class `i`, with `A` disjoint from the classes and
`M * (number of class vertices) < |A|`. -/
theorem extract {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (K M : ℕ) (S : Finset V) (hS : S.Nonempty)
    (hdeg : ∀ v ∈ S, 2 * (M + 1) * K * (K + 1) ≤ (S.filter (fun u => G.Adj v u)).card) :
    ∃ (A : Finset V) (cls : V → Option (Fin K)) (nb : V → Fin K → V),
      A ⊆ S ∧ (∀ w, cls w ≠ none → w ∈ S) ∧
      (∀ a ∈ A, cls a = none) ∧
      (∀ a ∈ A, ∀ i, G.Adj a (nb a i) ∧ cls (nb a i) = some i) ∧
      M * (univ.filter (fun w => cls w ≠ none)).card < A.card := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    refine ⟨S, fun _ => none, fun a _ => a, subset_rfl, fun w hw => absurd rfl hw,
      fun _ _ => rfl, fun _ _ i => i.elim0, ?_⟩
    simpa using hS.card_pos
  · obtain ⟨N, hN⟩ : ∃ N, N = 2 * (M + 1) * K := ⟨_, rfl⟩
    rw [← hN] at hdeg
    -- double counting over all labellings `V → Fin N`
    have hsum : ∑ ℓ : V → Fin N, M * (S.filter (fun w => (ℓ w).val < K)).card
        < ∑ ℓ : V → Fin N, (S.filter (fun x => K ≤ (ℓ x).val ∧
            ∀ i : Fin K, ∃ u ∈ S, G.Adj x u ∧ (ℓ u).val = i.val)).card := by
      rw [← Finset.mul_sum,
        sum_card_filter_comm S (fun (ℓ : V → Fin N) w => (ℓ w).val < K),
        sum_card_filter_comm S (fun (ℓ : V → Fin N) x => K ≤ (ℓ x).val ∧
            ∀ i : Fin K, ∃ u ∈ S, G.Adj x u ∧ (ℓ u).val = i.val),
        Finset.mul_sum]
      exact Finset.sum_lt_sum_of_nonempty hS
        (fun x hx => extract_count G K M N hK hN S x (hdeg x hx))
    obtain ⟨ℓ, -, hℓ⟩ := Finset.exists_lt_of_sum_lt hsum
    obtain ⟨cls, hcls⟩ : ∃ cls : V → Option (Fin K), ∀ w, cls w =
        if h : w ∈ S ∧ (ℓ w).val < K then some ⟨(ℓ w).val, h.2⟩ else none :=
      ⟨_, fun _ => rfl⟩
    obtain ⟨nb, hnb⟩ : ∃ nb : V → Fin K → V, ∀ a i, nb a i =
        if h : ∃ u ∈ S, G.Adj a u ∧ (ℓ u).val = i.val then h.choose else a :=
      ⟨_, fun _ _ => rfl⟩
    refine ⟨S.filter (fun x => K ≤ (ℓ x).val ∧
        ∀ i : Fin K, ∃ u ∈ S, G.Adj x u ∧ (ℓ u).val = i.val), cls, nb,
      Finset.filter_subset _ _, ?_, ?_, ?_, ?_⟩
    · intro w hw
      by_contra hwS
      exact hw (by rw [hcls, dite_eq_right (fun h => hwS h.1)])
    · intro a ha
      rw [Finset.mem_filter] at ha
      rw [hcls, dite_eq_right (fun h => absurd h.2 (by omega))]
    · intro a ha i
      rw [Finset.mem_filter] at ha
      have hex := ha.2.2 i
      obtain ⟨h1, h2, h3⟩ := hex.choose_spec
      rw [hnb, dite_eq_left hex]
      refine ⟨h2, ?_⟩
      rw [hcls, dite_eq_left ⟨h1, by omega⟩]
      exact congrArg some (Fin.ext h3)
    · have hU : (univ.filter (fun w => cls w ≠ none)) = S.filter (fun w => (ℓ w).val < K) := by
        ext w
        simp only [mem_filter, mem_univ, true_and]
        constructor
        · intro h
          by_contra hc
          exact h (by rw [hcls, dite_eq_right hc])
        · intro h
          rw [hcls, dite_eq_left h]
          exact Option.some_ne_none _
      rw [hU]
      exact hℓ

end GCG
