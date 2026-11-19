import GCG.Game

namespace GCG

open Finset

/-! ## Auxiliary definitions and lemmas for Bob's potential strategy -/

section Potential

variable {V : Type*} [Fintype V] {k : ℕ}

/-- Hypotheses (1)-(3) of Theorem 1, bundled. -/
structure Hyp (G : SimpleGraph V) (A : Finset V) (cls : V → Option (Fin k))
    (nb : V → Fin k → V) : Prop where
  hA : ∀ a ∈ A, cls a = none
  hU : ∀ w, cls w ≠ none → ∀ v, G.Adj w v → v ∈ A
  hnb : ∀ a ∈ A, ∀ i, G.Adj a (nb a i) ∧ cls (nb a i) = some i ∧
      ∀ w, G.Adj a w → cls w = some i → w = nb a i
  hlin : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → ∀ w w', cls w ≠ none → cls w' ≠ none →
      G.Adj a w → G.Adj a' w → G.Adj a w' → G.Adj a' w' → w = w'

/-- A class vertex `w` is *taken* in the position `c` if it has the colour of its class. -/
def Taken (cls c : V → Option (Fin k)) (w : V) : Prop :=
  cls w ≠ none ∧ c w = cls w

/-- A class vertex `w` is *free* in the position `c` if it is uncoloured and no neighbour
has the colour of its class. -/
def Free (G : SimpleGraph V) (cls c : V → Option (Fin k)) (w : V) : Prop :=
  cls w ≠ none ∧ c w = none ∧ ∀ v, G.Adj w v → c v ≠ cls w

/-- `a` is *alive*: it is uncoloured and none of its designated neighbours is dead. -/
def Alive (G : SimpleGraph V) (cls : V → Option (Fin k)) (nb : V → Fin k → V)
    (c : V → Option (Fin k)) (a : V) : Prop :=
  c a = none ∧ ∀ i, Taken cls c (nb a i) ∨ Free G cls c (nb a i)

open Classical in
/-- `t(a)`: the number of taken designated neighbours of `a`. -/
noncomputable def tk (cls : V → Option (Fin k)) (nb : V → Fin k → V)
    (c : V → Option (Fin k)) (a : V) : ℕ :=
  (univ.filter (fun i : Fin k => Taken cls c (nb a i))).card

open Classical in
/-- The weight of `a`: `2 ^ t(a)` if `a` is alive and `0` otherwise. -/
noncomputable def wt (G : SimpleGraph V) (cls : V → Option (Fin k)) (nb : V → Fin k → V)
    (c : V → Option (Fin k)) (a : V) : ℕ :=
  if Alive G cls nb c a then 2 ^ tk cls nb c a else 0

/-- The potential `Φ(c)`. -/
noncomputable def Phi (G : SimpleGraph V) (A : Finset V) (cls : V → Option (Fin k))
    (nb : V → Fin k → V) (c : V → Option (Fin k)) : ℕ :=
  ∑ a ∈ A, wt G cls nb c a

open Classical in
/-- The local potential `Φ_y(c)`. -/
noncomputable def PhiAt (G : SimpleGraph V) (A : Finset V) (cls : V → Option (Fin k))
    (nb : V → Fin k → V) (c : V → Option (Fin k)) (y : V) : ℕ :=
  ∑ a ∈ A, if G.Adj a y then wt G cls nb c a else 0

open Classical in
/-- `F(c)`: the number of free vertices. -/
noncomputable def numFree (G : SimpleGraph V) (cls c : V → Option (Fin k)) : ℕ :=
  (univ.filter (fun w : V => Free G cls c w)).card

/-- The invariant for positions with Bob to move. -/
def IB (G : SimpleGraph V) (A : Finset V) (cls : V → Option (Fin k))
    (nb : V → Fin k → V) (c : V → Option (Fin k)) : Prop :=
  2 ^ k * numFree G cls c < 8 * Phi G A cls nb c

/-- The invariant for positions with Alice to move. -/
def IA (G : SimpleGraph V) (A : Finset V) (cls : V → Option (Fin k))
    (nb : V → Fin k → V) (c : V → Option (Fin k)) : Prop :=
  2 ^ k * numFree G cls c < 8 * Phi G A cls nb c ∧
    ∀ y, Free G cls c y →
      2 ^ k * numFree G cls c + 8 * PhiAt G A cls nb c y < 8 * Phi G A cls nb c + 2 ^ k

variable {G : SimpleGraph V} {A : Finset V} {cls : V → Option (Fin k)} {nb : V → Fin k → V}

theorem exists_of_ne_none {α : Type*} {o : Option α} (h : o ≠ none) : ∃ x, o = some x := by
  cases o with
  | none => exact absurd rfl h
  | some x => exact ⟨x, rfl⟩

/-! ### The stuck lemma -/

omit [Fintype V] in
theorem stuck_move {c c' : V → Option (Fin k)} (hm : Move G c c') {a : V} (ha : c a = none)
    (hall : ∀ i : Fin k, ∃ w, G.Adj a w ∧ c w = some i) :
    c' a = none ∧ ∀ i : Fin k, ∃ w, G.Adj a w ∧ c' w = some i := by
  obtain ⟨v, j, hcv, hleg, hc'v, hoth⟩ := hm
  have hav : a ≠ v := by
    intro h
    obtain ⟨w, hw1, hw2⟩ := hall j
    rw [h] at hw1
    exact hleg w hw1 hw2
  refine ⟨by rw [hoth a hav]; exact ha, fun i => ?_⟩
  obtain ⟨w, hw1, hw2⟩ := hall i
  have hwv : w ≠ v := by
    intro h
    rw [h, hcv] at hw2
    cases hw2
  exact ⟨w, hw1, by rw [hoth w hwv]; exact hw2⟩

omit [Fintype V] in
/-- If an uncoloured vertex sees all `k` colours, Alice does not win. -/
theorem stuck {b : Bool} {c : V → Option (Fin k)} (h : AliceWins G k b c) :
    ∀ a, c a = none → (∀ i : Fin k, ∃ w, G.Adj a w ∧ c w = some i) → False := by
  induction h with
  | full b c hfull => intro a ha _; exact hfull a ha
  | alice c c' hm _ ih =>
    intro a ha hall
    obtain ⟨h1, h2⟩ := stuck_move hm ha hall
    exact ih a h1 h2
  | bob c hex _ ih =>
    intro a ha hall
    obtain ⟨c', hm⟩ := hex
    obtain ⟨h1, h2⟩ := stuck_move hm ha hall
    exact ih c' hm a h1 h2

/-! ### How one move changes statuses -/

omit [Fintype V] in
theorem taken_mono {c c' : V → Option (Fin k)} {v : V} (hcv : c v = none)
    (hoth : ∀ u, u ≠ v → c' u = c u) {w : V} (h : Taken cls c w) : Taken cls c' w := by
  obtain ⟨h1, h2⟩ := h
  have hwv : w ≠ v := by
    intro h
    rw [h] at h1 h2
    rw [hcv] at h2
    exact h1 h2.symm
  exact ⟨h1, by rw [hoth w hwv, h2]⟩

omit [Fintype V] in
theorem free_anti {c c' : V → Option (Fin k)} {v : V} {j : Fin k} (hcv : c v = none)
    (hc'v : c' v = some j) (hoth : ∀ u, u ≠ v → c' u = c u) {w : V}
    (h : Free G cls c' w) : Free G cls c w := by
  obtain ⟨h1, h2, h3⟩ := h
  have hwv : w ≠ v := by
    intro h
    rw [h, hc'v] at h2
    cases h2
  refine ⟨h1, by rw [← hoth w hwv, h2], fun u hu => ?_⟩
  by_cases huv : u = v
  · rw [huv, hcv]
    exact fun h => h1 h.symm
  · rw [← hoth u huv]
    exact h3 u hu

omit [Fintype V] in
theorem free_change {c c' : V → Option (Fin k)} {v : V} {j : Fin k}
    (hc'v : c' v = some j) (hoth : ∀ u, u ≠ v → c' u = c u) {w : V}
    (h : Free G cls c w) :
    Free G cls c' w ∨ w = v ∨ (G.Adj w v ∧ cls w = some j) := by
  obtain ⟨h1, h2, h3⟩ := h
  by_cases hwv : w = v
  · exact Or.inr (Or.inl hwv)
  by_cases hadj : G.Adj w v ∧ cls w = some j
  · exact Or.inr (Or.inr hadj)
  refine Or.inl ⟨h1, by rw [hoth w hwv, h2], fun u hu => ?_⟩
  by_cases huv : u = v
  · rw [huv, hc'v]
    intro h
    rw [huv] at hu
    exact hadj ⟨hu, h.symm⟩
  · rw [hoth u huv]
    exact h3 u hu

omit [Fintype V] in
theorem wt_mono {c c' : V → Option (Fin k)} {a : V} (hca : c a = none → c' a = none)
    (hT : ∀ w, Taken cls c w → Taken cls c' w)
    (hF : ∀ i, Free G cls c (nb a i) → Free G cls c' (nb a i) ∨ Taken cls c' (nb a i)) :
    wt G cls nb c a ≤ wt G cls nb c' a := by
  classical
  unfold wt
  by_cases hal : Alive G cls nb c a
  · have hal' : Alive G cls nb c' a :=
      ⟨hca hal.1, fun i => (hal.2 i).elim (fun h => Or.inl (hT _ h)) (fun h => (hF i h).symm)⟩
    rw [ite_eq_left hal, ite_eq_left hal']
    apply Nat.pow_le_pow_right (by norm_num)
    unfold tk
    apply Finset.card_le_card
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    exact hT _ hi
  · rw [ite_eq_right hal]
    exact Nat.zero_le _

theorem numFree_le {c c' : V → Option (Fin k)}
    (hFa : ∀ w, Free G cls c' w → Free G cls c w) : numFree G cls c' ≤ numFree G cls c := by
  classical
  unfold numFree
  apply Finset.card_le_card
  intro w hw
  simp only [mem_filter, mem_univ, true_and] at hw ⊢
  exact hFa w hw

theorem numFree_lt {c c' : V → Option (Fin k)}
    (hFa : ∀ w, Free G cls c' w → Free G cls c w) {y : V} (hy : Free G cls c y)
    (hy' : ¬ Free G cls c' y) : numFree G cls c' + 1 ≤ numFree G cls c := by
  classical
  unfold numFree
  apply Nat.succ_le_of_lt
  apply Finset.card_lt_card
  refine (Finset.ssubset_iff_of_subset ?_).2 ⟨y, ?_, ?_⟩
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    exact hFa w hw
  · simp only [mem_filter, mem_univ, true_and]
    exact hy
  · simp only [mem_filter, mem_univ, true_and]
    exact hy'

omit [Fintype V] in
theorem exists_alive {c : V → Option (Fin k)} (h : 0 < Phi G A cls nb c) :
    ∃ a ∈ A, Alive G cls nb c a := by
  classical
  by_contra hne
  have h0 : Phi G A cls nb c = 0 := by
    unfold Phi
    apply Finset.sum_eq_zero
    intro a ha
    unfold wt
    rw [ite_eq_right (fun hal => hne ⟨a, ha, hal⟩)]
  omega

theorem phi_pos_of_IB {c : V → Option (Fin k)} (h : IB G A cls nb c) :
    0 < Phi G A cls nb c := by
  have h1 : 0 < 8 * Phi G A cls nb c := lt_of_le_of_lt (Nat.zero_le _) h
  omega

/-! ### Alice's move -/

theorem alice_step (H : Hyp G A cls nb) {c c' : V → Option (Fin k)} (hm : Move G c c')
    (hI : IA G A cls nb c) : IB G A cls nb c' := by
  classical
  obtain ⟨v, j, hcv, hleg, hc'v, hoth⟩ := hm
  have hT : ∀ w, Taken cls c w → Taken cls c' w := fun w h => taken_mono hcv hoth h
  have hFa : ∀ w, Free G cls c' w → Free G cls c w := fun w h => free_anti hcv hc'v hoth h
  have hFle : numFree G cls c' ≤ numFree G cls c := numFree_le hFa
  have key : Phi G A cls nb c ≤ Phi G A cls nb c' ∨
      ∃ y, Free G cls c y ∧ Phi G A cls nb c ≤ Phi G A cls nb c' + PhiAt G A cls nb c y ∧
        numFree G cls c' + 1 ≤ numFree G cls c := by
    by_cases hvA : v ∈ A
    · have hclsv : cls v = none := H.hA v hvA
      obtain ⟨hadj, hcy, huniq⟩ := H.hnb v hvA j
      have hFc : ∀ w, Free G cls c w → Free G cls c' w ∨ w = nb v j := by
        intro w hw
        rcases free_change hc'v hoth hw with h | h | ⟨h1, h2⟩
        · exact Or.inl h
        · rw [h] at hw
          exact absurd hclsv hw.1
        · exact Or.inr (huniq w h1.symm h2)
      by_cases hy : Free G cls c (nb v j)
      · right
        refine ⟨nb v j, hy, ?_, ?_⟩
        · unfold Phi PhiAt
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_le_sum
          intro a ha
          by_cases haadj : G.Adj a (nb v j)
          · rw [ite_eq_left haadj]
            exact Nat.le_add_left _ _
          · rw [ite_eq_right haadj, Nat.add_zero]
            have hav : a ≠ v := by
              intro h
              rw [h] at haadj
              exact haadj hadj
            apply wt_mono (fun h => by rw [hoth a hav]; exact h) hT
            intro i hi
            rcases hFc _ hi with h | h
            · exact Or.inl h
            · have := (H.hnb a ha i).1
              rw [h] at this
              exact absurd this haadj
        · apply numFree_lt hFa hy
          intro hf
          exact hf.2.2 v hadj.symm (by rw [hc'v, hcy])
      · left
        apply Finset.sum_le_sum
        intro a ha
        by_cases hav : a = v
        · have hnal : ¬ Alive G cls nb c a := by
            rw [hav]
            intro hal
            rcases hal.2 j with h | h
            · exact hleg (nb v j) hadj (by rw [h.2, hcy])
            · exact hy h
          unfold wt
          rw [ite_eq_right hnal]
          exact Nat.zero_le _
        · apply wt_mono (fun h => by rw [hoth a hav]; exact h) hT
          intro i hi
          rcases hFc _ hi with h | h
          · exact Or.inl h
          · rw [h] at hi
            exact absurd hi hy
    · have hFc : ∀ w, Free G cls c w → Free G cls c' w ∨ w = v := by
        intro w hw
        rcases free_change hc'v hoth hw with h | h | ⟨h1, _⟩
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd (H.hU w hw.1 v h1) hvA
      have hne : ∀ a ∈ A, a ≠ v := by
        intro a ha h
        rw [h] at ha
        exact hvA ha
      by_cases hy : Free G cls c v ∧ cls v ≠ some j
      · right
        refine ⟨v, hy.1, ?_, ?_⟩
        · unfold Phi PhiAt
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_le_sum
          intro a ha
          by_cases haadj : G.Adj a v
          · rw [ite_eq_left haadj]
            exact Nat.le_add_left _ _
          · rw [ite_eq_right haadj, Nat.add_zero]
            apply wt_mono (fun h => by rw [hoth a (hne a ha)]; exact h) hT
            intro i hi
            rcases hFc _ hi with h | h
            · exact Or.inl h
            · have := (H.hnb a ha i).1
              rw [h] at this
              exact absurd this haadj
        · apply numFree_lt hFa hy.1
          intro hf
          have := hf.2.1
          rw [hc'v] at this
          cases this
      · left
        apply Finset.sum_le_sum
        intro a ha
        apply wt_mono (fun h => by rw [hoth a (hne a ha)]; exact h) hT
        intro i hi
        rcases hFc _ hi with h | h
        · exact Or.inl h
        · right
          rw [h] at hi ⊢
          have hcls : cls v = some j := by
            by_contra hne'
            exact hy ⟨hi, hne'⟩
          exact ⟨hi.1, by rw [hc'v, hcls]⟩
  have h0 := hI.1
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  unfold IB
  rcases key with h | ⟨y, hy, h1, h2⟩
  · have h3 := Nat.mul_le_mul_left (2 ^ k) hFle
    omega
  · have h3 : 2 ^ k * numFree G cls c' + 2 ^ k ≤ 2 ^ k * numFree G cls c := by
      have h5 := Nat.mul_le_mul_left (2 ^ k) h2
      rwa [Nat.mul_add, Nat.mul_one] at h5
    have h4 := hI.2 y hy
    omega

/-! ### Bob's move -/

theorem bob_step (H : Hyp G A cls nb) {c : V → Option (Fin k)} (hI : IB G A cls nb c)
    (hex : ∃ x, Free G cls c x) : ∃ c', Move G c c' ∧ IA G A cls nb c' := by
  classical
  have hne : (univ.filter (fun w => Free G cls c w)).Nonempty := by
    obtain ⟨x, hx⟩ := hex
    exact ⟨x, by simp only [mem_filter, mem_univ, true_and]; exact hx⟩
  obtain ⟨x, hxmem, hxmax⟩ :=
    Finset.exists_max_image _ (fun y => PhiAt G A cls nb c y) hne
  have hx : Free G cls c x := by
    simp only [mem_filter, mem_univ, true_and] at hxmem
    exact hxmem
  have hmax : ∀ y, Free G cls c y → PhiAt G A cls nb c y ≤ PhiAt G A cls nb c x := by
    intro y hy
    exact hxmax y (by simp only [mem_filter, mem_univ, true_and]; exact hy)
  obtain ⟨i, hi⟩ := exists_of_ne_none hx.1
  obtain ⟨c', hc'x, hoth⟩ : ∃ c' : V → Option (Fin k), c' x = some i ∧ ∀ u, u ≠ x → c' u = c u :=
    ⟨Function.update c x (some i), Function.update_self _ _ _,
      fun u hu => Function.update_of_ne hu _ _⟩
  have hmove : Move G c c' :=
    ⟨x, i, hx.2.1, fun w hw => by rw [← hi]; exact hx.2.2 w hw, hc'x, hoth⟩
  refine ⟨c', hmove, ?_⟩
  have hxA : x ∉ A := fun h => hx.1 (H.hA x h)
  have hT : ∀ w, Taken cls c w → Taken cls c' w := fun w h => taken_mono hx.2.1 hoth h
  have hT' : ∀ w, w ≠ x → Taken cls c' w → Taken cls c w :=
    fun w hw h => ⟨h.1, by rw [← hoth w hw]; exact h.2⟩
  have hTx : Taken cls c' x := ⟨hx.1, by rw [hc'x, hi]⟩
  have hnTx : ¬ Taken cls c x := fun h => hx.1 (by rw [← h.2, hx.2.1])
  have hFa : ∀ w, Free G cls c' w → Free G cls c w := fun w h => free_anti hx.2.1 hc'x hoth h
  have hFc : ∀ w, w ≠ x → Free G cls c w → Free G cls c' w := by
    intro w hw hf
    rcases free_change hc'x hoth hf with h | h | ⟨h1, _⟩
    · exact h
    · exact absurd h hw
    · exact absurd (H.hU w hf.1 x h1) hxA
  have hnFx : ¬ Free G cls c' x := by
    intro h
    have := h.2.1
    rw [hc'x] at this
    cases this
  have hF : numFree G cls c' + 1 ≤ numFree G cls c := numFree_lt hFa hx hnFx
  have hAl : ∀ a ∈ A, (Alive G cls nb c' a ↔ Alive G cls nb c a) := by
    intro a ha
    have hax : a ≠ x := by
      intro h
      rw [h] at ha
      exact hxA ha
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by rw [← hoth a hax]; exact h1, fun i' => ?_⟩
      by_cases hnx : nb a i' = x
      · right
        rw [hnx]
        exact hx
      · rcases h2 i' with h | h
        · exact Or.inl (hT' _ hnx h)
        · exact Or.inr (hFa _ h)
    · rintro ⟨h1, h2⟩
      refine ⟨by rw [hoth a hax]; exact h1, fun i' => ?_⟩
      by_cases hnx : nb a i' = x
      · left
        rw [hnx]
        exact hTx
      · rcases h2 i' with h | h
        · exact Or.inl (hT _ h)
        · exact Or.inr (hFc _ hnx h)
  have htk0 : ∀ a ∈ A, ¬ G.Adj a x → tk cls nb c' a = tk cls nb c a := by
    intro a ha hadj
    unfold tk
    congr 1
    apply Finset.filter_congr
    intro i' _
    have hnx : nb a i' ≠ x := by
      intro h
      have := (H.hnb a ha i').1
      rw [h] at this
      exact hadj this
    exact ⟨hT' _ hnx, hT _⟩
  have htk1 : ∀ a ∈ A, G.Adj a x → tk cls nb c' a = tk cls nb c a + 1 := by
    intro a ha hadj
    have hxi : x = nb a i := (H.hnb a ha i).2.2 x hadj hi
    unfold tk
    have hins : univ.filter (fun i' => Taken cls c' (nb a i')) =
        insert i (univ.filter (fun i' => Taken cls c (nb a i'))) := by
      ext i'
      simp only [mem_filter, mem_univ, true_and, mem_insert]
      constructor
      · intro h
        by_cases hii : i' = i
        · exact Or.inl hii
        · right
          apply hT' _ _ h
          intro hnx
          have := (H.hnb a ha i').2.1
          rw [hnx, hi] at this
          exact hii (Option.some.inj this).symm
      · rintro (h | h)
        · rw [h, ← hxi]
          exact hTx
        · exact hT _ h
    rw [hins, Finset.card_insert_of_notMem]
    simp only [mem_filter, mem_univ, true_and]
    rw [← hxi]
    exact hnTx
  have hwt : ∀ a ∈ A, wt G cls nb c' a =
      wt G cls nb c a + (if G.Adj a x then wt G cls nb c a else 0) := by
    intro a ha
    by_cases hadj : G.Adj a x
    · rw [ite_eq_left hadj]
      unfold wt
      rw [htk1 a ha hadj]
      by_cases hal : Alive G cls nb c a
      · rw [ite_eq_left hal, ite_eq_left ((hAl a ha).2 hal), pow_succ]
        ring
      · rw [ite_eq_right hal, ite_eq_right (fun h => hal ((hAl a ha).1 h))]
    · rw [ite_eq_right hadj, Nat.add_zero]
      unfold wt
      rw [htk0 a ha hadj]
      by_cases hal : Alive G cls nb c a
      · rw [ite_eq_left hal, ite_eq_left ((hAl a ha).2 hal)]
      · rw [ite_eq_right hal, ite_eq_right (fun h => hal ((hAl a ha).1 h))]
  have hPhi : Phi G A cls nb c' = Phi G A cls nb c + PhiAt G A cls nb c x := by
    unfold Phi PhiAt
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hwt
  have h0 : 2 ^ k * numFree G cls c < 8 * Phi G A cls nb c := hI
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have h3 : 2 ^ k * numFree G cls c' + 2 ^ k ≤ 2 ^ k * numFree G cls c := by
    have h5 := Nat.mul_le_mul_left (2 ^ k) hF
    rwa [Nat.mul_add, Nat.mul_one] at h5
  refine ⟨?_, ?_⟩
  · rw [hPhi]
    omega
  · intro y hy
    have hyx : y ≠ x := by
      intro h
      rw [h] at hy
      exact hnFx hy
    have hyc : Free G cls c y := hFa y hy
    have hyle := hmax y hyc
    have hS : 4 * (∑ a ∈ A, if G.Adj a y then (if G.Adj a x then wt G cls nb c a else 0) else 0)
        ≤ 2 ^ k := by
      by_cases hex2 : ∃ a0 ∈ A, G.Adj a0 y ∧ G.Adj a0 x
      · obtain ⟨a0, ha0, h0y, h0x⟩ := hex2
        have hsingle : (∑ a ∈ A, if G.Adj a y then (if G.Adj a x then wt G cls nb c a else 0)
            else 0) = wt G cls nb c a0 := by
          rw [Finset.sum_eq_single_of_mem a0 ha0]
          · rw [ite_eq_left h0y, ite_eq_left h0x]
          · intro a ha hne'
            by_cases hay : G.Adj a y
            · rw [ite_eq_left hay]
              by_cases hax : G.Adj a x
              · exact absurd (H.hlin a ha a0 ha0 hne' y x hyc.1 hx.1 hay h0y hax h0x) hyx
              · rw [ite_eq_right hax]
            · rw [ite_eq_right hay]
        rw [hsingle]
        unfold wt
        by_cases hal : Alive G cls nb c a0
        · rw [ite_eq_left hal]
          have htk : tk cls nb c a0 + 2 ≤ k := by
            obtain ⟨iy, hiy⟩ := exists_of_ne_none hyc.1
            have hxn : x = nb a0 i := (H.hnb a0 ha0 i).2.2 x h0x hi
            have hyn : y = nb a0 iy := (H.hnb a0 ha0 iy).2.2 y h0y hiy
            have hiiy : i ≠ iy := by
              intro h
              apply hyx
              rw [hyn, hxn, h]
            have hnTy : ¬ Taken cls c y := fun h => hyc.1 (by rw [← h.2, hyc.2.1])
            unfold tk
            have hsub : univ.filter (fun i' => Taken cls c (nb a0 i')) ⊆
                (univ.erase i).erase iy := by
              intro i' hi'
              simp only [mem_filter, mem_univ, true_and] at hi'
              simp only [mem_erase, mem_univ, and_true]
              refine ⟨?_, ?_⟩
              · intro h
                rw [h, ← hyn] at hi'
                exact hnTy hi'
              · intro h
                rw [h, ← hxn] at hi'
                exact hnTx hi'
            have hcard := Finset.card_le_card hsub
            rw [Finset.card_erase_of_mem (by simp only [mem_erase, mem_univ, and_true]; exact hiiy.symm),
              Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, Fintype.card_fin] at hcard
            have hk : 2 ≤ k := by
              have h2 := Finset.card_le_univ ({i, iy} : Finset (Fin k))
              rw [Finset.card_pair hiiy, Fintype.card_fin] at h2
              exact h2
            omega
          calc 4 * 2 ^ tk cls nb c a0 = 2 ^ (tk cls nb c a0 + 2) := by rw [pow_add]; ring
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) htk
        · rw [ite_eq_right hal]
          exact Nat.zero_le _
      · have hzero : (∑ a ∈ A, if G.Adj a y then (if G.Adj a x then wt G cls nb c a else 0)
            else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro a ha
          by_cases hay : G.Adj a y
          · rw [ite_eq_left hay]
            by_cases hax : G.Adj a x
            · exact absurd ⟨a, ha, hay, hax⟩ hex2
            · rw [ite_eq_right hax]
          · rw [ite_eq_right hay]
        rw [hzero]
        exact Nat.zero_le _
    have hPy : PhiAt G A cls nb c' y = PhiAt G A cls nb c y +
        ∑ a ∈ A, if G.Adj a y then (if G.Adj a x then wt G cls nb c a else 0) else 0 := by
      unfold PhiAt
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hay : G.Adj a y
      · simp only [ite_eq_left hay]
        exact hwt a ha
      · simp only [ite_eq_right hay, Nat.add_zero]
    rw [hPhi, hPy]
    omega

/-! ### The induction -/

theorem main_ind (H : Hyp G A cls nb) {b : Bool} {c : V → Option (Fin k)}
    (h : AliceWins G k b c) :
    (b = true → IA G A cls nb c → False) ∧ (b = false → IB G A cls nb c → False) := by
  induction h with
  | full b c hfull =>
    have hno : IB G A cls nb c → False := by
      intro hI
      obtain ⟨a, _, hal⟩ := exists_alive (phi_pos_of_IB hI)
      exact hfull a hal.1
    exact ⟨fun _ hI => hno hI.1, fun _ hI => hno hI⟩
  | alice c c' hm _ ih =>
    exact ⟨fun _ hI => ih.2 rfl (alice_step H hm hI), fun h => Bool.noConfusion h⟩
  | bob c hex hall ih =>
    refine ⟨fun h => Bool.noConfusion h, fun _ hI => ?_⟩
    by_cases hfree : ∃ x, Free G cls c x
    · obtain ⟨c', hm, hIA⟩ := bob_step H hI hfree
      exact (ih c' hm).1 rfl hIA
    · obtain ⟨a, ha, hal⟩ := exists_alive (phi_pos_of_IB hI)
      apply stuck (AliceWins.bob c hex hall) a hal.1
      intro i
      refine ⟨nb a i, (H.hnb a ha i).1, ?_⟩
      rcases hal.2 i with h | h
      · rw [h.2]
        exact (H.hnb a ha i).2.1
      · exact absurd ⟨_, h⟩ hfree

/-! ### The initial position -/

theorem init_IA [DecidableEq V] [DecidableRel G.Adj] (H : Hyp G A cls nb) (D : ℕ)
    (hD : ∀ w, cls w ≠ none → (A.filter (fun a => G.Adj a w)).card ≤ D)
    (hcount : 2 ^ k * (univ.filter (fun w => cls w ≠ none)).card + 8 * D < 8 * A.card) :
    IA G A cls nb (fun _ => none) := by
  classical
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hfree : ∀ w, Free G cls (fun _ => none) w ↔ cls w ≠ none := by
    intro w
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, rfl, fun v _ hv => h hv.symm⟩
  have hF : numFree G cls (fun _ => none) = (univ.filter (fun w => cls w ≠ none)).card := by
    unfold numFree
    congr 1
    apply Finset.filter_congr
    intro w _
    exact hfree w
  have hwt : ∀ a ∈ A, wt G cls nb (fun _ => none) a = 1 := by
    intro a ha
    have hal : Alive G cls nb (fun _ => none) a :=
      ⟨rfl, fun i => Or.inr ((hfree _).2 (by rw [(H.hnb a ha i).2.1]; exact Option.some_ne_none _))⟩
    unfold wt
    rw [ite_eq_left hal]
    have ht : tk cls nb (fun _ => none) a = 0 := by
      unfold tk
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ ht
      exact ht.1 ht.2.symm
    rw [ht, pow_zero]
  have hPhi : Phi G A cls nb (fun _ => none) = A.card := by
    unfold Phi
    rw [Finset.sum_congr rfl hwt]
    simp
  have hPy : ∀ y, PhiAt G A cls nb (fun _ => none) y = (A.filter (fun a => G.Adj a y)).card := by
    intro y
    unfold PhiAt
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro a ha
    rw [hwt a ha]
    congr
  refine ⟨?_, fun y hy => ?_⟩
  · rw [hF, hPhi]
    omega
  · rw [hF, hPhi, hPy]
    have := hD y hy.1
    omega

end Potential

/-- **Bob's potential strategy.** `A` is a set of vertices; `cls w = some i` puts `w` in the
class `U_i` (`i < k`). Every neighbour of a class vertex lies in `A`; every `a ∈ A` has
exactly one neighbour `nb a i` in each class `U_i`; two distinct vertices of `A` have at
most one common neighbour among class vertices; every class vertex has at most `D`
neighbours in `A`; and `2^k * |U| + 8 * D < 8 * |A|`. Then Alice does not win the
`k`-colour game on `G`. -/
theorem bob_wins_of_structure {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (A : Finset V) (cls : V → Option (Fin k)) (nb : V → Fin k → V) (D : ℕ)
    (hA : ∀ a ∈ A, cls a = none)
    (hU : ∀ w, cls w ≠ none → ∀ v, G.Adj w v → v ∈ A)
    (hnb : ∀ a ∈ A, ∀ i, G.Adj a (nb a i) ∧ cls (nb a i) = some i ∧
      ∀ w, G.Adj a w → cls w = some i → w = nb a i)
    (hlin : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → ∀ w w', cls w ≠ none → cls w' ≠ none →
      G.Adj a w → G.Adj a' w → G.Adj a w' → G.Adj a' w' → w = w')
    (hD : ∀ w, cls w ≠ none → (A.filter (fun a => G.Adj a w)).card ≤ D)
    (hcount : 2 ^ k * (univ.filter (fun w => cls w ≠ none)).card + 8 * D < 8 * A.card) :
    ¬ AliceWinsGame G k := by
  intro hw
  have H : Hyp G A cls nb := ⟨hA, hU, hnb, hlin⟩
  exact (main_ind H hw).1 rfl (init_IA H D hD hcount)

end GCG
