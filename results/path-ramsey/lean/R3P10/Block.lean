import R3P10.Edges

/-! # The lex-leader block: every clause holds when `X ≤lex act g X`

The auxiliary variable of non-skipped position `k` in the block of `g`
starting at `top` is `top + ns g k + 1`; it is set to its meaning
"`X` and `act g X` agree at every position `≤ k`". -/

namespace R3P10

variable {n : ℕ}

/-! ## Clause and literal helpers -/

theorem clauseTrue_nil (A : ℕ → Prop) : ¬ ClauseTrue A [] := by simp [ClauseTrue]

theorem clauseTrue_cons (A : ℕ → Prop) (l : Int) (C : Clause) :
    ClauseTrue A (l :: C) ↔ LitTrue A l ∨ ClauseTrue A C := by
  simp [ClauseTrue]

theorem clauseTrue_append (A : ℕ → Prop) (C D : Clause) :
    ClauseTrue A (C ++ D) ↔ ClauseTrue A C ∨ ClauseTrue A D := by
  simp only [ClauseTrue, List.mem_append]
  constructor
  · rintro ⟨l, hl | hl, h⟩
    · exact Or.inl ⟨l, hl, h⟩
    · exact Or.inr ⟨l, hl, h⟩
  · rintro (⟨l, hl, h⟩ | ⟨l, hl, h⟩)
    · exact ⟨l, Or.inl hl, h⟩
    · exact ⟨l, Or.inr hl, h⟩

theorem mem_sd {x : Int} {l : List Int} : x ∈ sd l ↔ x ∈ l := by
  simp [sd, List.mem_mergeSort, List.mem_dedup]

theorem clauseTrue_sd (A : ℕ → Prop) (l : List Int) : ClauseTrue A (sd l) ↔ ClauseTrue A l := by
  simp [ClauseTrue, mem_sd]

theorem litTrue_nat (A : ℕ → Prop) {m : ℕ} (h : 0 < m) : LitTrue A (m : Int) ↔ A m := by
  simp [LitTrue, h]

theorem litTrue_neg_nat (A : ℕ → Prop) {m : ℕ} (h : 0 < m) : LitTrue A (-(m : Int)) ↔ ¬ A m := by
  have : ¬ (0 < -(m : Int)) := by omega
  simp only [LitTrue, if_neg this, Int.natAbs_neg, Int.natAbs_natCast]

theorem litTrue_lit (A : ℕ → Prop) (k c : ℕ) : LitTrue A (lit k c) ↔ A (var k c) :=
  litTrue_nat A (by simp [var])

theorem litTrue_neg_lit (A : ℕ → Prop) (k c : ℕ) : LitTrue A (-lit k c) ↔ ¬ A (var k c) :=
  litTrue_neg_nat A (by simp [var])

/-! ## Counting non-skipped positions -/

theorem ns_zero (g : Gen n) : ns g 0 = 0 := rfl

theorem ns_succ (g : Gen n) (k : ℕ) : ns g (k + 1) = ns g k + if skip g k then 0 else 1 := by
  unfold ns
  rw [List.range_succ, List.filter_append, List.length_append]
  cases h : skip g k <;> simp [h]

theorem ns_mono (g : Gen n) {a b : ℕ} (h : a ≤ b) : ns g a ≤ ns g b := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [ns_succ]; omega

theorem ns_lt (g : Gen n) {a b : ℕ} (ha : skip g a = false) (h : a < b) : ns g a < ns g b := by
  have h1 : ns g (a + 1) = ns g a + 1 := by rw [ns_succ, ha]; rfl
  have h2 := ns_mono g (show a + 1 ≤ b by omega)
  omega

theorem skip_between (g : Gen n) {a b k : ℕ} (h : ns g a = ns g b) (hak : a ≤ k) (hkb : k < b) :
    skip g k = true := by
  by_contra hs
  have h1 := ns_lt g (by simpa using hs) hkb
  have h2 := ns_mono g hak
  omega

theorem ns_last (g : Gen n) {k j : ℕ} (h : ns g k = j + 1) :
    ∃ k0 < k, skip g k0 = false ∧ ns g k0 = j ∧ ∀ k', k0 < k' → k' < k → skip g k' = true := by
  induction k with
  | zero => simp [ns_zero] at h
  | succ k ih =>
    rw [ns_succ] at h
    cases hs : skip g k
    · refine ⟨k, by omega, hs, by simp [hs] at h; omega, fun k' h1 h2 => by omega⟩
    · simp only [hs, if_true, add_zero] at h
      obtain ⟨k0, hk0, h0, hj, hb⟩ := ih h
      refine ⟨k0, by omega, h0, hj, fun k' h1 h2 => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | h2
      · exact hb k' h1 h2
      · exact h2 ▸ hs

theorem ns_inj (g : Gen n) {a b : ℕ} (ha : skip g a = false) (hb : skip g b = false)
    (h : ns g a = ns g b) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (ns_lt g ha hab).ne
  · exact hab
  · exact absurd h (ns_lt g hb hab).ne'

/-! ## The block lemma -/

/-- The colour vector of `X` as a function on `Fin N`, compared lexicographically. -/
def vecF (X : Col n) : Fin (edges n).length → Fin 3 := fun i => vec X i

theorem block_ok (g : Gen n) (top : ℕ) (A : ℕ → Prop) (X : Col n)
    (hx : ∀ k < (edges n).length, ∀ c : Fin 3, A (var k c) ↔ vec X k = c)
    (haux : ∀ k < (edges n).length, skip g k = false →
      (A (top + ns g k + 1) ↔ ∀ k' ≤ k, vec X k' = vec (act g X) k'))
    (hlex : toLex (vecF X) ≤ toLex (vecF (act g X))) :
    CNFTrue A (blockClauses g top) := by
  intro C hC
  simp only [blockClauses, List.mem_flatMap, List.mem_range] at hC
  obtain ⟨k, hk, hC⟩ := hC
  cases hs : skip g k
  case true => simp [hs] at hC
  simp only [hs, Bool.false_eq_true, if_false] at hC
  -- the meaning of each literal at position k
  have hA : ∀ v : Fin 3, A (var k v) ↔ vec X k = v := hx k hk
  have hB : ∀ v : Fin 3, A (var (src g k) (g.col.symm v)) ↔ vec (act g X) k = v := by
    intro v
    rw [hx _ (src_lt g hk), vec_act g X hk, Equiv.eq_symm_apply]
  set EB := ∀ k' < k, vec X k' = vec (act g X) k' with hEB
  have hne : A (top + ns g k + 1) ↔ EB ∧ vec X k = vec (act g X) k := by
    rw [haux k hk hs]
    constructor
    · intro h; exact ⟨fun k' hk' => h k' hk'.le, h k le_rfl⟩
    · intro h k' hk'
      rcases Nat.lt_or_eq_of_le hk' with h' | h'
      · exact h.1 k' h'
      · exact h' ▸ h.2
  have hpre0 : ns g k = 0 → EB := by
    intro h0 k' hk'
    exact (vec_act_of_skip g X (by omega) (skip_between g (h0.trans (ns_zero g).symm).symm
      (Nat.zero_le _) hk')).symm
  have hpre1 : ∀ j, ns g k = j + 1 → (A (top + (j + 1)) ↔ EB) := by
    intro j hj
    obtain ⟨k0, hk0, hs0, hj0, hb⟩ := ns_last g hj
    rw [← add_assoc, ← hj0, haux k0 (by omega) hs0]
    constructor
    · intro h k' hk'
      by_cases h' : k' ≤ k0
      · exact h k' h'
      · exact (vec_act_of_skip g X (by omega) (hb k' (by omega) hk')).symm
    · intro h k' hk'
      exact h k' (by omega)
  -- the prefix literal
  have hpreC : ∀ rest : Clause,
      ClauseTrue A ((if ns g k = 0 then [] else [-((top + ns g k : ℕ) : Int)]) ++ rest) ↔
        (¬ EB ∨ ClauseTrue A rest) := by
    intro rest
    rw [clauseTrue_append]
    split_ifs with h0
    · simp only [clauseTrue_nil A, false_or]
      have := hpre0 h0
      tauto
    · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero h0
      rw [clauseTrue_cons, litTrue_neg_nat A (by omega), hj, hpre1 j hj]
      simp only [clauseTrue_nil A, or_false]
  have hneL : LitTrue A ((top + ns g k + 1 : ℕ) : Int) ↔ EB ∧ vec X k = vec (act g X) k := by
    rw [litTrue_nat A (by omega), hne]
  have hneN : LitTrue A (-((top + ns g k + 1 : ℕ) : Int)) ↔ ¬ (EB ∧ vec X k = vec (act g X) k) := by
    rw [litTrue_neg_nat A (by omega), hne]
  -- X ≤lex act g X: equal before k forces X_k ≤ (act g X)_k
  have hle : EB → vec X k ≤ vec (act g X) k := fun h =>
    show vecF X ⟨k, hk⟩ ≤ vecF (act g X) ⟨k, hk⟩ from
      Pi.apply_le_of_toLex hlex (fun j hj => h j (Fin.lt_def.1 hj))
  have forbid : ∀ v w : Fin 3, w < v →
      ClauseTrue A (sd ((if ns g k = 0 then [] else [-((top + ns g k : ℕ) : Int)]) ++
        [-lit k v, -lit (src g k) (g.col.symm w)])) := by
    intro v w hwv
    rw [clauseTrue_sd, hpreC, clauseTrue_cons, clauseTrue_cons, litTrue_neg_lit, litTrue_neg_lit,
      hA, hB]
    by_contra hc
    push Not at hc
    have := hle hc.1
    rw [hc.2.1, hc.2.2.1] at this
    exact absurd hwv (not_lt.2 this)
  have eqne : ∀ v : Fin 3,
      ClauseTrue A (sd ((if ns g k = 0 then [] else [-((top + ns g k : ℕ) : Int)]) ++
        [-lit k v, -lit (src g k) (g.col.symm v), ((top + ns g k + 1 : ℕ) : Int)])) := by
    intro v
    rw [clauseTrue_sd, hpreC, clauseTrue_cons, clauseTrue_cons, clauseTrue_cons, litTrue_neg_lit,
      litTrue_neg_lit, hA, hB, hneL]
    by_contra hc
    push Not at hc
    exact hc.2.2.2.1 hc.1 (hc.2.1.trans hc.2.2.1.symm)
  have neeq : ∀ v : Fin 3,
      ClauseTrue A (sd [-((top + ns g k + 1 : ℕ) : Int), -lit k v, lit (src g k) (g.col.symm v)]) := by
    intro v
    rw [clauseTrue_sd, clauseTrue_cons, clauseTrue_cons, clauseTrue_cons, litTrue_neg_lit,
      litTrue_lit, hA, hB, hneN]
    by_contra hc
    push Not at hc
    exact hc.2.2.1 (hc.1.2 ▸ hc.2.1)
  simp only [posClauses, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hC
  rcases hC with (((h | h | h | h | h | h) | h) | (h | h | h))
  · exact h ▸ forbid 1 0 (by decide)
  · exact h ▸ forbid 2 0 (by decide)
  · exact h ▸ forbid 2 1 (by decide)
  · exact h ▸ eqne 0
  · exact h ▸ eqne 1
  · exact h ▸ eqne 2
  · split_ifs at h with h0
    · simp at h
    · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero h0
      simp only [List.mem_singleton] at h
      subst h
      rw [clauseTrue_cons, clauseTrue_cons, hneN, litTrue_nat A (by omega), hj, hpre1 j hj]
      tauto
  · exact h ▸ neeq 0
  · exact h ▸ neeq 1
  · exact h ▸ neeq 2

end R3P10
