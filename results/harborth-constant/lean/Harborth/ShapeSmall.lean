import Harborth.ShapeDefs

/-!
# Shape Lemma for `p = 11` and `p = 13` by a kernel computation

A profile on `n` classes is sorted (`Tuple.sort`) into an ascending list of length `n` with
sum `2n - 1`. `gen n 0 (2n - 1)` enumerates all such lists (`mem_gen`). For every list
satisfying the hypotheses, `good` checks that the list is exceptional or that one of the
candidate depth lists (rule B, rule H(ρ) for `2 ≤ ρ < n`, a few explicit lists) passes `wcheck`, the
list form of the SLC hypotheses. The two checks run in the kernel (`decide +kernel`).
-/

namespace Harborth.ShapeAux

open Finset

/-! ### Enumeration of ascending lists -/

/-- All ascending lists of length `k` with entries `≥ lo` and sum `S`. -/
def gen : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, _, S => if S = 0 then [[]] else []
  | k + 1, lo, S => (List.range' lo (S / (k + 1) + 1 - lo)).flatMap
      (fun x => (gen k x (S - x)).map (x :: ·))

theorem length_mul_le_sum (x : ℕ) : ∀ l : List ℕ, (∀ y ∈ l, x ≤ y) → l.length * x ≤ l.sum
  | [], _ => by simp
  | a :: l, h => by
    have h1 := length_mul_le_sum x l (fun y hy => h y (by simp [hy]))
    have ha := h a (by simp)
    simp only [List.length_cons, List.sum_cons]
    nlinarith

theorem mem_gen : ∀ (k lo S : ℕ) (l : List ℕ), l.length = k → l.Pairwise (· ≤ ·) →
    (∀ y ∈ l, lo ≤ y) → l.sum = S → l ∈ gen k lo S
  | 0, lo, S, l, hl, _, _, hs => by
    rw [List.length_eq_zero_iff] at hl
    subst hl
    simp only [List.sum_nil] at hs
    subst hs
    simp [gen]
  | k + 1, lo, S, l, hl, hp, hlo, hs => by
    obtain ⟨x, l', rfl⟩ : ∃ x l', l = x :: l' := by
      cases l with
      | nil => simp at hl
      | cons x l' => exact ⟨x, l', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [List.pairwise_cons] at hp
    have hx : lo ≤ x := hlo x (by simp)
    simp only [List.sum_cons] at hs
    have hb := length_mul_le_sum x l' hp.1
    rw [hl] at hb
    have hxS : x ≤ S / (k + 1) := (Nat.le_div_iff_mul_le (by omega)).2 (by nlinarith)
    simp only [gen, List.mem_flatMap, List.mem_range'_1, List.mem_map]
    exact ⟨x, ⟨hx, by omega⟩, l', mem_gen k x (S - x) l' hl hp.2 hp.1 (by omega), rfl⟩

/-! ### The list form of the SLC hypotheses -/

/-- Pointwise `r ≤ v` and `r ≡ v (mod 2)`, with equal lengths. -/
def pw : List ℕ → List ℕ → Bool
  | [], [] => true
  | a :: as, b :: bs => decide (b ≤ a) && decide (b % 2 = a % 2) && pw as bs
  | _, _ => false

/-- `(x - 2)²` in `ℕ`. -/
def sqd (x : ℕ) : ℕ := if 2 ≤ x then (x - 2) ^ 2 else (2 - x) ^ 2

/-- Number of entries `≥ j`. -/
def cnt (r : List ℕ) (j : ℕ) : ℕ := (r.map (fun x => if j ≤ x then 1 else 0)).sum

/-- `∑_{i < m} ⌊cnt(i+1)²/4⌋`. -/
def spreadR (r : List ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => spreadR r i + cnt r (i + 1) ^ 2 / 4

/-- The SLC hypotheses for the profile list `l` and depth list `r` on `n` classes. -/
def wcheck (n : ℕ) (l r : List ℕ) : Bool :=
  pw l r && decide ((r.map (· ^ 2)).sum ≤ (l.map sqd).sum) && decide (n - 1 ≤ spreadR r n)

/-- The ascending list is `0, …, 0, c, n - c, n - 1` with `1 ≤ c ≤ 3`. -/
def excB (n : ℕ) (l : List ℕ) : Bool :=
  decide (l.getD (n - 1) 0 = n - 1) && decide (l.getD (n - 2) 0 + l.getD (n - 3) 0 = n) &&
    decide (1 ≤ l.getD (n - 3) 0) && decide (l.getD (n - 3) 0 ≤ 3) &&
    (List.range (n - 3)).all (fun i => decide (l.getD i 0 = 0))

/-- The hypotheses of the Shape Lemma (besides the sum). -/
def hypB (n : ℕ) (l : List ℕ) : Bool :=
  l.all (fun x => decide (x ≤ n - 1)) &&
    decide (2 * n - 4 ≤ (l.map (fun x => x * (x - 1) / 2)).sum)

/-- Rule B on a list: the first `k` classes of size 2 get depth 2. -/
def bassign : ℕ → List ℕ → List ℕ
  | _, [] => []
  | k, x :: xs =>
    if x = 2 then (if 0 < k then 2 :: bassign (k - 1) xs else 0 :: bassign k xs)
    else bval x :: bassign k xs

/-- Rule B with `k = min(n₂, n₀ + E)`. -/
def blist (l : List ℕ) : List ℕ :=
  bassign (min (l.count 2) (((l.filter (· ≠ 2)).map (fun x => sqd x - bval x ^ 2)).sum / 4)) l

/-- Candidate depth lists: rule B, rule H(ρ) for `2 ≤ ρ < n`, and the explicit lists `sp`. -/
def cands (n : ℕ) (sp : List (List ℕ)) (l : List ℕ) : List (List ℕ) :=
  blist l :: ((List.range' 2 (n - 2)).map (fun ρ => l.map (hcap ρ)) ++ sp)

/-- The check for one ascending list. -/
def good (n : ℕ) (sp : List (List ℕ)) (l : List ℕ) : Bool :=
  !hypB n l || excB n l || (cands n sp l).any (wcheck n l)

/-! ### Soundness -/

theorem pw_spec : ∀ (l r : List ℕ), pw l r = true → l.length = r.length ∧
    ∀ i (h1 : i < l.length) (h2 : i < r.length), r[i] ≤ l[i] ∧ r[i] % 2 = l[i] % 2
  | [], [], _ => by simp
  | [], _ :: _, h => by simp [pw] at h
  | _ :: _, [], h => by simp [pw] at h
  | a :: as, b :: bs, h => by
    simp only [pw, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨hl, hi⟩ := pw_spec as bs h3
    refine ⟨by simp [hl], fun i hi1 hi2 => ?_⟩
    cases i with
    | zero => simpa using ⟨h1, h2⟩
    | succ i => simpa using hi i (by simpa using hi1) (by simpa using hi2)

theorem ofFn_getD {n : ℕ} (u : Fin n → ℕ) (i : Fin n) : (List.ofFn u).getD i 0 = u i := by
  simp

theorem sum_map_ofFn {M : Type*} [AddCommMonoid M] {n : ℕ} (u : Fin n → ℕ) (f : ℕ → M) :
    ((List.ofFn u).map f).sum = ∑ i, f (u i) := by
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

theorem cnt_ofFn {n : ℕ} (r : Fin n → ℕ) (j : ℕ) :
    cnt (List.ofFn r) j = (univ.filter (fun i => j ≤ r i)).card := by
  unfold cnt
  rw [sum_map_ofFn, card_filter]

theorem spreadR_ofFn {n : ℕ} (r : Fin n → ℕ) (m : ℕ) :
    spreadR (List.ofFn r) m = ∑ i ∈ range m, (univ.filter (fun g => i + 1 ≤ r g)).card ^ 2 / 4 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [spreadR, ih, cnt_ofFn, sum_range_succ]

theorem sqd_cast (x : ℕ) : ((sqd x : ℕ) : ℤ) = ((x : ℤ) - 2) ^ 2 := by
  unfold sqd
  split_ifs with h
  · push_cast [Nat.cast_sub h]; ring
  · push_cast [Nat.cast_sub (by omega : x ≤ 2)]; ring

theorem wcheck_sound (n : ℕ) (u : Fin n → ℕ) (r : List ℕ) (h : wcheck n (List.ofFn u) r = true) :
    ∃ r' : Fin n → ℕ, SLCW (Fin n) n u r' := by
  simp only [wcheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hpw, hW⟩, hS⟩ := h
  obtain ⟨hlen, hpt⟩ := pw_spec _ _ hpw
  simp only [List.length_ofFn] at hlen
  set r' : Fin n → ℕ := fun i => r[i.1]'(by omega) with hr'
  have hrr : List.ofFn r' = r := by
    apply List.ext_getElem (by simp [hlen])
    intro i h1 h2
    simp [hr']
  rw [← hrr] at hW hS
  refine ⟨r', fun g => ?_, fun g => ?_, ?_, ?_⟩
  · have := (hpt g.1 (by simp) (by omega)).1
    simpa [hr'] using this
  · have := (hpt g.1 (by simp) (by omega)).2
    simpa [hr'] using this
  · rw [sum_map_ofFn, sum_map_ofFn] at hW
    have hW' : ((∑ i, r' i ^ 2 : ℕ) : ℤ) ≤ ((∑ i, sqd (u i) : ℕ) : ℤ) := by exact_mod_cast hW
    push_cast [sqd_cast] at hW'
    exact hW'
  · rw [spreadR_ofFn] at hS
    exact hS

theorem excB_sound (n : ℕ) (hn : 3 ≤ n) (u : Fin n → ℕ) (h : excB n (List.ofFn u) = true) :
    Exc (Fin n) n u := by
  simp only [excB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have e1 := ofFn_getD u ⟨n - 1, by omega⟩
  have e2 := ofFn_getD u ⟨n - 2, by omega⟩
  have e3 := ofFn_getD u ⟨n - 3, by omega⟩
  simp only at e1 e2 e3
  refine ⟨⟨n - 1, by omega⟩, ⟨n - 2, by omega⟩, ⟨n - 3, by omega⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Fin.ext_iff]; omega
  · simp [Fin.ext_iff]; omega
  · simp [Fin.ext_iff]; omega
  · rw [← e1]; exact h1
  · rw [← e2, ← e3]; exact h2
  · rw [← e3]; exact h3
  · rw [← e3]; exact h4
  · intro g hg1 hg2 hg3
    have hg : g.1 < n - 3 := by
      simp only [ne_eq, Fin.ext_iff] at hg1 hg2 hg3
      omega
    have := h5 g.1 hg
    rwa [ofFn_getD u g] at this

theorem hypB_of (n : ℕ) (u : Fin n → ℕ) (hv : ∀ g, u g ≤ n - 1)
    (hconc : 2 * n - 4 ≤ ∑ g, (u g).choose 2) : hypB n (List.ofFn u) = true := by
  simp only [hypB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact hv i
  · rw [sum_map_ofFn]
    simpa only [Nat.choose_two_right] using hconc

/-- Soundness of the kernel check: the Shape Lemma on `n` classes follows from it. -/
theorem small_of_check (n : ℕ) (hn : 3 ≤ n) (sp : List (List ℕ))
    (hcheck : (gen n 0 (2 * n - 1)).all (good n sp) = true)
    {α : Type*} [Fintype α] (hcard : Fintype.card α = n) (v : α → ℕ)
    (hv : ∀ g, v g ≤ n - 1) (hsum : ∑ g, v g = 2 * n - 1)
    (hconc : 2 * n - 4 ≤ ∑ g, (v g).choose 2) : ShapeConcl α n v := by
  let e : α ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let w : Fin n → ℕ := v ∘ e.symm
  let σ := Tuple.sort w
  let E : Fin n ≃ α := σ.trans e.symm
  have hE : v ∘ E = w ∘ σ := by funext i; rfl
  apply shapeConcl_comp_equiv E
  rw [hE]
  set u := w ∘ σ with hu
  have hmono : Monotone u := Tuple.monotone_sort w
  have huE : u = v ∘ E := hE.symm
  have husum : ∑ i, u i = 2 * n - 1 := by rw [huE, ← hsum]; exact Equiv.sum_comp E v
  have hmem : List.ofFn u ∈ gen n 0 (2 * n - 1) := by
    apply mem_gen
    · simp
    · exact List.pairwise_ofFn.2 (fun i j hij => hmono hij.le)
    · simp
    · rw [List.sum_ofFn, husum]
  have hg := List.all_eq_true.1 hcheck _ hmem
  have hhyp : hypB n (List.ofFn u) = true := by
    apply hypB_of n u (fun i => by rw [huE]; exact hv _)
    have := Equiv.sum_comp E (fun g => (v g).choose 2)
    rw [huE]
    simp only [Function.comp]
    rw [this]
    exact hconc
  simp only [good, hhyp, Bool.not_true, Bool.false_or, Bool.or_eq_true, List.any_eq_true] at hg
  rcases hg with hx | ⟨r, _, hr⟩
  · exact Or.inr (excB_sound n hn u hx)
  · exact Or.inl (wcheck_sound n u r hr)

/-! ### The two checks

Each check is split into chunks of 250 lists, one declaration each, to keep the kernel's
memory use per declaration small. -/

theorem all_of_chunks {β : Type*} (f : β → Bool) (c : ℕ) :
    ∀ (m : ℕ) (L : List β), L.length ≤ c * m →
      (∀ i < m, ((L.drop (c * i)).take c).all f = true) → L.all f = true
  | 0, L, hL, _ => by
    have : L = [] := List.length_eq_zero_iff.1 (by simpa using hL)
    subst this
    rfl
  | m + 1, L, hL, h => by
    rw [← List.take_append_drop c L, List.all_append, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by omega), all_of_chunks f c m (L.drop c) ?_ (fun i hi => ?_)⟩
    · simp only [List.length_drop]
      rw [Nat.mul_succ] at hL
      omega
    · rw [List.drop_drop, ← show c * (i + 1) = c + c * i by ring]
      exact h (i + 1) (by omega)

/-- Explicit depth lists for three shapes at `p = 11` (ascending order), cf. Section 6 of the paper. -/
def sp11 : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 1, 1, 3, 3, 3], [0, 0, 0, 0, 0, 1, 1, 1, 1, 3, 2],
    [0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 3]]

theorem check11_0 :
    (((gen 11 0 (2 * 11 - 1)).drop (250 * 0)).take 250).all (good 11 sp11) = true := by
  decide +kernel

theorem check11_1 :
    (((gen 11 0 (2 * 11 - 1)).drop (250 * 1)).take 250).all (good 11 sp11) = true := by
  decide +kernel

theorem check11_2 :
    (((gen 11 0 (2 * 11 - 1)).drop (250 * 2)).take 250).all (good 11 sp11) = true := by
  decide +kernel

theorem check11 : (gen 11 0 (2 * 11 - 1)).all (good 11 sp11) = true := by
  refine all_of_chunks _ 250 3 _ (by decide +kernel) (fun i hi => ?_)
  interval_cases i
  exacts [check11_0, check11_1, check11_2]

theorem check13_0 :
    (((gen 13 0 (2 * 13 - 1)).drop (250 * 0)).take 250).all (good 13 []) = true := by
  decide +kernel

theorem check13_1 :
    (((gen 13 0 (2 * 13 - 1)).drop (250 * 1)).take 250).all (good 13 []) = true := by
  decide +kernel

theorem check13_2 :
    (((gen 13 0 (2 * 13 - 1)).drop (250 * 2)).take 250).all (good 13 []) = true := by
  decide +kernel

theorem check13_3 :
    (((gen 13 0 (2 * 13 - 1)).drop (250 * 3)).take 250).all (good 13 []) = true := by
  decide +kernel

theorem check13_4 :
    (((gen 13 0 (2 * 13 - 1)).drop (250 * 4)).take 250).all (good 13 []) = true := by
  decide +kernel

theorem check13_5 :
    (((gen 13 0 (2 * 13 - 1)).drop (250 * 5)).take 250).all (good 13 []) = true := by
  decide +kernel

theorem check13_6 :
    (((gen 13 0 (2 * 13 - 1)).drop (250 * 6)).take 250).all (good 13 []) = true := by
  decide +kernel

theorem check13_7 :
    (((gen 13 0 (2 * 13 - 1)).drop (250 * 7)).take 250).all (good 13 []) = true := by
  decide +kernel

theorem check13 : (gen 13 0 (2 * 13 - 1)).all (good 13 []) = true := by
  refine all_of_chunks _ 250 8 _ (by decide +kernel) (fun i hi => ?_)
  interval_cases i
  exacts [check13_0, check13_1, check13_2, check13_3, check13_4, check13_5, check13_6, check13_7]

theorem shape_small {α : Type*} [Fintype α] (p : ℕ) (hp : p = 11 ∨ p = 13)
    (hcard : Fintype.card α = p) (v : α → ℕ)
    (hv : ∀ g, v g ≤ p - 1) (hsum : ∑ g, v g = 2 * p - 1)
    (hconc : 2 * p - 4 ≤ ∑ g, (v g).choose 2) : ShapeConcl α p v := by
  rcases hp with rfl | rfl
  · exact small_of_check 11 (by norm_num) sp11 check11 hcard v hv hsum hconc
  · exact small_of_check 13 (by norm_num) [] check13 hcard v hv hsum hconc

end Harborth.ShapeAux
