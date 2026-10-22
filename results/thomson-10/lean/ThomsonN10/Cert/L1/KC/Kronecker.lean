/- Adapted from proof/lean/ClaudeL1/KC/Kronecker.lean, aravindkarthigeyan/thomson-n9-lean, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
/-
ThomsonN10.Cert.L1.KC.Kronecker (copied from the upstream exact checker, namespace renamed) : Kronecker substitution, proved from scratch in core Lean 4.

* `kron_sound`      : zero test.  If every exponent is `< D` and the uncollected l1 norm is
                      `< 2^w`, then `p(2^w, 2^(wD), 2^(wD^2)) = 0` forces every collected
                      coefficient to vanish (hence `p = 0` as a function on every commutative ring).
* `kron_decode`     : coefficient extraction.  If the uncollected l1 norm is `< 2^(w-1)`, the
                      balanced base-`2^w` digits of `p(2^w, 2^(wD), 2^(wD^2))` are exactly the
                      collected coefficients; `kron_decode_l1` turns this into an exact l1 value.
-/
import ThomsonN10.Cert.L1.KC.Poly

namespace ThomsonN10.Cert.L1.KC

/-! ### Kronecker exponent -/

def kexp (D a b d : Nat) : Nat := a + D * (b + D * d)

theorem kexp_inj {D a b d a' b' d' : Nat} (ha : a < D) (hb : b < D) (ha' : a' < D)
    (hb' : b' < D) (h : kexp D a b d = kexp D a' b' d') : a = a' ∧ b = b' ∧ d = d' := by
  have hD : 0 < D := by omega
  unfold kexp at h
  have h1 : (a + D * (b + D * d)) % D = (a' + D * (b' + D * d')) % D := by rw [h]
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt ha'] at h1
  subst h1
  have h2 : b + D * d = b' + D * d' := Nat.eq_of_mul_eq_mul_left hD (Nat.add_left_cancel h)
  have h3 : (b + D * d) % D = (b' + D * d') % D := by rw [h2]
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt hb'] at h3
  subst h3
  exact ⟨rfl, rfl, Nat.eq_of_mul_eq_mul_left hD (Nat.add_left_cancel h2)⟩

theorem kexp_lt {D a b d : Nat} (ha : a < D) (hb : b < D) (hd : d < D) :
    kexp D a b d < D * D * D := by
  unfold kexp
  have h1 : D * (d + 1) ≤ D * D := Nat.mul_le_mul_left D hd
  have h2 : D * (b + D * d + 1) ≤ D * (D * D) := Nat.mul_le_mul_left D (by rw [Nat.mul_succ] at h1; omega)
  rw [Nat.mul_succ] at h2
  rw [Nat.mul_assoc]
  omega

/-! ### Univariate uncollected polynomials -/

abbrev UPoly := List (Int × Nat)

def uval (X : Int) : UPoly → Int
  | [] => 0
  | e :: l => e.1 * X ^ e.2 + uval X l

def ucoeff : UPoly → Nat → Int
  | [], _ => 0
  | e :: l, j => (if e.2 = j then e.1 else 0) + ucoeff l j

/-- split off the constant coefficient; shift the remaining exponents down by one -/
def lowSplit : UPoly → Int × UPoly
  | [] => (0, [])
  | e :: l =>
    if e.2 = 0 then ((lowSplit l).1 + e.1, (lowSplit l).2)
    else ((lowSplit l).1, (e.1, e.2 - 1) :: (lowSplit l).2)

theorem lowSplit_val (X : Int) (l : UPoly) :
    uval X l = (lowSplit l).1 + X * uval X (lowSplit l).2 := by
  induction l with
  | nil => simp [uval, lowSplit]
  | cons e l ih =>
    obtain ⟨c, k⟩ := e
    by_cases hk : k = 0
    · subst hk; simp only [uval, lowSplit, ite_true, Int.pow_zero, Int.mul_one, ih]; omega
    · simp only [uval, lowSplit, hk, ite_false, ih]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel, Int.pow_succ, Int.mul_add]
      rw [Int.mul_comm (X ^ k') X, ← Int.mul_assoc, Int.mul_comm c X, Int.mul_assoc]
      omega

theorem lowSplit_coeff0 (l : UPoly) : ucoeff l 0 = (lowSplit l).1 := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    by_cases hk : e.2 = 0
    · simp only [ucoeff, lowSplit, hk, ite_true, ih]; omega
    · simp only [ucoeff, lowSplit, hk, ite_false, ih]; omega

theorem lowSplit_coeffS (l : UPoly) (j : Nat) : ucoeff l (j + 1) = ucoeff (lowSplit l).2 j := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    by_cases hk : e.2 = 0
    · simp only [ucoeff, lowSplit, hk, ite_true, ih]; simp
    · simp only [ucoeff, lowSplit, hk, ite_false, ih]
      have : (e.2 = j + 1) ↔ (e.2 - 1 = j) := by omega
      simp only [this]

theorem lowSplit_keys {K : Nat} (l : UPoly) (h : ∀ e ∈ l, e.2 < K + 1) :
    ∀ e ∈ (lowSplit l).2, e.2 < K := by
  induction l with
  | nil => simp [lowSplit]
  | cons e l ih =>
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have he := h e (List.mem_cons_self ..)
    by_cases hk : e.2 = 0
    · simp only [lowSplit, hk, ite_true]; exact ih'
    · simp only [lowSplit, hk, ite_false]
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simp only; omega
      · exact ih' x hx

/-- `c + B*v = 0` with `|c| < B` forces `c = 0` and `v = 0`. -/
theorem small_add_mul_eq_zero {c v : Int} {B : Nat} (h : c + (B : Int) * v = 0)
    (hc : c.natAbs < B) : c = 0 ∧ v = 0 := by
  have hc' : c = -((B : Int) * v) := by omega
  have habs : c.natAbs = B * v.natAbs := by
    rw [hc', Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_natCast]
  rcases Nat.eq_zero_or_pos v.natAbs with h0 | hpos
  · have hv : v = 0 := Int.natAbs_eq_zero.mp h0
    subst hv; omega
  · have := Nat.le_mul_of_pos_right B hpos
    omega

/-- Univariate uniqueness: bounded collected coefficients and a zero value at `B` force all
collected coefficients to vanish. -/
theorem ucoeff_eq_zero (B : Nat) :
    ∀ (K : Nat) (l : UPoly), (∀ e ∈ l, e.2 < K) → (∀ j, (ucoeff l j).natAbs < B) →
      uval (B : Int) l = 0 → ∀ j, ucoeff l j = 0 := by
  intro K
  induction K with
  | zero =>
    intro l hk _ _ j
    match l with
    | [] => rfl
    | e :: _ => exact absurd (hk e (List.mem_cons_self ..)) (Nat.not_lt_zero _)
  | succ K ih =>
    intro l hk hc hv
    rw [lowSplit_val] at hv
    have h0 := hc 0
    rw [lowSplit_coeff0] at h0
    obtain ⟨hc0, hrest⟩ := small_add_mul_eq_zero hv h0
    have hrest' := ih (lowSplit l).2 (lowSplit_keys l hk)
      (fun j => by rw [← lowSplit_coeffS]; exact hc (j + 1)) hrest
    intro j
    cases j with
    | zero => rw [lowSplit_coeff0]; exact hc0
    | succ j => rw [lowSplit_coeffS]; exact hrest' j

/-! ### From three variables to one -/

def Poly.toU (D : Nat) (p : Poly) : UPoly := p.map (fun s => (s.c, kexp D s.a s.b s.d))

theorem Poly.eval_kron (X : Int) (D : Nat) (p : Poly) :
    Poly.eval X (X ^ D) (X ^ (D * D)) p = uval X (p.toU D) := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    simp only [Poly.eval, Poly.toU, List.map_cons, uval] at *
    rw [ih]
    congr 1
    simp only [Term.eval, kexp, ← Int.pow_mul, ← Int.pow_add]
    have : D * (s.b + D * s.d) = D * s.b + D * D * s.d := by
      rw [Nat.mul_add, Nat.mul_assoc]
    rw [this, ← Nat.add_assoc]
    rfl

theorem Poly.coeff_eq_ucoeff {D : Nat} {p : Poly} (hp : p.DegLt D) {a b d : Nat} (ha : a < D)
    (hb : b < D) : p.coeff a b d = ucoeff (p.toU D) (kexp D a b d) := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    simp only [Poly.coeff, Poly.toU, List.map_cons, ucoeff] at *
    rw [ih (fun t ht => hp t (List.mem_cons_of_mem _ ht))]
    congr 1
    obtain ⟨hsa, hsb, _⟩ := hp s (List.mem_cons_self ..)
    by_cases h : s.sameExp a b d = true
    · simp only [Term.sameExp, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      simp [Term.sameExp]
    · have h' : ¬ kexp D s.a s.b s.d = kexp D a b d := by
        intro hk
        obtain ⟨rfl, rfl, rfl⟩ := kexp_inj hsa hsb ha hb hk
        simp [Term.sameExp] at h
      simp only [Bool.not_eq_true] at h
      simp [h, h']

theorem Poly.coeff_eq_zero_of_out {D : Nat} {p : Poly} (hp : p.DegLt D) {a b d : Nat}
    (hout : ¬ (a < D ∧ b < D ∧ d < D)) : p.coeff a b d = 0 := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    simp only [Poly.coeff]
    rw [ih (fun t ht => hp t (List.mem_cons_of_mem _ ht))]
    have hs := hp s (List.mem_cons_self ..)
    have : s.sameExp a b d = false := by
      simp only [Term.sameExp, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
      omega
    simp [this]

theorem natAbs_ucoeff_toU_le (D : Nat) (p : Poly) (j : Nat) :
    (ucoeff (p.toU D) j).natAbs ≤ p.l1 := by
  induction p with
  | nil => simp [ucoeff, Poly.toU, Poly.l1]
  | cons s p ih =>
    simp only [Poly.toU, List.map_cons, ucoeff, Poly.l1] at *
    have h1 : (if kexp D s.a s.b s.d = j then s.c else 0).natAbs ≤ s.c.natAbs := by
      split <;> simp
    have := Int.natAbs_add_le (if kexp D s.a s.b s.d = j then s.c else 0) (ucoeff (Poly.toU D p) j)
    omega

theorem toU_keys {D : Nat} {p : Poly} (hp : p.DegLt D) : ∀ e ∈ p.toU D, e.2 < D * D * D := by
  intro e he
  simp only [Poly.toU, List.mem_map] at he
  obtain ⟨s, hs, rfl⟩ := he
  obtain ⟨h1, h2, h3⟩ := hp s hs
  exact kexp_lt h1 h2 h3

/-- **Kronecker zero test.** -/
theorem kron_sound (w D : Nat) (p : Poly) (hdeg : p.DegLt D) (hl1 : p.l1 < 2 ^ w)
    (hval : uval ((2 ^ w : Nat) : Int) (p.toU D) = 0) : ∀ a b d, p.coeff a b d = 0 := by
  intro a b d
  by_cases hin : a < D ∧ b < D ∧ d < D
  · rw [Poly.coeff_eq_ucoeff hdeg hin.1 hin.2.1]
    exact ucoeff_eq_zero (2 ^ w) (D * D * D) (p.toU D) (toU_keys hdeg)
      (fun j => Nat.lt_of_le_of_lt (natAbs_ucoeff_toU_le D p j) hl1) hval _
  · exact Poly.coeff_eq_zero_of_out hdeg hin

section
open Lean.Grind
/-- **Kronecker zero test, functional form**: the polynomial vanishes identically on every
commutative ring. -/
theorem kron_eval_zero (w D : Nat) (p : Poly) (hdeg : p.DegLt D) (hl1 : p.l1 < 2 ^ w)
    (hval : uval ((2 ^ w : Nat) : Int) (p.toU D) = 0) {α : Type u} [CommRing α] (x y z : α) :
    p.eval x y z = 0 :=
  Poly.eval_eq_zero_of_coeff p (kron_sound w D p hdeg hl1 hval) x y z
end

/-- **Kronecker substitution, `iff` form**: under the degree and l1 hypotheses, the value at
`(2^w, 2^(wD), 2^(wD^2))` vanishes iff every collected coefficient vanishes. -/
theorem kron_iff (w D : Nat) (p : Poly) (hdeg : p.DegLt D) (hl1 : p.l1 < 2 ^ w) :
    uval ((2 ^ w : Nat) : Int) (p.toU D) = 0 ↔ ∀ a b d, p.coeff a b d = 0 := by
  constructor
  · exact kron_sound w D p hdeg hl1
  · intro h
    rw [← Poly.eval_kron]
    exact Poly.eval_eq_zero_of_coeff p h _ _ _

/-! ### Natural-number digits, divide and conquer -/

/-- Horner value of a digit list (least significant first). -/
def nval (X : Nat) : List Nat → Nat
  | [] => 0
  | e :: l => e + X * nval X l

theorem nval_append (X : Nat) (l₁ l₂ : List Nat) :
    nval X (l₁ ++ l₂) = nval X l₁ + X ^ l₁.length * nval X l₂ := by
  induction l₁ with
  | nil => simp [nval]
  | cons e l ih =>
    simp only [List.cons_append, nval, ih, List.length_cons, Nat.pow_succ, Nat.mul_add]
    rw [Nat.mul_comm (X ^ l.length) X, Nat.mul_assoc]; omega

/-- sequential base-`2^w` digits (fallback) -/
def digitsSeq (w : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | S + 1, K => K % 2 ^ w :: digitsSeq w S (K >>> w)

/-- divide-and-conquer base-`2^w` digits of `K mod 2^(w*S)`; `fuel` only bounds the depth
(any fuel is correct; `log2 S + 1` makes it fully divide-and-conquer). -/
def digitsDC (w : Nat) : Nat → Nat → Nat → List Nat
  | 0, S, K => digitsSeq w S K
  | f + 1, S, K =>
    if S ≤ 1 then digitsSeq w S K
    else digitsDC w f (S / 2) (K % 2 ^ (w * (S / 2))) ++
         digitsDC w f (S - S / 2) (K >>> (w * (S / 2)))

theorem mod_two_pow_add (K w a b : Nat) :
    K % 2 ^ (w * a) + 2 ^ (w * a) * (K / 2 ^ (w * a) % 2 ^ (w * b)) = K % 2 ^ (w * (a + b)) := by
  rw [Nat.mul_add, Nat.pow_add, Nat.mod_mul]

theorem digitsSeq_spec (w : Nat) : ∀ S K, (digitsSeq w S K).length = S ∧
    (∀ e ∈ digitsSeq w S K, e < 2 ^ w) ∧ nval (2 ^ w) (digitsSeq w S K) = K % 2 ^ (w * S) := by
  intro S
  induction S with
  | zero => intro K; simp [digitsSeq, nval, Nat.mod_one]
  | succ S ih =>
    intro K
    obtain ⟨h1, h2, h3⟩ := ih (K >>> w)
    refine ⟨by simp [digitsSeq, h1], ?_, ?_⟩
    · intro e he
      simp only [digitsSeq, List.mem_cons] at he
      rcases he with rfl | he
      · exact Nat.mod_lt _ (Nat.two_pow_pos w)
      · exact h2 e he
    · simp only [digitsSeq, nval]
      rw [h3, Nat.shiftRight_eq_div_pow]
      have := mod_two_pow_add K w 1 S
      simp only [Nat.mul_one] at this
      rw [this, Nat.add_comm 1 S]

theorem digitsDC_spec (w : Nat) : ∀ f S K, (digitsDC w f S K).length = S ∧
    (∀ e ∈ digitsDC w f S K, e < 2 ^ w) ∧ nval (2 ^ w) (digitsDC w f S K) = K % 2 ^ (w * S) := by
  intro f
  induction f with
  | zero => intro S K; exact digitsSeq_spec w S K
  | succ f ih =>
    intro S K
    by_cases hS : S ≤ 1
    · simp only [digitsDC, hS, ite_true]; exact digitsSeq_spec w S K
    · simp only [digitsDC, hS, ite_false]
      obtain ⟨a1, a2, a3⟩ := ih (S / 2) (K % 2 ^ (w * (S / 2)))
      obtain ⟨b1, b2, b3⟩ := ih (S - S / 2) (K >>> (w * (S / 2)))
      refine ⟨by simp [a1, b1]; omega, ?_, ?_⟩
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact a2 e he
        · exact b2 e he
      · have e1 : nval (2 ^ w) (digitsDC w f (S / 2) (K % 2 ^ (w * (S / 2))) ++
            digitsDC w f (S - S / 2) (K >>> (w * (S / 2)))) =
            K % 2 ^ (w * (S / 2)) + 2 ^ (w * (S / 2)) * (K / 2 ^ (w * (S / 2)) % 2 ^ (w * (S - S / 2))) := by
          rw [nval_append, a3, b3, a1, Nat.mod_mod, Nat.shiftRight_eq_div_pow, ← Nat.pow_mul]
        rw [e1, mod_two_pow_add, show S / 2 + (S - S / 2) = S by omega]

theorem nval_lt (X : Nat) (_hX : 0 < X) : ∀ l : List Nat, (∀ e ∈ l, e < X) →
    nval X l < X ^ l.length := by
  intro l
  induction l with
  | nil => intro _; simp [nval]
  | cons e l ih =>
    intro h
    have he := h e (List.mem_cons_self ..)
    have hl := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [nval, List.length_cons, Nat.pow_succ]
    have : X * nval X l + X ≤ X * X ^ l.length := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left X hl
    rw [Nat.mul_comm (X ^ l.length) X]; omega

theorem nval_inj (X : Nat) (hX : 0 < X) : ∀ (l₁ l₂ : List Nat), (∀ e ∈ l₁, e < X) →
    (∀ e ∈ l₂, e < X) → l₁.length = l₂.length → nval X l₁ = nval X l₂ → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ _ _ hlen _; cases l₂ <;> simp_all
  | cons e l ih =>
    intro l₂ h1 h2 hlen hv
    match l₂, h2, hlen, hv with
    | f :: m, h2, hlen, hv =>
      simp only [nval] at hv
      have he := h1 e (List.mem_cons_self ..)
      have hf := h2 f (List.mem_cons_self ..)
      have hef : e = f := by
        have := congrArg (· % X) hv
        simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt hf] at this
        exact this
      subst hef
      have hm : nval X l = nval X m := Nat.eq_of_mul_eq_mul_left hX (Nat.add_left_cancel hv)
      rw [ih m (fun x hx => h1 x (List.mem_cons_of_mem _ hx))
        (fun x hx => h2 x (List.mem_cons_of_mem _ hx)) (by simpa using hlen) hm]

/-! ### Finite sums (front recursion) -/

def dsum : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | S + 1, f => f 0 + dsum S (fun j => f (j + 1))

theorem dsum_add (S : Nat) (f g : Nat → Int) :
    dsum S (fun j => f j + g j) = dsum S f + dsum S g := by
  induction S generalizing f g with
  | zero => rfl
  | succ S ih => simp only [dsum, ih (fun j => f (j + 1)) (fun j => g (j + 1))]; omega

theorem dsum_mul_left (S : Nat) (c : Int) (f : Nat → Int) :
    dsum S (fun j => c * f j) = c * dsum S f := by
  induction S generalizing f with
  | zero => simp [dsum]
  | succ S ih => simp only [dsum, ih (fun j => f (j + 1)), Int.mul_add]

theorem dsum_zero (S : Nat) : dsum S (fun _ => 0) = 0 := by
  induction S with
  | zero => rfl
  | succ S ih => simp [dsum, ih]

theorem dsum_single (S k : Nat) (g : Nat → Int) :
    dsum S (fun j => if k = j then g j else 0) = if k < S then g k else 0 := by
  induction S generalizing k g with
  | zero => simp [dsum]
  | succ S ih =>
    simp only [dsum]
    cases k with
    | zero =>
      have : ∀ j, ¬ (0 = j + 1) := by omega
      simp only [this, ite_false]
      simp [dsum_zero]
    | succ k =>
      have := ih k (fun j => g (j + 1))
      simp only [Nat.add_right_cancel_iff] at *
      rw [this]
      have h' : ¬ (k + 1 = 0) := by omega
      simp only [h', ite_false, Int.zero_add]
      by_cases hk : k < S
      · simp [hk, show k + 1 < S + 1 by omega]
      · simp [hk, show ¬ (k + 1 < S + 1) by omega]

/-- dense regrouping of an uncollected univariate polynomial -/
theorem uval_eq_dsum (X : Int) (S : Nat) : ∀ l : UPoly, (∀ e ∈ l, e.2 < S) →
    uval X l = dsum S (fun j => ucoeff l j * X ^ j) := by
  intro l
  induction l with
  | nil =>
    intro _
    simp only [uval, ucoeff, Int.zero_mul, dsum_zero]
  | cons e l ih =>
    intro h
    simp only [uval, ucoeff, Int.add_mul]
    rw [dsum_add, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    congr 1
    have hk := h e (List.mem_cons_self ..)
    have := dsum_single S e.2 (fun j => e.1 * X ^ j)
    simp only [hk, ite_true] at this
    rw [← this]
    congr 1; funext j; split <;> simp

/-- tabulate `f 0, ..., f (S-1)` -/
def tab : Nat → (Nat → Nat) → List Nat
  | 0, _ => []
  | S + 1, f => f 0 :: tab S (fun j => f (j + 1))

theorem tab_length (S : Nat) (f : Nat → Nat) : (tab S f).length = S := by
  induction S generalizing f with
  | zero => rfl
  | succ S ih => simp [tab, ih]

theorem mem_tab {S : Nat} {f : Nat → Nat} {e : Nat} (h : e ∈ tab S f) : ∃ j, j < S ∧ e = f j := by
  induction S generalizing f with
  | zero => cases h
  | succ S ih =>
    simp only [tab, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, by omega, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := ih h; exact ⟨j + 1, by omega, rfl⟩

theorem tab_getD (S : Nat) (f : Nat → Nat) (j : Nat) (hj : j < S) : (tab S f).getD j 0 = f j := by
  induction S generalizing f j with
  | zero => omega
  | succ S ih =>
    cases j with
    | zero => rfl
    | succ j => simp only [tab, List.getD_cons_succ]; exact ih _ j (by omega)

theorem nval_tab (X : Nat) (S : Nat) (f : Nat → Nat) :
    (nval X (tab S f) : Int) = dsum S (fun j => (f j : Int) * (X : Int) ^ j) := by
  induction S generalizing f with
  | zero => rfl
  | succ S ih =>
    simp only [tab, nval, dsum, Int.pow_zero, Int.mul_one, Int.natCast_add, Int.natCast_mul, ih]
    rw [← dsum_mul_left]
    congr 1; congr 1; funext j
    rw [Int.pow_succ]; grind

/-! ### Balanced digits -/

/-- `Σ_{j<S} 2^(w-1) * 2^(w j)`, computed as `2^(w-1) * (2^(wS)-1)/(2^w-1)` -/
def offsetNat (w S : Nat) : Nat := 2 ^ (w - 1) * ((2 ^ (w * S) - 1) / (2 ^ w - 1))

/-- balanced base-`2^w` digits of `K` in `S` slots (each in `[-2^(w-1), 2^(w-1))`) -/
def balDigits (w S : Nat) (K : Int) : List Int :=
  List.map (fun e : Nat => (e : Int) - ((2 ^ (w - 1) : Nat) : Int))
    (digitsDC w (Nat.log2 S + 1) S (K + (offsetNat w S : Int)).toNat)

theorem repunit_mul (X S : Nat) (hX : 1 ≤ X) :
    nval X (tab S (fun _ => 1)) * (X - 1) = X ^ S - 1 := by
  induction S with
  | zero => simp [tab, nval]
  | succ S ih =>
    simp only [tab, nval] at *
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, ih, Nat.pow_succ]
    have h1 : 1 ≤ X ^ S := Nat.pow_pos (by omega)
    rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm X (X ^ S)]
    have : X ≤ X ^ S * X := by
      have := Nat.mul_le_mul_right X h1; simpa using this
    omega

theorem offsetNat_eq (w S : Nat) (hw : 1 ≤ w) :
    (offsetNat w S : Int) = dsum S (fun j => ((2 ^ (w - 1) : Nat) : Int) * ((2 ^ w : Nat) : Int) ^ j) := by
  have hX : 1 ≤ 2 ^ w := Nat.two_pow_pos w
  have hX1 : 0 < 2 ^ w - 1 := by
    have : 2 ≤ 2 ^ w := by
      have := Nat.pow_le_pow_right (by decide : 0 < 2) hw; simpa using this
    omega
  have hrep := repunit_mul (2 ^ w) S hX
  rw [← Nat.pow_mul] at hrep
  have hdiv : (2 ^ (w * S) - 1) / (2 ^ w - 1) = nval (2 ^ w) (tab S (fun _ => 1)) := by
    rw [← hrep, Nat.mul_div_cancel _ hX1]
  unfold offsetNat
  rw [hdiv, Int.natCast_mul, nval_tab, ← dsum_mul_left]
  congr 1; funext j; simp

/-- **Univariate decoding**: with collected coefficients bounded by `2^(w-1)` and all keys
`< S`, the balanced digits of the value at `2^w` are exactly the collected coefficients. -/
theorem udecode (w S : Nat) (hw : 1 ≤ w) (l : UPoly) (hkeys : ∀ e ∈ l, e.2 < S)
    (hc : ∀ j, (ucoeff l j).natAbs < 2 ^ (w - 1)) :
    (balDigits w S (uval ((2 ^ w : Nat) : Int) l)).length = S ∧
    ∀ j, j < S → (balDigits w S (uval ((2 ^ w : Nat) : Int) l)).getD j 0 = ucoeff l j := by
  have hHX : 2 ^ w = 2 * 2 ^ (w - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have hXpos : 0 < 2 ^ w := Nat.two_pow_pos w
  -- dense natural digits n_j = C_j + H
  let H : Nat := 2 ^ (w - 1)
  let n : Nat → Nat := fun j => (ucoeff l j + (H : Int)).toNat
  have hn : ∀ j, ((n j : Nat) : Int) = ucoeff l j + (H : Int) := by
    intro j; have := hc j; simp only [n]; omega
  have hnlt : ∀ j, n j < 2 ^ w := by
    intro j; have := hc j; have := hn j; omega
  -- the shifted value equals nval of the dense digits
  have hval : uval ((2 ^ w : Nat) : Int) l + (offsetNat w S : Int) = (nval (2 ^ w) (tab S n) : Int) := by
    rw [uval_eq_dsum _ S l hkeys, offsetNat_eq w S hw, ← dsum_add, nval_tab]
    congr 1; funext j
    rw [hn j, Int.add_mul]
  have hdig := digitsDC_spec w (Nat.log2 S + 1) S (nval (2 ^ w) (tab S n))
  have hlt : nval (2 ^ w) (tab S n) < 2 ^ (w * S) := by
    have := nval_lt (2 ^ w) hXpos (tab S n) (by
      intro e he; obtain ⟨j, _, rfl⟩ := mem_tab he; exact hnlt j)
    rwa [tab_length, ← Nat.pow_mul] at this
  rw [Nat.mod_eq_of_lt hlt] at hdig
  obtain ⟨d1, d2, d3⟩ := hdig
  have heq : digitsDC w (Nat.log2 S + 1) S (nval (2 ^ w) (tab S n)) = tab S n :=
    nval_inj (2 ^ w) hXpos _ _ d2
      (by intro e he; obtain ⟨j, _, rfl⟩ := mem_tab he; exact hnlt j)
      (by rw [d1, tab_length]) d3
  unfold balDigits
  rw [hval, Int.toNat_natCast, heq]
  refine ⟨by simp [tab_length], ?_⟩
  intro j hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  have hj' : j < (tab S n).length := by rw [tab_length]; exact hj
  rw [List.getElem?_eq_getElem hj']
  simp only [Option.map_some, Option.getD_some]
  have := tab_getD S n j hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'] at this
  simp only [Option.getD_some] at this
  rw [this, hn j]; simp [H]

/-- **Kronecker decoding (three variables).** -/
theorem kron_decode (w D : Nat) (hw : 1 ≤ w) (p : Poly) (hdeg : p.DegLt D)
    (hl1 : p.l1 < 2 ^ (w - 1)) :
    (balDigits w (D * D * D) (uval ((2 ^ w : Nat) : Int) (p.toU D))).length = D * D * D ∧
    ∀ a b d, a < D → b < D → d < D →
      p.coeff a b d = (balDigits w (D * D * D) (uval ((2 ^ w : Nat) : Int) (p.toU D))).getD
        (kexp D a b d) 0 := by
  obtain ⟨h1, h2⟩ := udecode w (D * D * D) hw (p.toU D) (toU_keys hdeg)
    (fun j => Nat.lt_of_le_of_lt (natAbs_ucoeff_toU_le D p j) hl1)
  refine ⟨h1, fun a b d ha hb hd => ?_⟩
  rw [h2 _ (kexp_lt ha hb hd), Poly.coeff_eq_ucoeff hdeg ha hb]

/-! ### Exact l1 of the collected coefficients -/

def nsum : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | S + 1, f => f 0 + nsum S (fun j => f (j + 1))

theorem nsum_add (s t : Nat) (f : Nat → Nat) :
    nsum (s + t) f = nsum s f + nsum t (fun r => f (s + r)) := by
  induction s generalizing f with
  | zero => simp [nsum]
  | succ s ih =>
    rw [Nat.succ_add]
    simp only [nsum, ih (fun j => f (j + 1))]
    have : (fun r => f (s + r + 1)) = (fun r => f (s + 1 + r)) := by funext r; congr 1; omega
    rw [this]; omega

theorem nsum_mul (m n : Nat) (f : Nat → Nat) :
    nsum (m * n) f = nsum n (fun q => nsum m (fun r => f (r + m * q))) := by
  induction n generalizing f with
  | zero => simp [nsum]
  | succ n ih =>
    rw [show m * (n + 1) = m + m * n by rw [Nat.mul_succ, Nat.add_comm], nsum_add, ih]
    show _ = nsum m (fun r => f (r + m * 0)) +
      nsum n (fun q => nsum m (fun r => f (r + m * (q + 1))))
    congr 1
    congr 1; funext q; congr 1; funext r; congr 1; rw [Nat.mul_succ]; omega

/-- l1 norm of the collected coefficients over the box `[0,D)^3` -/
def boxL1 (D : Nat) (p : Poly) : Nat :=
  nsum D (fun d => nsum D (fun b => nsum D (fun a => (p.coeff a b d).natAbs)))

theorem list_sum_eq_nsum (l : List Int) :
    (l.map Int.natAbs).sum = nsum l.length (fun j => (l.getD j 0).natAbs) := by
  induction l with
  | nil => rfl
  | cons e l ih => simp [nsum, ih]

theorem nsum_congr {S : Nat} {f g : Nat → Nat} (h : ∀ j, j < S → f j = g j) :
    nsum S f = nsum S g := by
  induction S generalizing f g with
  | zero => rfl
  | succ S ih =>
    simp only [nsum]
    rw [h 0 (by omega), ih (fun j hj => h (j + 1) (by omega))]

/-- **Exact l1 from the decoded digits.** -/
theorem kron_decode_l1 (w D : Nat) (hw : 1 ≤ w) (p : Poly) (hdeg : p.DegLt D)
    (hl1 : p.l1 < 2 ^ (w - 1)) :
    boxL1 D p = ((balDigits w (D * D * D) (uval ((2 ^ w : Nat) : Int) (p.toU D))).map Int.natAbs).sum := by
  obtain ⟨h1, h2⟩ := kron_decode w D hw p hdeg hl1
  generalize balDigits w (D * D * D) (uval ((2 ^ w : Nat) : Int) (Poly.toU D p)) = ds at h1 h2 ⊢
  rw [list_sum_eq_nsum, h1, Nat.mul_assoc, nsum_mul, nsum_mul]
  unfold boxL1
  apply nsum_congr; intro d hd
  apply nsum_congr; intro b hb
  apply nsum_congr; intro a ha
  rw [h2 a b d ha hb hd]
  rfl

end ThomsonN10.Cert.L1.KC
