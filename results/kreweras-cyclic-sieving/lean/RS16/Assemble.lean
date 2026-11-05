import RS16.Count
import RS16.Interp

/-!
# Assembly (the paper, Steps 1 and 4)

Step 1: an element of order `d` of `Z/shZ` has the fixed points of `φ^p`, `p = sh/d`
(`fixCount_order`), and `(s, p)` gives `(h₁, ν, m₁)` with `s = ν m₁`, `p = h₁ m₁`,
`gcd(h₁, ν) = 1`, `h₁ ∣ h` and `d = ν h / h₁`. Step 4 then combines Step 2, Step 3 and the
large-`ν` argument.
-/

open scoped Classical

set_option linter.unusedSectionVars false

namespace RS16

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- `φ^{s h}` fixes every delta sequence when `c^h = 1`. -/
lemma phi_iter_sh {ℓ : G → ℕ} (hl : LenHyp ℓ) (c : G) {s h : ℕ} (hs : 0 < s) (hch : c ^ h = 1)
    {x : G × (Fin s → G)} (hx : IsDelta ℓ c x) : (phi c)^[s * h] x = x :=
  (phi_iter_fixed_iff c hl hs _ hx).mpr (rho_iter_sh c hs hch x.2)

/-- Step 1: fixed points of `φ^k` are those of `φ^{gcd(k, sh)}`. -/
lemma fixCount_gcd {ℓ : G → ℕ} (hl : LenHyp ℓ) (c : G) {α : Type*} (cls : G → α) {s h : ℕ}
    (hs : 0 < s) (hch : c ^ h = 1) (k : ℕ) (X : α) :
    fixCount ℓ c cls s k X = fixCount ℓ c cls s (Nat.gcd (s * h) k) X := by
  unfold fixCount
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  constructor
  · rintro ⟨hx, hk, hX⟩
    refine ⟨hx, ?_, hX⟩
    have h1 : Function.IsPeriodicPt (phi c) (s * h) x := phi_iter_sh hl c hs hch hx
    have h2 : Function.IsPeriodicPt (phi c) k x := hk
    exact h1.gcd h2
  · rintro ⟨hx, hk, hX⟩
    refine ⟨hx, ?_, hX⟩
    obtain ⟨t, ht⟩ := Nat.gcd_dvd_right (s * h) k
    have h1 : Function.IsPeriodicPt (phi c) (Nat.gcd (s * h) k) x := hk
    have := h1.mul_const t
    rw [← ht] at this
    exact this

variable {K : Type*} [Field K] [CharZero K]

/-- The whole claim, from the checked facts (see `Main.lean` for the statement). -/
theorem assemble {α : Type*} (ℓ : G → ℕ) (c : G) (h : ℕ) (cls : G → α) (rows : α → Row)
    (e : ℕ → ℕ → ℕ → ℕ)
    (hmul : ∀ x y, ℓ (x * y) ≤ ℓ x + ℓ y) (hconj : ∀ g x, ℓ (g * x * g⁻¹) = ℓ x)
    (hzero : ∀ x, ℓ x = 0 ↔ x = 1) (hn : 0 < ℓ c) (hh : 0 < h) (hch : c ^ h = 1)
    (he : ∀ h1 ν j : ℕ, Nat.Coprime h1 ν → j < ν → (h1 : ℤ) ∣ ν * e h1 ν j + j)
    (hnum : ∀ X, (rows X).numCount ≤ ℓ c) (hden : ∀ X, (rows X).dens.length ≤ ℓ c)
    (hid : ∀ (h1 ν m1 : ℕ) (X : α) (ω : K), h1 ∣ h → 1 ≤ ν → ν ≤ ℓ c → Nat.Coprime h1 ν →
      1 ≤ m1 → m1 ≤ ℓ c + 1 → IsPrimitiveRoot ω (ν * h / h1) →
      HasValueAt ((rows X).eval K (m1 * ν * h + 1)) ω (Lval ℓ c cls h1 ν (e h1 ν) X m1))
    (hreg : rows (cls c) = .qpow (ℓ c) (-(ℓ c : ℤ)))
    (hm1f : ∀ X, X ≠ cls c → (rows X).hasM1Factor)
    (bmax : ℕ) (hbmax : ∀ X, ∀ b ∈ (rows X).dens, (b : ℕ) ≤ bmax)
    (hlarge : ∀ (h1 ν m1 : ℕ) (X : α) (ω : K), h1 ∣ h → ℓ c < ν → Nat.Coprime h1 ν →
      ν * (h / h1) ≤ bmax → 1 ≤ m1 → m1 ≤ ℓ c + 1 → IsPrimitiveRoot ω (ν * h / h1) →
      HasValueAt ((rows X).eval K (m1 * ν * h + 1)) ω (if X = cls c then 1 else 0)) :
    ∀ (s : ℕ), 1 ≤ s → ∀ (d : ℕ) (k : ZMod (s * h)), addOrderOf k = d → ∀ (X : α) (ω : K),
      IsPrimitiveRoot ω d →
      HasValueAt ((rows X).eval K (s * h + 1)) ω (fixCount ℓ c cls s k.val X) := by
  intro s hs d k hk X ω hω
  have hl : LenHyp ℓ := ⟨hmul, hconj, hzero⟩
  have hN : 0 < s * h := Nat.mul_pos hs hh
  have : NeZero (s * h) := ⟨hN.ne'⟩
  -- Step 1: `p = gcd(sh, k) = sh / d`
  set p := Nat.gcd (s * h) k.val with hp
  rw [fixCount_gcd hl c cls hs hch k.val X, ← hp]
  have hd : d = s * h / p := by
    rw [← hk, ← ZMod.natCast_zmod_val k, ZMod.addOrderOf_coe _ hN.ne']
  have hp0 : 0 < p := Nat.gcd_pos_of_pos_left _ hN
  have hpN : p ∣ s * h := Nat.gcd_dvd_left _ _
  have hdp : d * p = s * h := by rw [hd]; exact Nat.div_mul_cancel hpN
  set m1 := Nat.gcd p s with hm1def
  set ν := s / m1
  set h1 := p / m1
  have hm1 : 0 < m1 := Nat.gcd_pos_of_pos_right _ hs
  have hsm : s = ν * m1 := (Nat.div_mul_cancel (Nat.gcd_dvd_right p s)).symm
  have hpm : p = h1 * m1 := (Nat.div_mul_cancel (Nat.gcd_dvd_left p s)).symm
  have hν : 0 < ν := Nat.pos_of_ne_zero fun h0 => by rw [h0, zero_mul] at hsm; omega
  have hcop : Nat.Coprime h1 ν := Nat.coprime_div_gcd_div_gcd hm1
  have hdh : d * h1 = ν * h := by
    have : d * h1 * m1 = ν * h * m1 := by
      rw [mul_assoc, ← hpm, hdp, hsm]; ring
    exact Nat.eq_of_mul_eq_mul_right hm1 this
  have hh1 : h1 ∣ h := hcop.dvd_of_dvd_mul_left ⟨d, by rw [← hdh, mul_comm]⟩
  have hh10 : 0 < h1 := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_mul] at hpm; omega
  have hd' : ν * h / h1 = d := by rw [← hdh, Nat.mul_div_cancel _ hh10]
  have hd0 : 0 < d := Nat.pos_of_ne_zero fun h0 => by rw [h0, zero_mul] at hdp; omega
  -- Step 2
  rw [hpm, hsm] at *
  rw [fixCount_eq_Lval c hl cls hm1 hν hcop (e h1 ν) (fun j => he h1 ν j hcop) X]
  -- the row at `m = (ν h) m₁ + 1`
  have hE : ((ν * m1 * h + 1 : ℕ) : ℤ) = ((ν * h : ℕ) : ℤ) * (m1 : ℤ) + 1 := by push_cast; ring
  have hdE : d ∣ ν * h := ⟨h1, by rw [← hdh]⟩
  have hrow : ∀ m1' : ℕ, (m1' : ℤ) * (ν : ℤ) * (h : ℤ) + 1 = ((ν * h : ℕ) : ℤ) * (m1' : ℤ) + 1 := by
    intro m1'; push_cast; ring
  rw [show ((ν * m1 : ℕ) : ℤ) * (h : ℤ) + 1 = ((ν * h : ℕ) : ℤ) * (m1 : ℤ) + 1 by push_cast; ring]
  by_cases hsmall : ν ≤ ℓ c
  · -- Step 3 with the binomial coefficients `Σ_{u ∈ U_X} c_j(u)`
    have := step3 (rows X) (ℓ c) d (ν * h) hd0 hω hdE (hnum X) (hden X)
      (fun j => ((∑ u ∈ Uset ℓ c cls h1 ν (e h1 ν) X, chains ℓ c h1 j u : ℕ) : K)) (by
        intro m1' h1' h2'
        have := hid h1 ν m1' X ω hh1 hν hsmall hcop h1' h2' (hd' ▸ hω)
        rw [hrow m1'] at this
        convert this using 1
        simp [Lval]) m1 hm1
    convert this using 1
    simp [Lval]
  · replace hsmall := not_le.mp hsmall
    rw [Lval_large c hl cls hsmall]
    have hval : ((if cls c = X then 1 else 0 : ℕ) : K) = if X = cls c then 1 else 0 := by
      by_cases hX : X = cls c <;> simp [hX, eq_comm]
    rw [hval]
    by_cases hbig : ν * (h / h1) ≤ bmax
    · have := step3 (rows X) (ℓ c) d (ν * h) hd0 hω hdE (hnum X) (hden X)
        (fun j => if j = 0 then (if X = cls c then 1 else 0) else 0) (by
          intro m1' h1' h2'
          have := hlarge h1 ν m1' X ω hh1 hsmall hcop hbig h1' h2' (hd' ▸ hω)
          rw [hrow m1'] at this
          convert this using 1
          simp [Finset.sum_ite_eq']) m1 hm1
      convert this using 1
      simp [Finset.sum_ite_eq']
    · replace hbig := not_le.mp hbig
      -- `d > b_max`: no denominator vanishes, `[m - 1]_q` does
      have hdb : bmax < d := by
        rw [← hd', Nat.mul_div_assoc _ hh1]; exact hbig
      have hω0 : ω ≠ 0 := hω.ne_zero hd0.ne'
      have hd2 : 2 ≤ d := by
        have : ν ≤ d := by
          rw [← hd', Nat.mul_div_assoc _ hh1]
          exact Nat.le_mul_of_pos_right _ (Nat.div_pos (Nat.le_of_dvd hh hh1) hh10)
        omega
      have hω1 : ω ≠ 1 := fun h1' => by
        rw [h1'] at hω
        have := IsPrimitiveRoot.one_left_iff.mp hω
        omega
      have hωE : ω ^ (ν * h * m1) = 1 := by
        rw [(hω.pow_eq_one_iff_dvd _)]
        exact Dvd.dvd.mul_right hdE _
      by_cases hX : X = cls c
      · subst hX
        rw [hreg]; simp only [↓reduceIte]
        simp only [Row.eval]
        have := hasValueAt_X_zpow (K := K) hω0
          ((ℓ c : ℤ) * (((ν * h : ℕ) : ℤ) * (m1 : ℤ) + 1) + -(ℓ c : ℤ))
        convert this using 1
        rw [show (ℓ c : ℤ) * (((ν * h : ℕ) : ℤ) * (m1 : ℤ) + 1) + -(ℓ c : ℤ) =
          (((ν * h * m1 : ℕ) : ℤ)) * (ℓ c : ℤ) by push_cast; ring, zpow_mul]
        simp only [zpow_natCast, hωE, one_pow]
      · simp only [hX, ↓reduceIte]
        apply row_m1 hω0 hω1 _ (rows X) (hm1f X hX)
        · intro b hb hb1
          have := (hω.pow_eq_one_iff_dvd _).mp hb1
          have := Nat.le_of_dvd b.pos this
          have := hbmax X b hb
          omega
        · rw [show ((ν * h : ℕ) : ℤ) * (m1 : ℤ) + 1 - 1 = ((ν * h * m1 : ℕ) : ℤ) by push_cast; ring,
            zpow_natCast, hωE]

end RS16
