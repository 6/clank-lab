import RS16

/-!
# Reiner–Sommers Conjecture 1.4: the reduction to finite checks (the paper, Steps 1–4)

The definitions are in `RS16/Defs.lean`. Each theorem below is stated for an arbitrary finite
group `G` with a length `ℓ` (reflection length in the Weyl group), an element `c` (the Coxeter
element) and a class map `cls` (`w ↦` the `W`-orbit of `V^w`), and for rows of the §3.6 shape
read as rational functions over any field `K` of characteristic `0`.

* `step2_fixed_points`: the number of delta sequences fixed by `φ^p` with bottom class `X` is
  checker A's polynomial `L_X(m₁)` (the paper, Step 2).
* `step2_large_m2`: for `ν > ℓ(c)` that polynomial is `[X = [c]]` (Step 2, "Large ν").
* `step3_rows`: agreement at `m₁ = 1, …, n + 1` of a row with such a polynomial gives agreement,
  and regularity at `ω`, for every `m₁ ≥ 1` (Steps 3 and 4).
* `rows_with_m1_factor`: the structural large-`ν` argument (Step 4).
* `conjecture_1_4`: everything together. Its hypotheses are exactly the facts the checkers verify;
  its conclusion is Conjecture 1.4 for every `s ≥ 1`, every element of `Z/shZ` and every class.
-/

open Polynomial

namespace RS16.Main

open RS16

/-- A polynomial is regular everywhere, and its value in the sense of `HasValueAt` is its
evaluation. -/
theorem value_of_polynomial {K : Type*} [Field K] (p : K[X]) (ω v : K) :
    HasValueAt (algebraMap K[X] (RatFunc K) p) ω v ↔ v = p.eval ω :=
  hasValueAt_polynomial_iff p ω v

/-- The value is unique. -/
theorem value_unique {K : Type*} [Field K] {f : RatFunc K} {ω v v' : K} (h : HasValueAt f ω v)
    (h' : HasValueAt f ω v') : v = v' :=
  h.unique h'

/-- Checker A's last step: an integer polynomial congruent to the constant `v` modulo the `d`-th
cyclotomic polynomial has value `v` at every primitive `d`-th root of unity. -/
theorem checker_value {K : Type*} [Field K] [CharZero K] (F G : ℤ[X]) (v : ℤ) {d : ℕ}
    (hd : 0 < d) (hF : F = C v + cyclotomic d ℤ * G) {ω : K} (hω : IsPrimitiveRoot ω d) :
    HasValueAt (algebraMap K[X] (RatFunc K) (F.map (Int.castRingHom K))) ω v := by
  rw [hasValueAt_polynomial_iff]
  have hr : (cyclotomic d K).IsRoot ω := (isRoot_cyclotomic_iff_charZero hd).mpr hω
  rw [hF, Polynomial.map_add, Polynomial.map_mul, map_cyclotomic, eval_add, eval_mul, hr.eq_zero]
  simp

/-- Checker A's exponents: the loop `e ← e + a + [wrap]`, `j ← j + b - ν [wrap]` with
`h₁ = a ν + b`, started at `(j, e) = (0, 0)`, keeps `h₁ ∣ ν e + j`. -/
theorem checker_exponents (h1 ν j x : ℕ) (hinv : (h1 : ℤ) ∣ ν * x + j) :
    if j + h1 % ν < ν then (h1 : ℤ) ∣ ν * (x + h1 / ν) + (j + h1 % ν : ℕ)
    else (h1 : ℤ) ∣ ν * (x + h1 / ν + 1) + (j + h1 % ν - ν : ℕ) := by
  have hab : (ν : ℤ) * ((h1 : ℤ) / ν) + (h1 : ℤ) % ν = h1 := Int.mul_ediv_add_emod _ _
  split_ifs with hw
  · have : (ν : ℤ) * ((x + h1 / ν : ℕ) : ℤ) + ((j + h1 % ν : ℕ) : ℤ) = (ν * x + j) + h1 := by
      push_cast; linear_combination hab
    push_cast at this ⊢
    rw [this]; exact dvd_add hinv dvd_rfl
  · have : (ν : ℤ) * ((x + h1 / ν + 1 : ℕ) : ℤ) + ((j + h1 % ν - ν : ℕ) : ℤ) =
        (ν * x + j) + h1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; linear_combination hab
    push_cast [Nat.cast_sub (show ν ≤ j + h1 % ν by omega)] at this ⊢
    rw [this]; exact dvd_add hinv dvd_rfl

/-- Exponents as in `step2_fixed_points` exist for every coprime `(h₁, ν)`. -/
theorem exists_exponents (h1 ν : ℕ) (hcop : Nat.Coprime h1 ν) :
    ∃ e : ℕ → ℕ, ∀ j, j < ν → (h1 : ℤ) ∣ ν * e j + j := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  -- `u h₁ + v ν = 1`; take `e_j = (-v j) mod h₁`
  refine ⟨fun j => ((-v * j) % (h1 : ℤ)).toNat, fun j _ => ?_⟩
  rcases Nat.eq_zero_or_pos h1 with h0 | hpos
  · subst h0
    have : ν = 1 := by simpa using hcop
    subst this
    have : j = 0 := by omega
    subst this
    simp
  · have hnn := Int.emod_nonneg (-v * j) (by omega : (h1 : ℤ) ≠ 0)
    rw [Int.toNat_of_nonneg hnn]
    have hm := Int.emod_add_ediv_mul (-v * j) h1
    have : (ν : ℤ) * ((-v * j) % h1) + j = h1 * (j * u - ν * ((-v * j) / h1)) := by
      linear_combination (ν : ℤ) * hm - (j : ℤ) * huv
    rw [this]
    exact Dvd.intro _ rfl

/-- The paper, Step 2. For `s = ν m₁`, `p = h₁ m₁` with `gcd(h₁, ν) = 1` and exponents
`e_j` with `h₁ ∣ ν e_j + j` (`j < ν`), the delta sequences fixed by `φ^p` whose bottom element
has class `X` number `L_X(m₁) = Σ_{k ≤ ℓ(c)} binom(m₁, k) Σ_{u ∈ U_X(h₁, ν)} c_k(u)`. -/
theorem step2_fixed_points {G : Type*} [Group G] [Fintype G] [DecidableEq G] {α : Type*}
    (ℓ : G → ℕ) (c : G) (cls : G → α)
    (hmul : ∀ x y, ℓ (x * y) ≤ ℓ x + ℓ y) (hconj : ∀ g x, ℓ (g * x * g⁻¹) = ℓ x)
    (hzero : ∀ x, ℓ x = 0 ↔ x = 1)
    {m1 ν h1 : ℕ} (hm1 : 0 < m1) (hν : 0 < ν) (hcop : Nat.Coprime h1 ν)
    (e : ℕ → ℕ) (he : ∀ j, j < ν → (h1 : ℤ) ∣ ν * e j + j) (X : α) :
    fixCount ℓ c cls (ν * m1) (h1 * m1) X = Lval ℓ c cls h1 ν e X m1 :=
  fixCount_eq_Lval c ⟨hmul, hconj, hzero⟩ cls hm1 hν hcop e he X

open scoped Classical in
/-- The paper, Step 2, "Large ν": for `ν > ℓ(c)`, `L_X(m₁) = [X = [c]]`. -/
theorem step2_large_m2 {G : Type*} [Group G] [Fintype G] [DecidableEq G] {α : Type*}
    (ℓ : G → ℕ) (c : G) (cls : G → α)
    (hmul : ∀ x y, ℓ (x * y) ≤ ℓ x + ℓ y) (hconj : ∀ g x, ℓ (g * x * g⁻¹) = ℓ x)
    (hzero : ∀ x, ℓ x = 0 ↔ x = 1)
    {m1 ν h1 : ℕ} (hν : ℓ c < ν) (e : ℕ → ℕ) (X : α) :
    Lval ℓ c cls h1 ν e X m1 = if cls c = X then 1 else 0 :=
  Lval_large c ⟨hmul, hconj, hzero⟩ cls hν e X

/-- The paper, Steps 3 and 4. A row with at most `n` numerator and at most `n` denominator
brackets, at `m = E m₁ + 1` with `d ∣ E`, that is regular at a primitive `d`-th root of unity `ω`
with value `Σ_{j ≤ n} binom(m₁, j) a_j` for `m₁ = 1, …, n + 1`, is so for every `m₁ ≥ 1`. -/
theorem step3_rows {K : Type*} [Field K] [CharZero K] (row : Row) (n d E : ℕ) {ω : K}
    (hd : 0 < d) (hω : IsPrimitiveRoot ω d) (hdE : d ∣ E)
    (hnum : row.numCount ≤ n) (hden : row.dens.length ≤ n) (a : ℕ → K)
    (h : ∀ m1 : ℕ, 1 ≤ m1 → m1 ≤ n + 1 → HasValueAt (row.eval K (E * m1 + 1)) ω
      (∑ j ∈ Finset.range (n + 1), (m1.choose j : K) * a j)) :
    ∀ m1 : ℕ, 1 ≤ m1 → HasValueAt (row.eval K (E * m1 + 1)) ω
      (∑ j ∈ Finset.range (n + 1), (m1.choose j : K) * a j) :=
  step3 row n d E hd hω hdE hnum hden a h

/-- The paper, Step 4, `d > b_max`: a row with a factor `[m - 1]_q` and no denominator
bracket vanishing at `ω ≠ 1` has value `0` at `ω` when `ω^(m-1) = 1`. -/
theorem rows_with_m1_factor {K : Type*} [Field K] [CharZero K] (row : Row) {ω : K} (m : ℤ)
    (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) (hm : ω ^ (m - 1) = 1) (hrow : row.hasM1Factor)
    (hb : ∀ b ∈ row.dens, ω ^ (b : ℕ) ≠ 1) :
    HasValueAt (row.eval K m) ω 0 :=
  row_m1 hω0 hω1 hm row hrow hb

/-- The length hypotheses hold for checker A's `ℓ(w) = rank(w - 1)` on any group `W` of
invertible matrices over a field (the Weyl group in its root-lattice representation). -/
theorem reflection_length {K : Type*} [Field K] {n : ℕ} (W : Subgroup (Matrix (Fin n) (Fin n) K)ˣ) :
    (∀ x y : W, rankLen ((x * y : W) : (Matrix (Fin n) (Fin n) K)ˣ) ≤
        rankLen (x : (Matrix (Fin n) (Fin n) K)ˣ) + rankLen (y : (Matrix (Fin n) (Fin n) K)ˣ)) ∧
      (∀ g x : W, rankLen ((g * x * g⁻¹ : W) : (Matrix (Fin n) (Fin n) K)ˣ) =
        rankLen (x : (Matrix (Fin n) (Fin n) K)ˣ)) ∧
      (∀ x : W, rankLen (x : (Matrix (Fin n) (Fin n) K)ˣ) = 0 ↔ x = 1) :=
  ⟨fun x y => rankLen_mul _ _, fun g x => rankLen_conj _ _, fun x => by
    rw [rankLen_eq_zero]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩⟩

open scoped Classical in
/-- **Reiner–Sommers Conjecture 1.4** from the checked facts. `G`, `ℓ`, `c`, `h`, `cls` are the
Weyl group, reflection length, Coxeter element, Coxeter number and `w ↦ [V^w]`; `rows X` is the
§3.6 row of the class `X`; `e h₁ ν` are checker A's block exponents. The hypotheses after the
first line are what the checkers verify (lean/README.md):
* `hnum`, `hden`: the row shape counts;
* `hid`: the identities for `h₁ ∣ h`, `1 ≤ ν ≤ n`, `gcd(h₁, ν) = 1`, `m₁ = 1, …, n + 1`;
* `hreg`, `hm1f`, `hbmax`: the regular row, the `[m - 1]` factors, the largest denominator;
* `hlarge`: the values `[X = [c]]` for `ν > n` and `d ≤ b_max`, `m₁ = 1, …, n + 1`.
Conclusion: for every `s ≥ 1`, every `k ∈ Z/shZ` of order `d` and every class `X`, the row of `X`
at `m = sh + 1` is regular at every primitive `d`-th root of unity `ω` with value the number of
`x ∈ NC^(s)(W)` fixed by `φ^k` whose bottom element has class `X`. -/
theorem conjecture_1_4 {K : Type*} [Field K] [CharZero K]
    {G : Type*} [Group G] [Fintype G] [DecidableEq G] {α : Type*}
    (ℓ : G → ℕ) (c : G) (h : ℕ) (cls : G → α) (rows : α → Row) (e : ℕ → ℕ → ℕ → ℕ)
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
      HasValueAt ((rows X).eval K (s * h + 1)) ω (fixCount ℓ c cls s k.val X) :=
  assemble ℓ c h cls rows e hmul hconj hzero hn hh hch he hnum hden hid hreg hm1f bmax hbmax hlarge

end RS16.Main
