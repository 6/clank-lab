import Mathlib

/-!
# Definitions (the paper, Section 2)

Everything the statements in `Main.lean` use. The proofs are in the other files of `RS16/`.

* Right side: the rows of Reiner–Sommers §3.6 in the shape both checkers accept, read as
  rational functions of `q`, and the value of a rational function at a point where it is regular.
* Left side: Armstrong's delta sequences, the Bessis–Reiner action, its fixed points, and the
  fixed-point polynomial that checker A computes (the paper, Step 2).
-/

open Polynomial

namespace RS16

/-! ## Values of rational functions -/

section Values

variable {K : Type*} [Field K]

/-- `f` is regular at `ω` with value `v`: `f = N / Q` for polynomials `N`, `Q` with `Q(ω) ≠ 0`,
and `v = N(ω) / Q(ω)`. For a polynomial `f` this says `v = f(ω)` (`hasValueAt_polynomial_iff`),
and the value is unique (`HasValueAt.unique`). -/
def HasValueAt (f : RatFunc K) (ω v : K) : Prop :=
  ∃ N Q : K[X], Q.eval ω ≠ 0 ∧
    f = algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) Q ∧ v = N.eval ω / Q.eval ω

/-- The `q`-integer `[x]_q = (1 - q^x) / (1 - q)`, a rational function of `q`
(`1 + q + ⋯ + q^(x-1)` for `x ≥ 1`). -/
noncomputable def qint (x : ℤ) : RatFunc K := (1 - RatFunc.X ^ x) / (1 - RatFunc.X)

end Values

/-! ## Rows of the §3.6 tables -/

/-- A summand `± q^(α m + β) [m + γ]_q` of a numerator sum (`neg` is the sign). -/
structure SumTerm where
  neg : Bool
  α : ℤ
  β : ℤ
  γ : ℤ

/-- The row shape both checkers accept (`shape` in `checks/check_a.py`): products of
`q^(α m + β)`, numerator brackets `[m + γ]_q` and sums `Σ ± q^(α m + β) [m + γ]_q`, divided by
products of constant brackets `[b]_q` with `b ≥ 1`. -/
inductive Row
  /-- `q^(α m + β)` -/
  | qpow (α β : ℤ)
  /-- `[m + γ]_q` -/
  | br (γ : ℤ)
  /-- `Σ ± q^(α m + β) [m + γ]_q` -/
  | sum (ts : List SumTerm)
  /-- `a · b` -/
  | mul (a b : Row)
  /-- `a / Π_{b ∈ bs} [b]_q` -/
  | div (a : Row) (bs : List ℕ+)

namespace Row

/-- The row at parameter `m`, as a rational function of `q`. -/
noncomputable def eval (K : Type*) [Field K] : Row → ℤ → RatFunc K
  | qpow α β, m => RatFunc.X ^ (α * m + β)
  | br γ, m => qint (m + γ)
  | sum ts, m =>
      (ts.map fun t => (if t.neg then -1 else 1) * RatFunc.X ^ (t.α * m + t.β) * qint (m + t.γ)).sum
  | mul a b, m => eval K a m * eval K b m
  | div a bs, m => eval K a m / (bs.map fun b : ℕ+ => qint ((b : ℕ) : ℤ)).prod

/-- Number of numerator brackets, a sum counting once (checker A's `shape`). -/
def numCount : Row → ℕ
  | qpow _ _ => 0
  | br _ => 1
  | sum _ => 1
  | mul a b => numCount a + numCount b
  | div a _ => numCount a

/-- The constant brackets of the denominators, with multiplicity (checker A's `const_brackets`). -/
def dens : Row → List ℕ+
  | qpow _ _ => []
  | br _ => []
  | sum _ => []
  | mul a b => dens a ++ dens b
  | div a bs => dens a ++ bs

/-- `[m - 1]_q` is a factor of the whole product (checker A's `has_m1_factor`). -/
def hasM1Factor : Row → Prop
  | br γ => γ = -1
  | mul a b => hasM1Factor a ∨ hasM1Factor b
  | div a _ => hasM1Factor a
  | _ => False

end Row

/-! ## Delta sequences, the action and its fixed points -/

section Action

variable {G : Type*} [Group G]

/-- The absolute order for the length `ℓ`: `x ≤ y` iff `ℓ(x) + ℓ(x⁻¹ y) = ℓ(y)`. -/
def absLE (ℓ : G → ℕ) (x y : G) : Prop := ℓ x + ℓ (x⁻¹ * y) = ℓ y

/-- `(w₀; w₁, …, w_s)` lies in Armstrong's `NC^(s)(W)`: `w₀ w₁ ⋯ w_s = c` and
`ℓ(w₀) + ℓ(w₁) + ⋯ + ℓ(w_s) = ℓ(c)`. Here `x.1 = w₀` and `x.2 i = w_{i+1}`. -/
def IsDelta (ℓ : G → ℕ) (c : G) {s : ℕ} (x : G × (Fin s → G)) : Prop :=
  x.1 * (List.ofFn x.2).prod = c ∧ ℓ x.1 + ∑ i, ℓ (x.2 i) = ℓ c

/-- The twisted rotation `ρ(w₁, …, w_s) = (c w_s c⁻¹, w₁, …, w_{s-1})`. -/
def rho (c : G) {s : ℕ} (w : Fin s → G) : Fin s → G := fun i =>
  if i.val = 0 then c * w ⟨s - 1, by have := i.isLt; omega⟩ * c⁻¹
  else w ⟨i.val - 1, by have := i.isLt; omega⟩

/-- The Bessis–Reiner generator (their (6.4)):
`φ(w₀; w₁, …, w_s) = (t w₀ t⁻¹; t, w₁, …, w_{s-1})` with `t = c w_s c⁻¹`. -/
def phi (c : G) {s : ℕ} (x : G × (Fin s → G)) : G × (Fin s → G) :=
  if h : 0 < s then
    (rho c x.2 ⟨0, h⟩ * x.1 * (rho c x.2 ⟨0, h⟩)⁻¹, rho c x.2)
  else x

/-- The number of `x ∈ NC^(s)(W)` fixed by `φ^k` whose bottom element `w₀` has class `X`. -/
noncomputable def fixCount {α : Type*} (ℓ : G → ℕ) (c : G) (cls : G → α) (s k : ℕ) (X : α) : ℕ :=
  Nat.card {x : G × (Fin s → G) // IsDelta ℓ c x ∧ (phi c)^[k] x = x ∧ cls x.1 = X}

/-! ## The fixed-point polynomial (the paper, Step 2; checker A, "left side") -/

variable [Fintype G] [DecidableEq G]

open scoped Classical in
/-- `NC(W) ∩ C`, with `C` the centralizer of `c^{h₁}`. -/
noncomputable def ncC (ℓ : G → ℕ) (c : G) (h1 : ℕ) : Finset G :=
  Finset.univ.filter fun u => absLE ℓ u c ∧ Commute u (c ^ h1)

open scoped Classical in
/-- `chains k u`: the number of strict chains `e = z₀ < z₁ < ⋯ < z_k = u` with every `z_i` in
`NC(W) ∩ C`, by checker A's recursion. -/
noncomputable def chains (ℓ : G → ℕ) (c : G) (h1 : ℕ) : ℕ → G → ℕ
  | 0, u => if u = 1 then 1 else 0
  | k + 1, u => ∑ z ∈ (ncC ℓ c h1).filter (fun z => z ≠ u ∧ absLE ℓ z u), chains ℓ c h1 k z

/-- `w₀(u) = c (u₁ u₂ ⋯ u_{ν})⁻¹` with `u_j = c^{e_j} u c^{-e_j}` (blocks `j = 0, …, ν - 1`). -/
def bottom (c : G) (ν : ℕ) (e : ℕ → ℕ) (u : G) : G :=
  c * (List.ofFn fun j : Fin ν => c ^ e j * u * (c ^ e j)⁻¹).prod⁻¹

open scoped Classical in
/-- `U_X(h₁, ν)`: the `u ∈ NC(W) ∩ C` with `ℓ(w₀(u)) + ν ℓ(u) = ℓ(c)` and `[w₀(u)] = X`. -/
noncomputable def Uset {α : Type*} (ℓ : G → ℕ) (c : G) (cls : G → α) (h1 ν : ℕ) (e : ℕ → ℕ)
    (X : α) : Finset G :=
  (ncC ℓ c h1).filter fun u => ℓ (bottom c ν e u) + ν * ℓ u = ℓ c ∧ cls (bottom c ν e u) = X

/-- The left side `L_X(m₁) = Σ_{k ≤ ℓ(c)} binom(m₁, k) Σ_{u ∈ U_X(h₁, ν)} c_k(u)`. -/
noncomputable def Lval {α : Type*} (ℓ : G → ℕ) (c : G) (cls : G → α) (h1 ν : ℕ) (e : ℕ → ℕ)
    (X : α) (m1 : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (ℓ c + 1), m1.choose k * ∑ u ∈ Uset ℓ c cls h1 ν e X, chains ℓ c h1 k u

end Action

end RS16
