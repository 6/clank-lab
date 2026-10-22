import Mathlib

/-!
# Definitions for the Main Lemma of the proof of Elgin–Reading–Stella Conjecture 13

Plain-English glosses are in each docstring. Variable `0` is `u`, variable `1` is `w`.
-/

noncomputable section

namespace ErsConj13

open MvPowerSeries

/-- `A = ℚ⟦u,w⟧`, formal power series in two commuting variables `u` (index 0) and `w`
(index 1) over `ℚ`. -/
abbrev A := MvPowerSeries (Fin 2) ℚ

/-- The variable `u`. -/
abbrev u : A := X 0

/-- The variable `w`. -/
abbrev w : A := X 1

/-- `zd i` is the operator `z_i ∂/∂z_i`: `zd 0 = u ∂_u`, `zd 1 = w ∂_w`. It multiplies the
coefficient of `u^p w^q` by `p` (for `i = 0`) or by `q` (for `i = 1`). -/
def zd (i : Fin 2) (f : A) : A := fun e => (e i : ℚ) * coeff e f

/-- The Poisson bracket `{f, g} = (u∂_u f)(w∂_w g) − (w∂_w f)(u∂_u g)`. On monomials it is
`{z^a, z^b} = ω(a,b) z^{a+b}` with `ω(a,b) = a₁b₂ − a₂b₁` (here `z^a = u^{a₁} w^{a₂}`), and this
formula is its (unique) continuous bilinear extension to all of `A`. -/
def bracket (f g : A) : A := zd 0 f * zd 1 g - zd 1 f * zd 0 g

/-- The `h`-degree `h(u^p w^q) = q − p` of an exponent `e = (p, q)`. -/
def hdeg (e : Fin 2 →₀ ℕ) : ℤ := (e 1 : ℤ) - (e 0 : ℤ)

/-- `𝒪_{h ≥ k}`: the series all of whose monomials with nonzero coefficient have `h ≥ k`
(the closed span of the monomials with `h ≥ k`). -/
def OGe (k : ℤ) : Set A := {f | ∀ e, coeff e f ≠ 0 → k ≤ hdeg e}

/-- `𝒪_{h ≤ k}`: the series all of whose monomials with nonzero coefficient have `h ≤ k`. -/
def OLe (k : ℤ) : Set A := {f | ∀ e, coeff e f ≠ 0 → hdeg e ≤ k}

/-- `diag F = F(uw) = Σ_k F_k u^k w^k` for a one-variable series `F = Σ_k F_k t^k`. -/
def diag (F : PowerSeries ℚ) : A :=
  fun e => if e 0 = e 1 then PowerSeries.coeff (e 0) F else 0

/-- `ersCoeff j = (1/j) Σ_{ℓ=0}^{j+1} C(ℓ, j+1−ℓ) · C(j+ℓ−1, ℓ)`, the conjectured
`τ^{1,5}(2j,j)` (for `j ≥ 1`; terms with `ℓ < ⌈(j+1)/2⌉` vanish because `C(ℓ, j+1−ℓ) = 0`).
All subtractions are of naturals that cannot truncate for `j ≥ 1` and `ℓ ≤ j + 1`. -/
def ersCoeff (j : ℕ) : ℚ :=
  (1 / (j : ℚ)) * ∑ ℓ ∈ Finset.range (j + 2),
    ((Nat.choose ℓ (j + 1 - ℓ) * Nat.choose (j + ℓ - 1) ℓ : ℕ) : ℚ)

/-- `S = 1 + Σ_{j≥1} a_j t^j` with `a_j = ersCoeff j`. -/
def S : PowerSeries ℚ := PowerSeries.mk fun j => if j = 0 then 1 else ersCoeff j

end ErsConj13
