import Mathlib

/-!
# Definitions for the 1-1-1 ABC KPP speed-up claim

Everything the top-level statement `ABC.abc_kpp_linear_speedup` and the cited axiom
`ABC.Zlatos2010.theorem_1_1` mention is defined here, from Mathlib only.

Conventions, following Zlatoš, ARMA 195 (2010) (arXiv:0704.1163v2), quoted in
`ABC/Cited/Zlatos.lean`:
* `E n` is `ℝⁿ` with the Euclidean inner product and Lebesgue measure.
* A function on the torus `ℝⁿ / LℤⁿZ` is an `L`-periodic function on `ℝⁿ`; integrals over
  the torus are integrals over the cell `[0, L)ⁿ`.
* `f` is only defined on `[0, 1]` in the source, so a solution takes values in `[0, 1]`.
-/

open MeasureTheory Filter Topology InnerProductSpace Laplacian
open scoped RealInnerProductSpace

noncomputable section

namespace ABC

/-- `ℝⁿ` with its Euclidean structure. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The `i`-th standard basis vector. -/
abbrev ev {n : ℕ} (i : Fin n) : E n := EuclideanSpace.single i 1

/-- `g` is `L`-periodic in each coordinate direction (hence under `Lℤⁿ`). -/
def Periodic {n : ℕ} {β : Type*} (L : ℝ) (g : E n → β) : Prop :=
  ∀ (i : Fin n) (x : E n), g (x + L • ev i) = g x

/-- The period cell `[0, L)ⁿ`. -/
def cell (n : ℕ) (L : ℝ) : Set (E n) := {x | ∀ i, x i ∈ Set.Ico 0 L}

/-- The 1-1-1 ABC field `V(x, y, z) = (sin z + cos y, sin x + cos z, sin y + cos x)`. -/
def abcField (ξ : E 3) : E 3 :=
  !₂[Real.sin (ξ 2) + Real.cos (ξ 1), Real.sin (ξ 0) + Real.cos (ξ 2),
     Real.sin (ξ 1) + Real.cos (ξ 0)]

/-- Zlatoš (1.2): `f ∈ C^{1,ε}([0,1])`, `f(0) = f(1) = 0`, `f` non-increasing on `(1-ε, 1)`
for some `ε > 0`, and `0 < f(s) ≤ s f′(0)` for `s ∈ (0,1)`. The Hölder exponent is taken in
`(0, 1]`, as usual for `C^{1,ε}`; `f′` is the derivative within `[0,1]` (one-sided at `0`). -/
def ZlatosKPP (f : ℝ → ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
    ContDiffOn ℝ 1 f (Set.Icc 0 1) ∧
    (∃ C : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |derivWithin f (Set.Icc 0 1) s - derivWithin f (Set.Icc 0 1) t| ≤ C * |s - t| ^ ε) ∧
    f 0 = 0 ∧ f 1 = 0 ∧
    AntitoneOn f (Set.Ioo (1 - ε) 1) ∧
    ∀ s ∈ Set.Ioo (0 : ℝ) 1, 0 < f s ∧ f s ≤ s * derivWithin f (Set.Icc 0 1) 0

/-- `f′(0)`, the derivative of `f` at `0` within `[0, 1]`. -/
def fderiv0 (f : ℝ → ℝ) : ℝ := derivWithin f (Set.Icc 0 1) 0

/-- Divergence of a vector field on `ℝⁿ`. -/
def divergence {n : ℕ} (u : E n → E n) (x : E n) : ℝ := ∑ i, fderiv ℝ u x (ev i) i

/-- Zlatoš (1.3), for an `L`-periodic flow: `u ∈ C^{1,ε}(Tⁿ)`, `∇·u ≡ 0`, `∫_{Tⁿ} u = 0`. -/
def ZlatosFlow {n : ℕ} (L : ℝ) (u : E n → E n) : Prop :=
  Periodic L u ∧ ContDiff ℝ 1 u ∧
    (∃ ε C : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ x y, ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ C * ‖x - y‖ ^ ε) ∧
    (∀ x, divergence u x = 0) ∧
    ∫ x in cell n L, u x = 0

/-- A classical solution of `T_t + A u·∇T = ΔT + f(T)` on `ℝ × ℝⁿ` (Zlatoš (1.1)) with values
in `[0, 1]`: `T`, `T_t`, `∇T` and `D²T` exist and are jointly continuous. -/
def IsClassicalSolution {n : ℕ} (u : E n → E n) (f : ℝ → ℝ) (A : ℝ) (T : ℝ → E n → ℝ) :
    Prop :=
  (∀ t x, T t x ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ x, Differentiable ℝ (fun t => T t x)) ∧
  (∀ t, ContDiff ℝ 2 (T t)) ∧
  Continuous (fun p : ℝ × E n => T p.1 p.2) ∧
  Continuous (fun p : ℝ × E n => deriv (fun s => T s p.2) p.1) ∧
  Continuous (fun p : ℝ × E n => fderiv ℝ (T p.1) p.2) ∧
  Continuous (fun p : ℝ × E n => iteratedFDeriv ℝ 2 (T p.1) p.2) ∧
  ∀ t x, deriv (fun s => T s x) t + A * ⟪u x, gradient (T t) x⟫ = Δ (T t) x + f (T t x)

/-- A pulsating front in direction `e` with speed `c` (Zlatoš, after (1.3), for period `L`):
a solution of the form `T(t,x) = U(x·e − ct, x)`, `U` `L`-periodic in `x`,
`U(s, x) → 1` as `s → −∞` and `U(s, x) → 0` as `s → +∞`, uniformly in `x`. -/
def IsPulsatingFront {n : ℕ} (L : ℝ) (u : E n → E n) (f : ℝ → ℝ) (A : ℝ) (e : E n) (c : ℝ)
    (T : ℝ → E n → ℝ) : Prop :=
  IsClassicalSolution u f A T ∧
  ∃ U : ℝ → E n → ℝ,
    (∀ t x, T t x = U (⟪x, e⟫ - c * t) x) ∧
    (∀ s, Periodic L (U s)) ∧
    TendstoUniformly U (fun _ => (1 : ℝ)) atBot ∧
    TendstoUniformly U (fun _ => (0 : ℝ)) atTop

/-- The minimal pulsating front speed `c*_e(A)`: in the KPP case fronts exist precisely for
`c ≥ c*_e(A)` (Zlatoš, citing Berestycki–Hamel), so it is the infimum of the front speeds. -/
def cstar {n : ℕ} (L : ℝ) (u : E n → E n) (f : ℝ → ℝ) (e : E n) (A : ℝ) : ℝ :=
  sInf {c | ∃ T, IsPulsatingFront L u f A e c T}

/-- `g` is a weak gradient of `w` on `ℝⁿ`: both locally integrable and
`∫ w ∂ᵢφ = −∫ gᵢ φ` for every smooth compactly supported `φ`. -/
def IsWeakGradient {n : ℕ} (w : E n → ℝ) (g : E n → E n) : Prop :=
  LocallyIntegrable w ∧ LocallyIntegrable g ∧
    ∀ φ : E n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → ∀ i : Fin n,
      ∫ x, w x * fderiv ℝ φ x (ev i) = - ∫ x, g x i * φ x

/-- `w ∈ H¹(Tⁿ)` (real-valued, period `L`) with weak gradient `g`. -/
def IsH1Torus {n : ℕ} (L : ℝ) (w : E n → ℝ) (g : E n → E n) : Prop :=
  Periodic L w ∧ IsWeakGradient w g ∧
    MemLp w 2 (volume.restrict (cell n L)) ∧ MemLp g 2 (volume.restrict (cell n L))

/-- Zlatoš (1.5): `I = {w ∈ H¹(Tⁿ) | Im w = 0 and u·∇w = 0}`, for period `1`; `w` is
real-valued and `u·∇w = 0` holds almost everywhere (as in Zlatoš's proof of Thm 1.2). -/
def FirstIntegral {n : ℕ} (u : E n → E n) (w : E n → ℝ) (g : E n → E n) : Prop :=
  IsH1Torus 1 w g ∧ ∀ᵐ x, ⟪u x, g x⟫ = 0

/-- The right side of Zlatoš (1.6):
`sup { ∫(u·e)w² / ‖w‖₂² : w ∈ I, ‖∇w‖₂² ≤ f′(0)‖w‖₂² }`, norms and integrals over `Tⁿ`.
(`w = 0` contributes `0`, which the constant `w = 1` also gives, so it changes nothing.) -/
def zlatosSup {n : ℕ} (u : E n → E n) (f : ℝ → ℝ) (e : E n) : ℝ :=
  sSup {r | ∃ w g, FirstIntegral u w g ∧
    ∫ x in cell n 1, ‖g x‖ ^ 2 ≤ fderiv0 f * ∫ x in cell n 1, w x ^ 2 ∧
    r = (∫ x in cell n 1, ⟪u x, e⟫ * w x ^ 2) / ∫ x in cell n 1, w x ^ 2}

end ABC
