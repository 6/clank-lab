import Mathlib

/-!
# The scattering diagram `D(P₁, P₂)` over `B = ℚ⟦x,y⟧`, levelwise

Conventions follow GPS §1.3 (Gross–Pandharipande–Siebert, "The tropical vertex", arXiv 0902.0779)
and BLMMR §2. In GPS §1.3 a ray is `m₀' + ℝ_{≥0} m₀` with function in `k[z^{m₀}]`, crossing it
applies `z^m ↦ z^m f^{⟨m,n₀⟩}` with `⟨n₀, γ'⟩ > 0`, and consistency is `θ_γ = θ_s ∘ ⋯ ∘ θ_1 = id`
for loops. For a counterclockwise loop the crossings are, in this file's walls, `θ_{(1,0)}⁻¹`, the
rays' `θ_r⁻¹` by increasing slope, `θ_{(0,1)}⁻¹`, `θ_{(1,0)}`, `θ_{(0,1)}`, which gives exactly the
identity below. (BLMMR draw the rays as `ℝ_{≤0}(v₁,v₂)`, the GS/GHKK sign convention, with the same
functions.) The Lean wall `θ_{r,f}` below is GPS's intro `θ_{r,f}` with `f ↦ f⁻¹`, and
consistency is the identity of ring homomorphisms
`θ_{(0,1)} ∘ θ_{(1,0)} = θ_{(1,0)} ∘ (ascending product of the other rays) ∘ θ_{(0,1)}`
(composition `(g ∘ h)(a) = g (h a)`). This orientation is pinned by GPS §1's `ℓ₁ = ℓ₂ = 2` example
(`(1 − xy)^{−4}` on `(1,1)`, `(1 + x^{n+1}yⁿ)²` on `(n+1, n)`) and by the finite `B₂`/`G₂` diagrams;
the reversed order fails these. (GPS eq. (0.1), read naively with ring-homomorphism composition,
matches the reversed family, so it is not cited as the source of the order.)
* a ray is a primitive vector `r = (r₁, r₂) ∈ ℕ² ∖ 0`; we index rays by their slope
  `r₂/r₁ ∈ [0, ∞]` (type `Slope = WithTop ℚ≥0`; slope `s = n/d` in lowest terms is the ray `(d, n)`,
  and `⊤` is the ray `(0, 1)`);
* the wall `θ_{r,f}` for `f ∈ 1 + tℚ⟦t⟧` is the substitution automorphism
  `x ↦ x f(z^r)^{r₂}`, `y ↦ y f(z^r)^{−r₁}`, i.e. `z^m ↦ z^m f(z^r)^{ω(m,r)}` with
  `ω(m,r) = m₁r₂ − m₂r₁`;
* a family `f : Slope → ℚ⟦t⟧` (one function per ray, axes included) is a *consistent family for
  `D(P₁,P₂)`* when `θ_{(0,1),P₂} ∘ θ_{(1,0),P₁} = Π_{r ascending} θ_{r,f_r}`. The
  infinite product is read levelwise: modulo `𝔪^N`, `𝔪 = (x,y)`, only rays with `r₁ + r₂ < N`
  act non-trivially (`θ_{r,f}(z^m) ≡ z^m mod z^m 𝔪^{r₁+r₂}`), so the identity is required, for
  every `N`, for the finite ascending product over the rays with `r₁ + r₂ < N`, modulo `𝔪^N`, on the
  generators `x, y` (both sides are substitution endomorphisms preserving `𝔪^N`, so agreement on
  `x, y` mod `𝔪^N` is agreement on `B/𝔪^N`).
-/

noncomputable section

namespace ErsConj13.Scat

/-- `B = ℚ⟦x,y⟧` (variable 0 is `x`, variable 1 is `y`). -/
abbrev B := MvPowerSeries (Fin 2) ℚ

/-- Slopes of rays: `s : ℚ≥0` is the ray `(s.den, s.num)`; `⊤` is the ray `(0, 1)`. -/
abbrev Slope := WithTop ℚ≥0

/-- The primitive vector `(r₁, r₂)` of the ray with slope `s`. -/
def ray (s : Slope) : ℕ × ℕ := WithTop.recTopCoe (0, 1) (fun q => (q.den, q.num)) s

/-- The monomial `z^r = x^{r₁} y^{r₂}`. -/
def rayMono (s : Slope) : B :=
  MvPowerSeries.monomial (Finsupp.single 0 (ray s).1 + Finsupp.single 1 (ray s).2) 1

/-- `f(z^r)` for a one-variable series `f`. -/
def rayEval (s : Slope) (f : PowerSeries ℚ) : B := PowerSeries.subst (rayMono s) f

/-- The wall `θ_{r,f}`: the substitution `x ↦ x f(z^r)^{r₂}`, `y ↦ y (f(z^r)^{r₁})⁻¹`. -/
def wall (s : Slope) (f : PowerSeries ℚ) : B → B :=
  MvPowerSeries.subst ![MvPowerSeries.X 0 * rayEval s f ^ (ray s).2,
    MvPowerSeries.X 1 * (rayEval s f ^ (ray s).1)⁻¹]

/-- The slope of `(p, q) ∈ ℕ²`: `q/p`, or `⊤` when `p = 0`. -/
def slopeOf (p q : ℕ) : Slope := if p = 0 then ⊤ else (((q : ℚ≥0) / p : ℚ≥0) : Slope)

/-- The rays `r` with `r₁ + r₂ < N` (primitive vectors), as slopes. -/
def slopesBelow (N : ℕ) : Finset Slope :=
  ((Finset.range N ×ˢ Finset.range N).filter
    (fun pq => Nat.Coprime pq.1 pq.2 ∧ pq.1 + pq.2 < N)).image (fun pq => slopeOf pq.1 pq.2)

/-- The finite ascending ordered product `θ_{r₁,f_{r₁}} ∘ θ_{r₂,f_{r₂}} ∘ ⋯` over the rays with
`r₁ + r₂ < N`, smallest slope leftmost (so applied last). -/
def orderedProd (f : Slope → PowerSeries ℚ) (N : ℕ) : B → B :=
  ((slopesBelow N).sort (· ≤ ·)).foldr (fun s φ => wall s (f s) ∘ φ) id

/-- `f ≡ g mod 𝔪^N`: all coefficients of total degree `< N` agree. -/
def EqMod (N : ℕ) (f g : B) : Prop :=
  ∀ e : Fin 2 →₀ ℕ, e 0 + e 1 < N → MvPowerSeries.coeff e f = MvPowerSeries.coeff e g

/-- `f` is a consistent family for `D(P₁, P₂)`: every ray function has constant term 1,
and for every `N`, `θ_{(0,1),P₂} ∘ θ_{(1,0),P₁} ≡ Π_{|r|<N, ascending} θ_{r,f_r}` modulo `𝔪^N` on
`x` and `y`. Here `P₁(t)` is evaluated at `z^{(1,0)} = x` and `P₂(t)` at `z^{(0,1)} = y`. -/
def IsConsistentFamily (P₁ P₂ : PowerSeries ℚ) (f : Slope → PowerSeries ℚ) : Prop :=
  (∀ s, PowerSeries.constantCoeff (f s) = 1) ∧
  ∀ N : ℕ, ∀ i : Fin 2,
    EqMod N (orderedProd f N (MvPowerSeries.X i))
      (wall ⊤ P₂ (wall (0 : ℚ≥0) P₁ (MvPowerSeries.X i)))

end ErsConj13.Scat
