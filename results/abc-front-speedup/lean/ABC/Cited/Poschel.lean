import Mathlib

/-!
# Cited input: Pöschel, Proc. Sympos. Pure Math. 69 (2001), Theorem A

J. Pöschel, *A lecture on the classical KAM theorem*, Proc. Sympos. Pure Math. 69 (2001)
707–732; arXiv:0908.2234v1 ("Version 1.3 – 2009"), PDF sha256
`95503c181ede41948041b65963390244680457ab9d8d24b1a4716c81c5735d35`. The verbatim passages are
in the docstring of `ABC.Poschel2001.theorem_A`.
Provenance: arXiv v1.3 carries "small corrections" relative to the 2001 publication, whose text
was not opened; the axiom quotes v1.3.

Conventions:
* `ℝⁿ`, `ℂⁿ` are `Fin n → ℝ`, `Fin n → ℂ`; their Mathlib norms are the sup-norms
  `max_i |x_i|`, and `‖·‖` on a product is the max of the two norms, so every `‖·‖` and `dist`
  below is the source's "sup-norm" `|·|` (§2b).
* `𝕋ⁿ` is `ℝⁿ` modulo `2πℤⁿ` (§1b): functions on `𝕋ⁿ` are `2π`-periodic in each angle, and a
  map into `B × 𝕋ⁿ` is given by a lift `Φ` with `Φ − Φ₀` `2π`-periodic.
* A point of phase space × parameters is `(I, θ, ω) : ℂⁿ × ℂⁿ × ℂⁿ`; real points are images of
  `ofRe : ℝⁿ → ℂⁿ`.
* `ν = τ + 1` is written out as `τ + 1`; `s ^ (τ + 1)` is `Real.rpow`.

## Readings

Where Theorem A leaves something implicit, we chose as follows (each with the sentence it rests
on).

1. *Ω is an open connected set, not assumed bounded.* §1c: "a local diffeomorphism between D and
   some open frequency domain Ω ⊂ ℝⁿ". Boundedness and a regular boundary enter only the measure
   statements ("for any bounded domain Ω", "provided the boundary of Ω is piecewise smooth"),
   not Theorem A.
2. *Ω_α = {ω ∈ Ω ∩ Δ_α^τ : dist(ω, y) ≥ α for all y ∈ ∂Ω}, distance in the sup-norm.* §1e:
   "the subsets Ω_α ⊂ Ω, α > 0, whose frequencies belong to Δ_α and also have at least distance
   α to the boundary of Ω", with "|·| stands for the sup-norm of real vectors" (§2b). The
   condition is stated pointwise over `frontier Ω` (so `Ω = ℝⁿ`, with empty boundary, imposes
   no constraint, as "distance to ∅ = ∞" would), not with `Metric.infDist`, which is `0` on `∅`.
3. *`n ≥ 2`, the source's standing assumption.* §1b: "We assume that the number
   n of degrees of freedom is at least 2, since one degree of freedom systems are always
   integrable." The claim uses `n = 2`.
4. *`α, r, s, h > 0`.* §1d: "there exist constants α > 0 and τ > 0"; `r, s, h` are radii of the
   "complex neighbourhoods" D_{r,s}, O_h (§2b), so they are positive.
5. *O_h = {ω ∈ ℂⁿ : ∃ ω₀ ∈ Ω_α, |ω − ω₀| < h}.* §2b: "O_h = {ω : |ω − Ω_α| < h} ⊂ ℂⁿ"; the
   distance to a set is `< h` iff some point of the set is within `< h`.
6. *"P real analytic on D_{r,s} × O_h"*: `P` is complex differentiable (holomorphic) on that
   open set, real at real points of it, and `2π`-periodic in each `θ_j`. §1b: "all our
   hamiltonians are assumed to be real analytic in all arguments" and "f_ε has period 2π in
   each component of q"; §2b calls D_{r,s} a "complex neighbourhood of the torus {0} × 𝕋ⁿ".
7. *|P|_{r,s,h} through a bound `ε`.* §2b: "The sup-norm of functions on D_{r,s} × O_h is
   denoted by |·|_{r,s,h}." We assume `‖P x‖ ≤ ε` on D_{r,s} × O_h and `ε ≤ γαrs^ν`, and prove
   the estimates with `ε` in place of |P|_{r,s,h}. This is equivalent to the source, because the
   right-hand sides are increasing in |P|_{r,s,h} and `ε = |P|_{r,s,h}` is allowed.
8. *H = N + P with N = e(ω) + ⟨ω, I⟩ for an arbitrary `e`, and ⟨ω, I⟩ = Σ ω_j I_j (bilinear,
   the analytic extension).* §2a: "N = e(ω) + ⟨ω,I⟩". `e` does not depend on `(I, θ)`, so it does
   not affect `X_H`.
9. *X_H = (−∂_θ H, ∂_I H)* (complex partial derivatives, at real points). §1b: "ṗ = −H_q(p, q),
   q̇ = H_p(p, q)" and "υ = Σ dp_j ∧ dq_j", "υ(X_H, ·) = −dH", with I the action and θ the angle
   (§2a: "Writing also θ instead of q").
10. *`X_H|_{φ(ω)} ∘ Φ = DΦ·X_N` is the identity
    `X_H(Φ(θ, ω); φ(ω)) = ∂_θΦ(θ, ω) · ω` for real θ and ω ∈ Ω_α.* §2a: "X_N = Σ ω_j ∂/∂θ_j";
    §2b: "we wrote X_N also for the analogous constant vector field on 𝕋ⁿ alone", "an embedded
    invariant Kronecker torus 𝒯_ω = Φ(𝕋ⁿ, ω) with frequencies ω for the hamiltonian vector field
    X_H at the slightly shifted parameter value ω̃ = φ(ω)". The θ-derivative is the complex one
    of the analytic extension, equal at real points to the real one.
11. *B = {I ∈ ℝⁿ : |I| < r}, and φ(Ω_α) ⊂ O_h.* §2a: "B some sufficiently small ball around the
    origin in ℝⁿ"; X_H ∘ Φ only makes sense where P is defined, that is, at
    `(Φ(θ, ω), φ(ω)) ∈ D_{r,s} × O_h`. §5c: "a map F consisting of a family of embeddings
    Φ : 𝕋ⁿ × Ω_α → D × 𝕋ⁿ and a parameter transformation φ : Ω_α → Ω", obtained as the limit of
    `F_j : D_j × O_j → D_0 × O_0`. The stated estimates give `|I| ≤ cγr` and
    `|φ(ω) − ω| ≤ cγαs^ν ≤ cγh`, so both inclusions hold once `cγ < 1`. They are derived, not
    quoted: the axiom's `γ` is the source's `γ` shrunk to `min(γ, 1/(2c))`. That is legitimate
    because `∃ γ` precedes `∃ c` and `c` is unchanged, and a smaller `γ` only strengthens the
    hypothesis.
12. *Φ's complex extension is defined on T_* × Ω_α*, with `Φ(·, ω)` holomorphic on
    `T_* = {θ ∈ ℂⁿ : |ℑθ| < s/2}`; Φ is real at real θ. §2b: "Φ is real analytic on
    T_* = {θ : |ℑθ| < s/2} for each ω", and the estimates hold "uniformly on T_* × Ω_α". §5c:
    "⋂ D_j × O_j = T_* × Ω_α". We use the open strip as written (the weaker claim).
13. *Torus lift.* Φ : 𝕋ⁿ × Ω_α → B × 𝕋ⁿ "close to Φ₀" and "W(Φ − Φ₀)" are read through a lift
    with `Φ(θ + 2πe_j, ω) = Φ(θ, ω) + (0, 2πe_j)`, so that `Φ − Φ₀` is a function on 𝕋ⁿ.
14. *"torus embedding"*: `θ ↦ Φ(θ, ω)` is injective on 𝕋ⁿ (equal images mod `2πℤⁿ` force equal
    θ mod `2πℤⁿ`) and an immersion (injective derivative). This is an embedding, since 𝕋ⁿ is
    compact. §2a calls Φ₀ "trivial embeddings of 𝕋ⁿ over Ω into phase space".
15. *Lagrangian*: `υ(∂_uΦ, ∂_vΦ) = 0` for all real tangent vectors `u, v` at real θ. §1c: "the
    restriction of the symplectic form υ to their tangent space vanishes, and their dimension is
    maximal with respect to this property". Maximality is automatic for an embedded n-torus in
    2n-dimensional phase space.
16. *Estimates.* `|W(Φ − Φ₀)| ≤ δ` pointwise on T_* × Ω_α, and `αs^ν |W(Φ − Φ₀)|_𝔏 ≤ δ` as
    `αs^ν |W(Φ(θ,υ) − Φ₀(θ)) − W(Φ(θ,ω) − Φ₀(θ))| ≤ δ |υ − ω|` for each θ ∈ T_*, υ, ω ∈ Ω_α,
    where `δ = c ε / (αrs^ν)`. Likewise for `φ − id` on Ω_α, with `c ε / r`. §2b: "|φ|_𝔏 =
    sup_{υ≠ω} |φ(υ) − φ(ω)| / |υ − ω|", "uniformly on T_* × Ω_α and Ω_α, respectively";
    W = diag(r⁻¹Id, s⁻¹Id) acts on `(I, θ)`. The words "Lipschitz continuous" are also stated
    separately (they follow from the `|·|_𝔏` bounds).
-/

noncomputable section

namespace ABC.Poschel2001

open Real

variable {n : ℕ}

/-- A real vector as a complex vector, `ℝⁿ ⊂ ℂⁿ`. -/
def ofRe (x : Fin n → ℝ) : Fin n → ℂ := fun i => (x i : ℂ)

/-- The componentwise imaginary part `ℑθ`. -/
def imPart (θ : Fin n → ℂ) : Fin n → ℝ := fun i => (θ i).im

/-- §1d: `|k| = |k₁| + ⋯ + |kₙ|`. -/
def l1norm (k : Fin n → ℤ) : ℝ := ∑ i, |(k i : ℝ)|

/-- `⟨k, ω⟩` for `k ∈ ℤⁿ`, `ω ∈ ℝⁿ`. -/
def pairZ (k : Fin n → ℤ) (ω : Fin n → ℝ) : ℝ := ∑ i, (k i : ℝ) * ω i

/-- §1d: `Δ_α^τ`, the `ω ∈ ℝⁿ` with `|⟨k,ω⟩| ⩾ α / |k|^τ` for all `0 ≠ k ∈ ℤⁿ`. -/
def Delta (τ α : ℝ) : Set (Fin n → ℝ) :=
  {ω | ∀ k : Fin n → ℤ, k ≠ 0 → α / l1norm k ^ τ ≤ |pairZ k ω|}

/-- §1e: `Ω_α ⊂ Ω`, the frequencies of `Ω` that belong to `Δ_α = Δ_α^τ` and have at least
(sup-norm) distance `α` to the boundary of `Ω` (Readings 2). -/
def OmegaAlpha (τ : ℝ) (Ω : Set (Fin n → ℝ)) (α : ℝ) : Set (Fin n → ℝ) :=
  {ω | ω ∈ Ω ∧ ω ∈ Delta τ α ∧ ∀ y ∈ frontier Ω, α ≤ dist ω y}

/-- Points `(I, θ, ω)` of `ℂⁿ × ℂⁿ × ℂⁿ` (actions, angles, parameters). -/
abbrev Pt (n : ℕ) := (Fin n → ℂ) × (Fin n → ℂ) × (Fin n → ℂ)

/-- Points `(I, θ)` of (complexified) phase space `ℂⁿ × ℂⁿ`. -/
abbrev Ph (n : ℕ) := (Fin n → ℂ) × (Fin n → ℂ)

/-- §2b: `D_{r,s} = {I : |I| < r} × {θ : |ℑθ| < s} ⊂ ℂⁿ × ℂⁿ`. -/
def Drs (r s : ℝ) : Set (Ph n) := {z | ‖z.1‖ < r ∧ ‖imPart z.2‖ < s}

/-- §2b: `O_h = {ω : |ω − K| < h} ⊂ ℂⁿ` for `K = Ω_α ⊂ ℝⁿ` (Readings 5). -/
def Oh (K : Set (Fin n → ℝ)) (h : ℝ) : Set (Fin n → ℂ) :=
  {ω | ∃ ω₀ ∈ K, ‖ω - ofRe ω₀‖ < h}

/-- `D_{r,s} × O_h` as a set of points `(I, θ, ω)`. -/
def DO (r s : ℝ) (K : Set (Fin n → ℝ)) (h : ℝ) : Set (Pt n) :=
  {x | (x.1, x.2.1) ∈ Drs r s ∧ x.2.2 ∈ Oh K h}

/-- `2π e_j ∈ ℂⁿ`, the period in the angle `θ_j`. -/
def twoPiE (j : Fin n) : Fin n → ℂ := Pi.single j ((2 * π : ℝ) : ℂ)

/-- "`P` is real analytic on `U`" (Readings 6): holomorphic on `U`, real at the real points of
`U`, and `2π`-periodic in each angle `θ_j`. -/
def IsRealAnalyticOn (P : Pt n → ℂ) (U : Set (Pt n)) : Prop :=
  DifferentiableOn ℂ P U ∧
    (∀ I θ ω : Fin n → ℝ, (ofRe I, ofRe θ, ofRe ω) ∈ U →
      (P (ofRe I, ofRe θ, ofRe ω)).im = 0) ∧
    ∀ (j : Fin n), ∀ x ∈ U, P (x.1, x.2.1 + twoPiE j, x.2.2) = P x

/-- §2a: `H = N + P` with `N = e(ω) + ⟨ω, I⟩`, at the point `x = (I, θ, ω)`. -/
def ham (e : (Fin n → ℂ) → ℂ) (P : Pt n → ℂ) (x : Pt n) : ℂ :=
  e x.2.2 + ∑ j, x.2.2 j * x.1 j + P x

/-- §1b: the hamiltonian vector field `X_H = (−H_θ, H_I)` of `H` at the parameter value `ω`,
evaluated at `z = (I, θ)` (Readings 9). -/
def XH (H : Pt n → ℂ) (ω : Fin n → ℂ) (z : Ph n) : Ph n :=
  (fun j => -fderiv ℂ (fun θ' => H (z.1, θ', ω)) z.2 (Pi.single j 1),
   fun j => fderiv ℂ (fun I' => H (I', z.2, ω)) z.1 (Pi.single j 1))

/-- §1b: the symplectic form `υ = Σ_j dI_j ∧ dθ_j` on two tangent vectors `(I, θ)`. -/
def sympForm (a b : Ph n) : ℂ := ∑ j, (a.1 j * b.2 j - a.2 j * b.1 j)

/-- §2b: `T_* = {θ : |ℑθ| < s/2}`. -/
def Tstar (s : ℝ) : Set (Fin n → ℂ) := {θ | ‖imPart θ‖ < s / 2}

/-- §2a: `Φ₀(θ, ω) = (0, θ)`. -/
def Phi0 (θ : Fin n → ℂ) : Ph n := (0, θ)

/-- §2b: `W = diag(r⁻¹ Id, s⁻¹ Id)` acting on `(I, θ)`. -/
def W (r s : ℝ) (z : Ph n) : Ph n := (r⁻¹ • z.1, s⁻¹ • z.2)

/-- §2b: `|f|_{𝔏} ≤ L` on `S`, where `|f|_𝔏 = sup_{υ≠ω} |f(υ) − f(ω)| / |υ − ω|`. -/
def LipSemiLe {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] (f : X → Y)
    (S : Set X) (L : ℝ) : Prop :=
  ∀ υ ∈ S, ∀ ω ∈ S, dist (f υ) (f ω) ≤ L * dist υ ω

/-- A real analytic "torus embedding" `θ ↦ Φ(θ)` of `𝕋ⁿ` into `ℂⁿ × ℂⁿ`, given on real `θ` by
its lift (Readings 13, 14). It is injective on `𝕋ⁿ`: equal actions and angles equal mod
`2πℤⁿ` force `θ ≡ θ'` mod `2πℤⁿ`. Its derivative is injective at every real `θ`. -/
def IsTorusEmbedding (Φ : (Fin n → ℂ) → Ph n) : Prop :=
  (∀ θ θ' : Fin n → ℝ, (Φ (ofRe θ)).1 = (Φ (ofRe θ')).1 →
      (∃ k : Fin n → ℤ, (Φ (ofRe θ)).2 = (Φ (ofRe θ')).2 + ofRe (fun i => 2 * π * k i)) →
      ∃ k : Fin n → ℤ, θ = θ' + fun i => 2 * π * k i) ∧
    ∀ θ : Fin n → ℝ, Function.Injective (fderiv ℂ Φ (ofRe θ))

/-- §1c: the embedded torus `θ ↦ Φ(θ)` is Lagrangian: `υ` vanishes on its tangent spaces. -/
def IsLagrangian (Φ : (Fin n → ℂ) → Ph n) : Prop :=
  ∀ θ u v : Fin n → ℝ, sympForm (fderiv ℂ Φ (ofRe θ) (ofRe u)) (fderiv ℂ Φ (ofRe θ) (ofRe v)) = 0

/-- The conclusion of Theorem A for `H = N + P` on `D_{r,s} × O_h`, with `|P|_{r,s,h} ≤ ε`,
`Ω_α = OmegaAlpha τ Ω α`, `ν = τ + 1`, and constant `c`. Here `φ : Ω_α → Ω` and
`Φ : T_* × Ω_α → ℂⁿ × ℂⁿ` (the complex extension in `θ`); values off these sets are unused. -/
structure Conclusion (τ c : ℝ) (Ω : Set (Fin n → ℝ)) (α r s h ε : ℝ)
    (e : (Fin n → ℂ) → ℂ) (P : Pt n → ℂ)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) (Φ : (Fin n → ℂ) → (Fin n → ℝ) → Ph n) : Prop where
  /-- `φ : Ω_α → Ω`. -/
  mapsTo : ∀ ω ∈ OmegaAlpha τ Ω α, φ ω ∈ Ω
  /-- `φ(ω) ∈ O_h`, so `H` is defined at the shifted parameter (Readings 11). -/
  mem_Oh : ∀ ω ∈ OmegaAlpha τ Ω α, ofRe (φ ω) ∈ Oh (OmegaAlpha τ Ω α) h
  /-- `Φ : 𝕋ⁿ × Ω_α → B × 𝕋ⁿ` is real, with `B = {I ∈ ℝⁿ : |I| < r}` (Readings 11, 12). -/
  real : ∀ ω ∈ OmegaAlpha τ Ω α, ∀ θ : Fin n → ℝ,
    ∃ a b : Fin n → ℝ, Φ (ofRe θ) ω = (ofRe a, ofRe b) ∧ ‖a‖ < r
  /-- `Φ` is a lift of a map on `𝕋ⁿ` with `Φ − Φ₀` periodic (Readings 13). -/
  periodic : ∀ ω ∈ OmegaAlpha τ Ω α, ∀ (j : Fin n) (θ : Fin n → ℝ),
    Φ (ofRe θ + twoPiE j) ω = Φ (ofRe θ) ω + ((0 : Fin n → ℂ), twoPiE j)
  /-- `Φ` is real analytic on `T_*` for each `ω`. -/
  analytic : ∀ ω ∈ OmegaAlpha τ Ω α, DifferentiableOn ℂ (fun θ => Φ θ ω) (Tstar s)
  /-- Each `Φ(·, ω)` is a torus embedding. -/
  embedding : ∀ ω ∈ OmegaAlpha τ Ω α, IsTorusEmbedding (fun θ => Φ θ ω)
  /-- The embedded tori are Lagrangian. -/
  lagrangian : ∀ ω ∈ OmegaAlpha τ Ω α, IsLagrangian (fun θ => Φ θ ω)
  /-- `X_H|_{φ(ω)} ∘ Φ = DΦ·X_N`, with `X_N = Σ_j ω_j ∂/∂θ_j` (Readings 10). -/
  invariant : ∀ ω ∈ OmegaAlpha τ Ω α, ∀ θ : Fin n → ℝ,
    XH (ham e P) (ofRe (φ ω)) (Φ (ofRe θ) ω) = fderiv ℂ (fun θ' => Φ θ' ω) (ofRe θ) (ofRe ω)
  /-- `φ` is Lipschitz continuous on `Ω_α`. -/
  lipschitz_φ : ∃ K, LipschitzOnWith K φ (OmegaAlpha τ Ω α)
  /-- `Φ` is a Lipschitz continuous family over `Ω_α`, uniformly on `T_*`. -/
  lipschitz_Φ : ∃ K, ∀ θ ∈ Tstar s, LipschitzOnWith K (Φ θ) (OmegaAlpha τ Ω α)
  /-- `|W(Φ − Φ₀)| ≤ c / (α r s^ν) · |P|_{r,s,h}` on `T_* × Ω_α`. -/
  est_Φ : ∀ θ ∈ Tstar s, ∀ ω ∈ OmegaAlpha τ Ω α,
    ‖W r s (Φ θ ω - Phi0 θ)‖ ≤ c / (α * r * s ^ (τ + 1)) * ε
  /-- `α s^ν |W(Φ − Φ₀)|_𝔏 ≤ c / (α r s^ν) · |P|_{r,s,h}`, uniformly in `θ ∈ T_*`. -/
  est_Φ_lip : ∀ θ ∈ Tstar s,
    LipSemiLe (fun ω => W r s (Φ θ ω - Phi0 θ)) (OmegaAlpha τ Ω α)
      ((α * s ^ (τ + 1))⁻¹ * (c / (α * r * s ^ (τ + 1)) * ε))
  /-- `|φ − id| ≤ c / r · |P|_{r,s,h}` on `Ω_α`. -/
  est_φ : ∀ ω ∈ OmegaAlpha τ Ω α, ‖φ ω - ω‖ ≤ c / r * ε
  /-- `α s^ν |φ − id|_𝔏 ≤ c / r · |P|_{r,s,h}` on `Ω_α`. -/
  est_φ_lip : LipSemiLe (fun ω => φ ω - ω) (OmegaAlpha τ Ω α)
    ((α * s ^ (τ + 1))⁻¹ * (c / r * ε))

/-- **Cited axiom.** Pöschel (2001), Theorem A (arXiv:0908.2234v1, §2b, p. 10), for `n ≥ 2`
(Readings 3). It is used once, in `ABC.S4.HAND_KAM_curves_proof` (`S4/Final.lean`), with `n = τ = 2`.

> Theorem A  Let H = N + P. Suppose P is real analytic on D_{r,s} × O_h with
> |P|_{r,s,h} ⩽ γαrs^ν,  αs^ν ⩽ h,
> where ν = τ + 1 and γ is a small constant depending only on n and τ. Suppose also that
> r, s, h ⩽ 1. Then there exists a Lipschitz continuous map φ : Ω_α → Ω close to the identity
> and a Lipschitz continuous family of real analytic torus embeddings Φ : 𝕋ⁿ × Ω_α → B × 𝕋ⁿ
> close to Φ₀, such that for each ω ∈ Ω_α the embedded tori are Lagrangian and
> X_H|_{φ(ω)} ∘ Φ = DΦ·X_N.
> Moreover, Φ is real analytic on T_* = {θ : |ℑθ| < s/2} for each ω, and
> |W(Φ − Φ₀)|, αs^ν |W(Φ − Φ₀)|_𝔏 ⩽ (c / (αrs^ν)) |P|_{r,s,h},
> |φ − id|, αs^ν |φ − id|_𝔏 ⩽ (c / r) |P|_{r,s,h},
> uniformly on T_* × Ω_α and Ω_α, respectively, where c is a constant depending only on n and
> τ, and W = diag(r⁻¹Id, s⁻¹Id).

Definitions used, verbatim:

§1b: "the conjugate angular variables, whose domain is the usual n-torus 𝕋ⁿ obtained from ℝⁿ by
identifying points whose components differ by integer multiples of 2π. Thus, f_ε has period 2π
in each component of q. Moreover, all our hamiltonians are assumed to be real analytic in all
arguments. The equations of motion are, as usual, ṗ = −H_q(p, q), q̇ = H_p(p, q) […] The
underlying phase space is D × 𝕋ⁿ ⊂ ℝⁿ × 𝕋ⁿ with the standard symplectic structure
υ = Σ_{1⩽j⩽n} dp_j ∧ dq_j. The hamiltonian vector field X_H associated with the equations of
motions then satisfies υ(X_H, ·) = −dH."

§1c: "In addition these tori are Lagrangian. That is, the restriction of the symplectic form υ
to their tangent space vanishes, and their dimension is maximal with respect to this property."
and "a local diffeomorphism between D and some open frequency domain Ω ⊂ ℝⁿ".

§1d: "strongly nonresonant in the sense that there exist constants α > 0 and τ > 0 such that
(1) |⟨k,ω⟩| ⩾ α / |k|^τ for all 0 ≠ k ∈ ℤⁿ, where |k| = |k₁| + ⋯ + |kₙ|. […] Let Δ_α^τ denote
the set of all ω ∈ ℝⁿ satisfying these infinitely many conditions with fixed α and τ." and "But
here we will fix τ > n − 1 and drop it from the notation, letting Δ_α = Δ_α^τ."

§1e: "To state the Kam theorem, we therefore single out the subsets Ω_α ⊂ Ω, α > 0, whose
frequencies belong to Δ_α and also have at least distance α to the boundary of Ω."

§2a: "Writing also θ instead of q for the angular variables, we obtain the family of
hamiltonians H = N + P with N = e(ω) + ⟨ω,I⟩, P = P_h(I, ω) + P_ϵ(I, θ, ω). They are real
analytic in the coordinates (I, θ) in B × 𝕋ⁿ, B some sufficiently small ball around the origin
in ℝⁿ, as well as in the parameters ω in some uniform neighbourhood of Ω." and "There is an
invariant Kronecker torus 𝒯_ω = {0} × 𝕋ⁿ with constant vector field X_N = Σ_{1⩽j⩽n} ω_j ∂/∂θ_j
for each ω ∈ Ω, and all these tori are given by the family Φ₀ : 𝕋ⁿ × Ω → B × 𝕋ⁿ,
(θ, ω) ↦ (0, θ) of trivial embeddings of 𝕋ⁿ over Ω into phase space."

§2b: "Let D_{r,s} = {I : |I| < r} × {θ : |ℑθ| < s} ⊂ ℂⁿ × ℂⁿ and O_h = {ω : |ω − Ω_α| < h} ⊂ ℂⁿ
denote complex neighbourhoods of the torus {0} × 𝕋ⁿ and Ω_α, respectively, where |·| stands
for the sup-norm of real vectors. The sup-norm of functions on D_{r,s} × O_h is denoted by
|·|_{r,s,h}. We will also consider the Lipschitz constants of mappings with respect to ω. We
define |φ|_𝔏 = sup_{υ≠ω} |φ(υ) − φ(ω)| / |υ − ω|, where the underlyingdomain will be clear from
the context or indicated by a subscript." and, after the theorem: "By slight abuse of notation
we wrote X_N also for the analogous constant vector field on 𝕋ⁿ alone."

The bound `ε` stands for `|P|_{r,s,h}` (Readings 7); `ν = τ + 1` is written out. -/
axiom theorem_A :
    ∀ n : ℕ, 2 ≤ n → ∀ τ : ℝ, (n : ℝ) - 1 < τ →
    ∃ γ : ℝ, 0 < γ ∧ ∃ c : ℝ, 0 < c ∧
    ∀ (Ω : Set (Fin n → ℝ)) (α r s h ε : ℝ) (e : (Fin n → ℂ) → ℂ) (P : Pt n → ℂ),
      IsOpen Ω → IsConnected Ω →
      0 < α → 0 < r → 0 < s → 0 < h → r ≤ 1 → s ≤ 1 → h ≤ 1 →
      IsRealAnalyticOn P (DO r s (OmegaAlpha τ Ω α) h) →
      (∀ x ∈ DO r s (OmegaAlpha τ Ω α) h, ‖P x‖ ≤ ε) →
      ε ≤ γ * α * r * s ^ (τ + 1) →
      α * s ^ (τ + 1) ≤ h →
      ∃ (φ : (Fin n → ℝ) → (Fin n → ℝ)) (Φ : (Fin n → ℂ) → (Fin n → ℝ) → Ph n),
        Conclusion τ c Ω α r s h ε e P φ Φ

end ABC.Poschel2001
