import ABC.Defs

/-!
# Cited input: Zlatoš, ARMA 195 (2010), Theorem 1.1

A. Zlatoš, *Sharp asymptotics for KPP pulsating front speed-up and diffusion enhancement by
flows*, Arch. Ration. Mech. Anal. 195 (2010) 441–453; arXiv:0704.1163v2, p. 2:

> Theorem 1.1. If u and f satisfy (1.2) and (1.3) and |e| = 1, then
> lim_{A→∞} c∗e(A)/A = sup_{w∈I, ‖∇w‖₂² ≤ f′(0)‖w‖₂²} ∫_Tn (u · e)w² dx / ‖w‖₂² . (1.6)
> In particular, the limit exists.

with (1.1) "Tt + Au · ∇T = ∆T + f(T) on Rn", (1.2) "f ∈ C1,ε([0, 1]), f(0) = f(1) = 0 and
f is non-increasing on (1 − ε, 1) for some ε > 0, 0 < f(s) ≤ sf′(0) for s ∈ (0, 1)", (1.3)
"The 1-periodic flow u : Tn → Rn satisfies u ∈ C1,ε(Tn), ∇ · u ≡ 0, ∫_Tn u dx = 0", (1.5)
"I ≡ {w ∈ H1(Tn) | Im w = 0 and u · ∇w = 0}", and pulsating fronts and c∗e(A) as defined
in `ABC.IsPulsatingFront` and `ABC.cstar` with period `1`.

Provenance: the passages are quoted from arXiv:0704.1163v2. The published ARMA text was not
opened (paywalled); El Smaily–Kirsch (ARMA 213 (2014), arXiv:1307.4106v2), Theorem B, restates the
published result in the same form, with "max" for "sup".

## Readings

Z1. *`cstar` is an `sInf` over the Lean fronts.* Zlatoš cites Berestycki–Hamel(–Nadirashvili):
    in the KPP case fronts exist precisely for `c ≥ c*_e(A)`. Their fronts are classical, take
    values in `(0, 1)` and have uniform limits, so they meet every clause of
    `IsClassicalSolution` and `IsPulsatingFront`. For `c ≠ 0`, `Periodic 1 (U s)` is their
    condition `T(t + k·e/c, x) = T(t, x − k)`. For `c ≤ 0`, where `U` is unconstrained off the
    diagonal, there is still no front: `T ≥ 1 − δ` on a half-space dominates the Cauchy
    solution from a compactly supported bump, which tends to `1` locally uniformly by the KPP
    hair-trigger effect, contradicting `T → 0`. So the set is `[c*, ∞)` with `c* > 0`, and
    `sInf` is not the junk value.
Z2. *`zlatosSup` is not junk.* Its set contains `w ≡ 1` (`g = 0`, and `f′(0) > 0` follows from
    `0 < f(s) ≤ s f′(0)`), and is bounded above by `sup |u·e|`, so `sSup` is the supremum.
Z3. *One ε.* (1.2) and (1.3) both say "for some ε > 0". `ZlatosKPP` uses one `ε ≤ 1` for the
    Hölder exponent and the interval `(1 − ε, 1)`, and `ZlatosFlow` its own; taking the smaller
    of the two satisfies the source's single ε, since both conditions weaken as ε decreases.
Z4. *`u·∇w = 0` holds almost everywhere* (`ABC.FirstIntegral`), as in Zlatoš's proof of
    Theorem 1.2; `w ∈ H¹` has only a weak gradient.
Z5. *Dimension.* There is no hypothesis `n ≥ 1`: `‖e‖ = 1` is impossible for `n = 0`, so that
    case is vacuous.
-/

namespace ABC.Zlatos2010

open Filter Topology

/-- **Cited axiom.** Zlatoš (2010), Theorem 1.1, period `1` (Readings Z1–Z5). -/
axiom theorem_1_1 {n : ℕ} (u : E n → E n) (f : ℝ → ℝ) (e : E n)
    (hf : ZlatosKPP f) (hu : ZlatosFlow 1 u) (he : ‖e‖ = 1) :
    Tendsto (fun A => cstar 1 u f e A / A) atTop (𝓝 (zlatosSup u f e))

end ABC.Zlatos2010
