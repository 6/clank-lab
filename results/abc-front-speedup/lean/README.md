# The Lean proof

A Lake project for Lean `v4.34.0` (pinned in `lean-toolchain`) and Mathlib at commit
`5ed2965256430c3649e86755f9576b54eca72435` (pinned in `lakefile.toml` and
`lake-manifest.json`). From this folder:

```sh
lake exe cache get
lake build
```

`lake build` builds the library `ABC` and the file `PublicChecks.lean`, which restates the
main theorem with its full type, checks two definitions by `rfl`, and checks with
`#guard_msgs` the exact axioms of four theorems. A different axiom list fails the build. With
the Mathlib cache the build takes about 15 minutes of processor time and about 7 GB of memory.

## The theorem

`ABC.abc_kpp_linear_speedup` in `ABC/Main.lean`:

```lean
theorem abc_kpp_linear_speedup (f : ℝ → ℝ) (hf : ZlatosKPP f) (e : E 3) (he : ‖e‖ = 1) :
    ∃ ℓ : ℝ, 0 < ℓ ∧
      Tendsto (fun K => cstar (2 * Real.pi) abcField f e K / K) atTop (𝓝 ℓ)
```

Every definition it uses is in `ABC/Defs.lean`:

- `E n` is `EuclideanSpace ℝ (Fin n)`, so `‖e‖ = 1` says that `e` is a unit vector.
- `abcField` is $V(x,y,z)=(\sin z+\cos y,\ \sin x+\cos z,\ \sin y+\cos x)$; `PublicChecks.lean`
  checks this by `rfl`.
- `ZlatosKPP f` is condition (1.2) of Zlatoš's paper, the paper's (1): an exponent
  $\varepsilon\in(0,1]$, $f$ continuously differentiable on $[0,1]$ with
  $\varepsilon$-Hölder derivative ($f'(0)$ is the one-sided derivative within $[0,1]$),
  $f(0)=f(1)=0$, $f$ non-increasing on $(1-\varepsilon,1)$, and $0<f(s)\le f'(0)s$ for
  $s\in(0,1)$.
- `IsClassicalSolution u f A T` says that $T$ solves $`T_t+A\,u\cdot\nabla T=\Delta T+f(T)`$
  on $\mathbb R\times\mathbb R^n$, with $T$, $T_t$, $\nabla T$ and $D^2T$ jointly continuous.
- `IsPulsatingFront L u f A e c T` says that $T$ is such a solution with values in $[0,1]$,
  of the form $T(t,\xi)=U(\xi\cdot e-ct,\xi)$ with $U(s,\cdot)$ $L$-periodic in each variable
  and $U(s,\xi)\to1$ as $s\to-\infty$, $U(s,\xi)\to0$ as $s\to+\infty$, uniformly in $\xi$.
- `cstar L u f e A` is the infimum of the speeds $c$ of such fronts (`sInf`, checked by `rfl`
  in `PublicChecks.lean`).

So the formal theorem says: for every $f$ satisfying the paper's (1) and every unit vector $e$,
$`c^*_e(K)/K`$ converges to a positive limit as $K\to\infty$, where $`c^*_e(K)`$ is the minimal
speed of $2\pi$-periodic pulsating fronts of $`T_t+K\,V\cdot\nabla T=\Delta T+f(T)`$. This is the
paper's Theorem 1. The Readings Z1 and Z2 in `ABC/Cited/Zlatos.lean` explain why `cstar` and
`zlatosSup` are not Lean's junk values for `sInf` and `sSup` of empty or unbounded sets.

## Axioms

`#print axioms ABC.abc_kpp_linear_speedup` gives exactly:

- `propext`, `Classical.choice`, `Quot.sound`: Lean's standard axioms.
- `ABC.Cert.fixed_point` (`ABC/Cert.lean`): there is a point `p` with `CertFacts p`, the
  paper's Theorem 2 with its numbers as exact rationals. `p` lies in the square `certBox`
  (`ABC/Flow.lean`); the streamline from `(p, 0)` reaches `(p, 2π)` at a time
  $T\in[3.2352,3.2354]$ with $\sin y+\cos x\ge1.92$ on $[0,T]$; the first-crossing map `retMap`
  has a derivative at `p` with trace in $[-1.9650,-1.9640]$; and `TwistNonzero retMap p`
  (`ABC/Twist.lean`, the paper's Appendix B). The two programs in `../checks/` certify these
  facts, and `../checks/cert_import.py` checks that the rationals in these two Lean files are the
  ones in the certificate and in both programs' output.
- `ABC.Zlatos2010.theorem_1_1` (`ABC/Cited/Zlatos.lean`): Zlatoš, Arch. Ration. Mech. Anal. 195
  (2010), Theorem 1.1, for $1$-periodic flows, with its hypotheses (1.2) and (1.3).
- `ABC.Poschel2001.theorem_A` (`ABC/Cited/Poschel.lean`): Pöschel, Proc. Sympos. Pure Math. 69
  (2001), Theorem A, quoted from arXiv:0908.2234 (version 1.3).

Each cited file quotes the source passage and has a Readings section listing how each phrase
of the quoted statement is read in Lean. Every hypothesis of the two cited theorems is proved
in Lean for this flow: Zlatoš's (1.2) by `zlatosKPP_smul` and (1.3) by `zlatosFlow_abcUnit`
after rescaling to period $1$; Pöschel's analyticity and smallness hypotheses in `ABC/S4/`.

`PublicChecks.lean` also checks the axioms of two intermediate results:

- `ABC.S4.kam_input : KAMInput` (invariant curves with a Lipschitz label around every point
  satisfying `CertFacts`, the paper's Proposition 4) uses Pöschel's theorem and not the
  certificate axiom; the certified facts enter it as a hypothesis.
- `ABC.vortex_tube_exists` (the paper's Proposition 6, taking `KAMInput` as a hypothesis) uses
  the certificate axiom and neither cited theorem.

The uniqueness of the fixed point, which both programs prove, is not used.

## Layout

| Files | Content | Paper |
| --- | --- | --- |
| `ABC/Defs.lean` | the definitions above and Zlatoš's variational supremum `zlatosSup` | §1, App. A |
| `ABC/Cited/` | the two cited theorems | App. A |
| `ABC/ODE.lean`, `ABC/Flow.lean`, `ABC/Twist.lean`, `ABC/Cert.lean` | streamlines, the first-crossing map, the twist coefficient, the certified facts | §3, App. B |
| `ABC/S4/` | Floquet reduction, Birkhoff normal form, elliptic rescaling, Pöschel's theorem, invariant curves | §4, App. C |
| `ABC/Hand.lean`, `ABC/LemmaW*.lean`, `ABC/Tube*.lean` | the invariant function and the tube | §5 |
| `ABC/DriftAvg.lean`, `ABC/Drift.lean`, `ABC/Positivity.lean` | the averages and positivity of Zlatoš's supremum | §5, §6 |
| `ABC/Rescale.lean`, `ABC/Unit.lean`, `ABC/Hyp.lean`, `ABC/Main.lean` | rescaling to period $1$ and the main theorem | §6 |

Files named `…Aux…` hold helper lemmas for the file of the same stem.
