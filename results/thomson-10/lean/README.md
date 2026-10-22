# Lean proof

With elan, Git, and gzip installed, run from this directory:

```sh
lake exe cache get
lake build
```

The pinned toolchain and dependency revisions are recorded in `lean-toolchain`
and `lake-manifest.json`. Lake expands the compressed exact ambient
certificate before reading the proof; no separate preparation script is
needed. The first build compiles the certificate checks and can take tens of
minutes. Subsequent builds reuse the normal Lake cache. If the expanded
certificate source is absent after restoring a build cache, `lake build`
restores it before Lean reads its imports.
Allow about 10 GiB of combined RAM and swap for the first build. On a
memory-limited system, set `LEAN_NUM_THREADS=1` to avoid compiling several
large certificate modules simultaneously.

## Formal statement and verification details

`Publication.lean` checks the exact theorem and candidate-admissibility types,
a pair-count check, an interval-order check, and the guarded axiom reports below.

The project pins Lean 4.34.1 and Mathlib revision [`d13f23b723b8a846827a245b89c10fc7d3f11612`](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612). A successful standalone build completed 3,509 jobs in about 33 minutes with two compiler threads, reusing Mathlib's cache and artifacts from an interrupted setup; this is not a timed build from an empty cache. Allow about 10 GiB of combined RAM and swap; the memory setting is given above. The Python check takes seconds.

[`Publication.lean`](Publication.lean) guards the following actual `#print axioms` output:

```text
'ThomsonN10.thomson_ten_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'ThomsonN10.candidate_admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'ThomsonN10.Cert.L1.Data.residual_agrees_JSON' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The supplied proof uses neither `native_decide` nor `Lean.ofReduceBool`; the guarded dependency reports confirm that no `Lean.ofReduceBool` axiom enters these results.

The Lean build proves [`ThomsonN10.thomson_ten_complete`](Solution.lean), with its exact statement in [`Challenge.lean`](Challenge.lean). Its competitors are maps $x:\{0,\ldots,9\}\to\mathbb{R}^3$ satisfying $\|x_i\|=1$ for every $i$ and injectivity. For every candidate parameter $h$, putting $p=p(h)$ and $E(x)=\sum_{i<j}\|x_i-x_j\|^{-1}$, it proves

$$
E(p)\leq E(x),\qquad E(x)=E(p)\ \Longleftrightarrow\ \exists Q\in O(3),\ \exists\sigma\in S_{10},\ \forall i,\ x_i=Qp_{\sigma(i)}.
$$

Reflections are allowed. Lean's real inverse assigns $0^{-1}=0$; colliding configurations are excluded by injectivity, not assigned infinite energy. Read the main theorem together with [`candidate_admissible`](ThomsonN10/Admissible.lean), which proves that the candidate itself consists of ten distinct unit vectors. Every certificate obligation is discharged.

The height is defined by the subtype [`CandidateParameter`](ThomsonN10/Candidate.lean): $h\in I$ and $s(h)=0$, where $s$ is the explicit stationarity expression, equivalently the derivative of the candidate-family energy

```math
\begin{aligned}
F(h)={}&\frac12+\frac{4\sqrt2+2}{\sqrt{1-h^2}}\\
 &+\frac8{\sqrt{2-\sqrt2+(2+\sqrt2)h^2}}+\frac8{\sqrt{2+\sqrt2+(2-\sqrt2)h^2}}\\
 &+\frac8{\sqrt{2-2h}}+\frac8{\sqrt{2+2h}}.
\end{aligned}
```

The certified interval is $I=[N/D,(2N+1)/(2D)]$, with $D=2^{283}5^7$ and

```math
\begin{aligned}
N={}&513213568640798381215999065069\cdot10^{60}\\
 &+135718731748351905698829816800\cdot10^{30}\\
 &+875926548421101580455514066781.
\end{aligned}
```

These are exactly `heightLower` and `heightUpper`; the interval has width less than $2^{-300}$ and contains $h=0.422687424043986\ldots$. Lean proves existence and uniqueness in this interval, through [`Param/Root.lean`](ThomsonN10/Param/Root.lean) and [`Param/Final.lean`](ThomsonN10/Param/Final.lean); this is part of the main theorem, not a Python root-finding claim.

For every injective unit-sphere configuration with $E(x)\leq E(p)$, the global argument first gives $\langle x_i,x_j\rangle<13/20$ for distinct indices. A degree-16 scalar minorant $m(t)\leq(2-2t)^{-1/2}$ and a rational three-point positive-semidefinite certificate bound the sum of the 45 nonnegative pairwise slacks by $L<10^{-30}$. Outside seven windows of radius $\delta=10^{-10}$ around the candidate's inner products, the scalar gap is at least $10^{-30}$. Thus every pair must lie in a window. The [paper](../paper/paper.pdf) explains the Delsarte–Yudin-type separation bound, the three-point bound and the finite classification that fixes one coherent interval pattern after relabeling; membership in seven windows alone does not establish that pattern.

The preliminary separation bound uses the coarser energy cap $32717/1000=32.717$, which the certified candidate energy satisfies. This is the same cutoff used in the earlier ten-point chord result in the [credits](../README.md#credits); the paper's provenance appendix explains its role and the relation between the two bounds.

Orthogonal Procrustes alignment then bounds the total displacement $\rho=(\sum_i\|y_i-p_i\|^2)^{1/2}$ by $10000\delta=10^{-6}$. The chosen windows therefore land well inside the local certificate's radius $10^{-3}$; no equality of the global and local radii is needed. A componentwise force calculation turns the height equation into full spherical stationarity. The constrained-Hessian certificate and an explicit cubic remainder bound give

$$
E(y)-E(p)\geq\frac{\rho^2}{40}-\frac{153}{10}\rho^3\geq\frac{\rho^2}{200}\qquad(\rho\leq1/1000).
$$

The cubic bound is a separate exact algebraic estimate, not an inference from Hessian positivity. [`LocalPotential.lean`](ThomsonN10/Local/LocalPotential.lean) proves $(1+u)^{-1/2}\geq1-u/2+3u^2/8-5u^3/16$ for $-1<u\leq1$, giving a pairwise quadratic lower bound with a cubic loss of at most $(51/50)\|w\|^3/\|d\|^4$ for $\|w\|\leq\|d\|/200$. Here $d=p_i-p_j$ and $w=(y_i-p_i)-(y_j-p_j)$. Summing over pairs using the certified candidate separation $\|d\|\geq1$ gives the displayed $(153/10)\rho^3$ bound. The Hessian certificate supplies the quadratic term. Exact unit-sphere identities account for radial curvature. Every nonzero aligned displacement with $\rho\leq1/1000$ therefore raises the energy, so a competitor of no greater energy has $\rho=0$. This treats the full spherical configuration space up to orthogonal maps, including perturbations that break the candidate's symmetry. The infinitesimal directions removed by Procrustes alignment are rotations; reflections are included in the orthogonal choice.

The project adapts the MIT-licensed nine-point formalization by Aravind
Karthigeyan. See [THIRD_PARTY.md](../THIRD_PARTY.md) for origins, changes,
and its full license notice.
