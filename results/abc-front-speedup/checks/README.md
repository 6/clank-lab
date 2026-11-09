# The certified orbit

`sh checks/run.sh`, run from the result's folder after
`python3 -m pip install -r checks/requirements.txt`, proves the paper's Theorem 2 twice, with
two programs that share no code, and then checks that the Lean certificate axiom states what
they prove. It needs a C++ compiler, `make`, `git`, `cmake` (the requirements file installs
one) and an internet connection, takes a few minutes, and prints six lines:

```
ok: ordinary and rescaled Taylor steps enclose the exact sine flow and its degree-3 jet
ok: checker 1 (CAPD) passes the control and the certificate
ok: checker 1 rejects corruptions c1, c2, c3
ok: checker 2 (arb) passes the control and the certificate
ok: checker 2 rejects corruptions c1, c2, c3
ok: the Lean certificate axiom's numbers match the certificate and both checkers' output
```

Any failure stops it with a line starting `FAIL:`. Everything it builds goes to a temporary
folder that is removed at the end.

## The certificate

`cert.txt` gives the square $\mathcal X$ (its center as two integers over $2^{40}$ and its
half-width $2^{-20}$) and the claimed ranges of the return time and of the trace of the
derivative of the first-crossing map $P$ from $z=0$ to $z=2\pi$. Its comment block states the
claims. `control-cert.txt` does the same for the integrable control flow
$x'=\cos y$, $y'=\sin x$, $z'=13/10$, whose return map is known exactly.

## Checker 1: CAPD

`get-capd.sh` downloads the CAPD library from its GitHub repository at a fixed commit of version
6.1.0 and builds it with machine intervals; `build.sh` compiles `bnf.cpp` against it. One
CAPD header is patched at build time (a `sed` line in `build.sh`): CAPD's `normalForms.h`
does not compile for jets with complex interval coefficients, because it converts a factorial
through the real type of the complex type, and the patch converts it to a `double` instead. It
leaves every formula unchanged; the factorials involved are small integers, exact in double
precision.

`bnf check cert.txt` integrates the flow with its variational equations to order 3 over all of
$\mathcal X$, encloses the crossing with $z=2\pi$, proves by the interval Newton method that
$P-\mathrm{id}$ has a unique zero $p$ in $\mathcal X$, encloses the return time and the trace,
checks $\sin y+\cos x\ge1.92$ (it finds at least $1.9215$) along every integration step, and
computes the Birkhoff normal form with CAPD's `computePlanarEllipticNormalForm`. That routine is
labeled area-preserving, while $P$ preserves $`V_z\,dx\wedge dy`$ rather than $dx\wedge dy$; its
formula uses only $\bar\lambda=1/\lambda$, which holds at the fixed point because
$\det DP(p)=1$, and the paper's Appendix B shows that its twist coefficient is a nonzero multiple
of the one defined there. `bnf control` runs the integrable control and compares with the exact
values.

## Checker 2: Arb

`check_arb.py` uses only ball arithmetic from Arb through python-flint, with its own Taylor
integrator (order 36, step $1/32$, with a priori enclosures), at 256-bit precision. It refines the
fixed point in high precision, proves by the Krawczyk method a unique zero of $P-\mathrm{id}$ in a
square of half-width $2^{-100}$ inside $\mathcal X$, encloses the trace and $\det DP(p)$, checks
$\sin y+\cos x$ along the whole orbit segment (at least $1.9378$ there), and computes the twist
coefficient of $\Phi\circ P\circ\Phi^{-1}$ in the area-preserving coordinates $\Phi$ of the
paper's Lemma 3. Floating-point numbers are used only to choose candidates and inflation radii;
every conclusion is checked in ball arithmetic. With `flow control` in the certificate it runs
the integrable control instead, which it reproduces to within $8\cdot10^{-29}$.

For a Taylor polynomial of order $N$ and step length $h$, the recurrence evaluated on the
a priori enclosure bounds the coefficient of order $N+1$, including its factorial.
Each state and variational-jet coefficient therefore receives that bound multiplied by
$h^N[0,h]$, which encloses the required remainder factor. The crossing-time evaluator uses
the same coefficient with the time offset raised to power $N+1$; the rescaled final step
uses length one. `check_remainder.py` tests both kinds of step at order two against the
exact flow $x'=\cos y$, $y'=1$, $z'=0$, including its degree-three variational jet;
the extra factor of $h$ would exclude the exact ordinary-step endpoint.

## Corrupted certificates

`run.sh` writes three corrupted copies of `cert.txt` and requires both checkers to reject each:
`c1` moves the center by $2^{-19}$, `c2` sets the upper trace bound to $-1.9646$, and `c3` sets
the upper return time to $3.2352$.

## The Lean certificate axiom

`cert_import.py CAPD_OUTPUT ARB_OUTPUT` reads the square from `lean/ABC/Flow.lean` and the
numbers of `ABC.CertFacts` from `lean/ABC/Cert.lean`, with exact rationals. It checks that the
square and the bounds on the return time and the trace are those of `cert.txt`, that the lower
bound $1.92$ on $\sin y+\cos x$ is at most both checkers' certified bounds, and that both
outputs end in a pass and state each imported fact, including the nonzero twist coefficient.

## Sources

Zlatoš's Theorem 1.1 is quoted from arXiv:0704.1163v2; the published text was not opened.
Mohammad El Smaily and Stéphane Kirsch (Arch. Ration. Mech. Anal. 213 (2014), Theorem B) restate
the published result in the same form. Pöschel's Theorem A is quoted from arXiv:0908.2234
(version 1.3, 2009), which carries small corrections to the 2001 printed text. We could not
obtain the full text of Huang, Zhao and Dai (1998); it predates the 2016 statement of Xin, Yu
and Zlatoš that a rigorous proof of vortex tubes was not known.

## Further credits

- A. Zlatoš, *Sharp asymptotics for KPP pulsating front speed-up and diffusion enhancement by
  flows*, Arch. Ration. Mech. Anal. 195 (2010), 441–453,
  [doi:10.1007/s00205-009-0282-1](https://doi.org/10.1007/s00205-009-0282-1);
  [arXiv:0704.1163](https://arxiv.org/abs/0704.1163): Theorem 1.1, the limit formula, and
  Remark 3, the positivity criterion.
- M. El Smaily and S. Kirsch, *Front speed enhancement by incompressible flows in three or
  higher dimensions*, Arch. Ration. Mech. Anal. 213 (2014), 327–354;
  [arXiv:1307.4106](https://arxiv.org/abs/1307.4106): Theorem B and Remark 2.
- J. Xin, Y. Yu and A. Zlatoš, *Periodic orbits of the ABC flow with A = B = C = 1*, SIAM J.
  Math. Anal. 48 (2016), 4087–4093; [arXiv:1601.02724](https://arxiv.org/abs/1601.02724): the
  question, in its introduction.
- T. McMillen, J. Xin, Y. Yu and A. Zlatoš, *Ballistic orbits and front speed enhancement for
  ABC flows*, SIAM J. Appl. Dyn. Syst. 15 (2016), 1753–1782;
  [arXiv:1606.01461](https://arxiv.org/abs/1606.01461), Section 1.
- J. Pöschel, *A lecture on the classical KAM theorem*, Proc. Sympos. Pure Math. 69 (2001),
  707–732; [arXiv:0908.2234](https://arxiv.org/abs/0908.2234): Theorem A.
- H. Berestycki and F. Hamel, *Front propagation in periodic excitable media*, Comm. Pure Appl.
  Math. 55 (2002), 949–1032: existence of pulsating fronts exactly for $`c\ge c^*`$.
- T. Dombre, U. Frisch, J. M. Greene, M. Hénon, A. Mehr and A. M. Soward, *Chaotic streamlines in
  the ABC flows*, J. Fluid Mech. 167 (1986), 353–391.
- L. Shen, J. Xin and A. Zhou, *Finite element computation of KPP front speeds in 3D cellular
  and ABC flows*, Math. Model. Nat. Phenom. 8 (2013), 182–197.
- M. Breden and J.-P. Lessard, *Polynomial interpolation and a priori bootstrap for
  computer-assisted proofs in nonlinear ODEs*, Discrete Contin. Dyn. Syst. Ser. B 23 (2018),
  2825–2858, [doi:10.3934/dcdsb.2018164](https://doi.org/10.3934/dcdsb.2018164);
  [arXiv:1704.03128](https://arxiv.org/abs/1704.03128).
- T. Kapela and C. Simó, *Rigorous KAM results around arbitrary periodic orbits for Hamiltonian
  systems*, Nonlinearity 30 (2017), 965–986.
- D. Wilczak and R. Barrio, *Systematic computer-assisted proof of branches of stable elliptic
  periodic orbits and surrounding invariant tori*, SIAM J. Appl. Dyn. Syst. 16 (2017), 1618–1649,
  [doi:10.1137/17M1113254](https://doi.org/10.1137/17M1113254).
- D. Wilczak and P. Zgliczyński, *$`C^r`$-Lohner algorithm*,
  [arXiv:0704.0720](https://arxiv.org/abs/0704.0720) (2007): the integrator CAPD uses for the
  derivatives of the first-crossing map.
- W. Szumiński and J. Llibre, *Dynamics, periodic orbits and C¹ non-integrability of the ABC
  flow*, [arXiv:2609.17449](https://arxiv.org/abs/2609.17449) (2026).
- D.-B. Huang, X.-H. Zhao and H.-H. Dai, *Invariant tori and chaotic streamlines in the ABC flow*,
  Phys. Lett. A 237 (1998), 136–140; not read in full (see Sources).
- T. Kapela, M. Mrozek, D. Wilczak and P. Zgliczyński, *CAPD::DynSys: a flexible C++ toolbox for
  rigorous numerical analysis of dynamical systems*, Commun. Nonlinear Sci. Numer. Simul. 101
  (2021), 105578; the library at [github.com/CAPDGroup/CAPD](https://github.com/CAPDGroup/CAPD).
- F. Johansson, *Arb: efficient arbitrary-precision midpoint-radius interval arithmetic*, IEEE
  Trans. Comput. 66 (2017), 1281–1292, now part of [FLINT](https://flintlib.org/), used through
  python-flint.
- The Lean 4 theorem prover (L. de Moura and S. Ullrich, CADE 28, 2021) and the Mathlib library
  (The mathlib Community, CPP 2020).
