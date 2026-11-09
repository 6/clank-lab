# KPP fronts in the 1-1-1 ABC flow speed up linearly in every direction

[![Checks](https://github.com/6/clank-lab/actions/workflows/abc-front-speedup.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/abc-front-speedup.yml)

The [Arnold–Beltrami–Childress (ABC) flow](https://en.wikipedia.org/wiki/Arnold%E2%80%93Beltrami%E2%80%93Childress_flow) with $A=B=C=1$ is the steady, periodic, incompressible velocity field $V(x,y,z)=(\sin z+\cos y,\ \sin x+\cos z,\ \sin y+\cos x)$, a standard model of a chaotic three-dimensional flow. Stir a reacting medium, such as a flame or a spreading population, with $K$ times this flow: the reaction–diffusion equation $`T_t+K\,V\cdot\nabla T=\Delta T+f(T)`$ with a [KPP reaction](https://en.wikipedia.org/wiki/Fisher%27s_equation) $f$ has traveling fronts in every direction $e$, and $`c^*_e(K)`$ is the smallest front speed. Andrej Zlatoš proved in 2010 that $`c^*_e(K)/K`$ has a limit as $K\to\infty$, equal to a supremum over first integrals of the flow, and that it is positive exactly when some first integral $w$ of the flow has $`\int (V\cdot e)\,w\ne 0`$. In 2016 Jack Xin, Yifeng Yu and Zlatoš ([arXiv:1601.02724](https://arxiv.org/abs/1601.02724)) pointed out that a positive-measure "vortex tube" of streamlines moving roughly linearly would make the limit positive for this flow, but that "a rigorous proof of their existence is currently not known"; Tyler McMillen, Xin, Yu and Zlatoš added that KAM theorems "do not provide any regularity of the set of quasi-periodic orbits".

We prove that for every unit vector $e$ and every KPP reaction $f$ in Zlatoš's sense, the limit $`\lim_{K\to\infty}c^*_e(K)/K`$ exists and is positive: fronts in the 1-1-1 ABC flow speed up linearly in every direction. Two independent interval-arithmetic programs certify an elliptic periodic orbit with nonzero twist. Jürgen Pöschel's [KAM theorem](https://en.wikipedia.org/wiki/Kolmogorov%E2%80%93Arnold%E2%80%93Moser_theorem) with frequencies as parameters then gives a family of invariant curves around it with a Lipschitz label, and that label gives the first integral Zlatoš's formula needs. Along the way we show that a vortex tube exists: an open set of positive measure, made of whole streamlines, on which the vertical velocity $\sin y+\cos x$ stays above a positive constant, so that each of its streamlines climbs in $z$ at least linearly in time.

Written proof, with Lean and computer checks; not yet reviewed by experts.

The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.24072734](https://doi.org/10.5281/zenodo.24072734)

This DOI identifies version 1; version 2 corrects the build checks.

## Check it

The deduction of the theorem from the certified orbit and from the theorems of Zlatoš and Pöschel is proved in Lean 4 with Mathlib. The two cited theorems enter as axioms, stated with all their hypotheses, and the certified facts about the orbit as a third axiom; the [Lean documentation](lean/README.md) lists them and explains how the formal statement matches the paper's theorem. With [elan](https://github.com/leanprover/elan) installed, from this folder:

```sh
cd lean
lake exe cache get
lake build
```

The build checks the proof and the exact list of axioms it uses. With the Mathlib cache it takes about 15 minutes of processor time and about 7 GB of memory.

The two programs that certify the orbit run from one script. It needs Python 3.10 or later, a C++ compiler, `make`, `git` and an internet connection (it downloads and builds the CAPD library at a fixed commit). From this folder:

```sh
python3 -m pip install -r checks/requirements.txt
sh checks/run.sh
```

It takes a few minutes and prints five lines starting `ok:`. Each program checks an integrable control with known exact values, then the certificate, then rejects three corrupted certificates; a last step checks that the numbers in the Lean axiom are those the programs certify. The [checker documentation](checks/README.md) describes each step.

## Credits

The question comes from Jack Xin, Yifeng Yu and Andrej Zlatoš (*Periodic orbits of the ABC flow with A = B = C = 1*, SIAM Journal on Mathematical Analysis, 2016) and from Tyler McMillen, Xin, Yu and Zlatoš (SIAM Journal on Applied Dynamical Systems, 2016). The proof rests on two theorems used exactly as published: Zlatoš's limit formula for KPP front speeds (*Sharp asymptotics for KPP pulsating front speed-up and diffusion enhancement by flows*, Archive for Rational Mechanics and Analysis, 2010), extended to periodic domains by Mohammad El Smaily and Stéphane Kirsch (2014), and Jürgen Pöschel's KAM theorem (*A lecture on the classical KAM theorem*, 2001). The numerical study of this flow's streamlines by Thierry Dombre, Uriel Frisch, John Greene, Michel Hénon, A. Mehr and Andrew Soward (1986) is where Xin, Yu and Zlatoš trace the vortex tubes.

Maxime Breden and Jean-Philippe Lessard gave computer-assisted proofs for ABC flows (2018); Tomasz Kapela and Carles Simó, and Daniel Wilczak and Roberto Barrio, combined rigorous normal forms with KAM theory around periodic orbits (2017). Wojciech Szumiński and Jaume Llibre recently studied periodic orbits of ABC flows near the integrable cases (2026). The orbit is certified with the CAPD library and with Fredrik Johansson's Arb through python-flint, and the deduction is checked in Lean with Mathlib. [Further credits](checks/README.md#further-credits) give the exact references.

Apache-2.0 (see the repository's LICENSE).

## Cite

```bibtex
@misc{GrahamAbcFrontSpeedup2026,
  author = {Graham, P.},
  title = {{KPP fronts in the 1-1-1 ABC flow speed up linearly in every direction}},
  year = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/abc-front-speedup-v2/results/abc-front-speedup}},
  doi = {10.5281/zenodo.24072734}
}
```
