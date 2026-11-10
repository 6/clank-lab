# Checkers

`python3 checks/check.py`, run from the result's folder, runs two exact checkers on `data/small-paths.json` and then on two corrupted copies of it, and prints `PASS: six asymmetric periodic paths, periods 8, 10, 30, 42, 58 and 102`. It needs Python 3.10 or later and its standard library only (`requirements.txt` lists nothing else). The run takes about a second on one core, with under 50 MB of memory.

These programs check the paper's Proposition 5.1. The rest of the proof is the Lean development in `../lean/`, with the cited period theorem as its one axiom.

## The data

`data/small-paths.json` lists six trajectories. Each entry gives the half-period `l` and the `period` $2l$; the starting side `wall` (always 0, the side from vertex 0 to vertex 1) and the starting point's fraction `u0` along it (always 1/200); and the initial direction `dir` as two pairs of rationals $[[x_1, x_2], [y_1, y_2]]$, meaning the direction $(X, \sigma Y)$ with $X = x_1 + x_2\sqrt{5}$, $Y = y_1 + y_2\sqrt{5}$ and $\sigma = \sin 72^\circ$. The vertices of the pentagon are at angles $0^\circ, 72^\circ, \dots, 288^\circ$ on the unit circle. The field `orbit_vector` records the orbit vector $(a, b, c, d)$ in whose direction the trajectory was found; the checkers do not read it.

## The programs

`paths_sqrt5.py` stores points as $(X, Y)$ with $x = X$ and $y = \sigma Y$, with $X, Y$ in $\mathbb{Q}(\sqrt{5})$, and decides signs exactly. From the start it repeatedly finds the side hit at the least positive time among the sides other than the current one, rejects a hit at a vertex, and reflects the direction in that side. It stops at the first return of the full state (side, point, direction), requires that return after exactly $2l$ bounces, and then checks that the rotation of the initial point and direction by $72^\circ$ is not among the $2l$ states, so that the rotation does not map the trajectory to itself.

`paths_zeta.py` was written separately and imports nothing from the other program. It works in the cyclotomic field $\mathbb{Q}(\zeta)$, $\zeta = e^{2\pi i/5}$, with the vertices at $\zeta^k$; the reflection in side $k$ sends a direction $d$ to $-\zeta^{2k+1}\bar d$ and the rotation is multiplication by $\zeta$. Real quantities are reduced to $\mathbb{Q}(\sqrt{5})$ to decide signs. It makes the same checks.

## Corrupted data

`check.py` also writes two corrupted copies of the data and requires both programs to reject each:

1. the half-period of the period-42 trajectory relabeled 22: rejected because the trajectory closes after 42 bounces, not 44;
2. the first coordinate of the period-10 direction changed to $-37/10$: rejected because the trajectory does not close within the allowed number of bounces.

## Further credits

- Diana Davis and Samuel Lelièvre, *Periodic paths on the pentagon, double pentagon and golden L*, [arXiv:1810.11310v2](https://arxiv.org/abs/1810.11310v2) (July 23, 2024; version 1 October 26, 2018). Section 4.1 states Conjecture 4.3: "Every even number arises as the combinatorial period of an asymmetric periodic billiard trajectory on the pentagon, other than 2, 12, 14 and 18. We have verified this up to period 4000." Proposition 4.2 shows that every positive multiple of 10 is the period of a rotationally symmetric trajectory.
- Alex Kontorovich and Xin Zhang, *On the local-global conjecture for combinatorial period lengths of closed billiards on the regular pentagon*, International Mathematics Research Notices 2025, no. 15, rnaf227, [doi:10.1093/imrn/rnaf227](https://doi.org/10.1093/imrn/rnaf227); [arXiv:2409.10682](https://arxiv.org/abs/2409.10682) (September 16, 2024). Conjecture 1.1 restates the question; Theorem 1.2 proves it for almost every even number; Theorem 1.4 shows that evenness is the only congruence obstruction; Section 2 gives the semigroup $\Gamma^+$, the identification of the long saddle connections in the first quadrant with $\Gamma^+ \cdot (0,1)^t$, and Theorem 2.1, the cited input; Section 4 produces periods from the vectors of $B^m A^n B^k$.
- Diana Davis, Dmitry Fuchs and Serge Tabachnikov, *Periodic trajectories in the regular pentagon*, Moscow Mathematical Journal 11 (2011), no. 3, 439–461, [arXiv:1102.1005](https://arxiv.org/abs/1102.1005): Theorem 11, the period theorem in its original form, which Kontorovich and Zhang's Theorem 2.1 and Davis and Lelièvre's Theorem 3.30 restate in the golden L coordinates.
- Leonardo de Moura and Sebastian Ullrich, *The Lean 4 theorem prover and programming language*, CADE 28 (2021): the proof assistant.
