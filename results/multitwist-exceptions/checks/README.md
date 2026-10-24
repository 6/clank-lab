# Checkers

`check.py` runs both checkers on the finite facts F0–F4 of the paper and on
four corruptions. It then runs the finite model and diagram checks for the
pseudo-Anosov-base extension:

```sh
python3 checks/check.py
```

Python 3.10 or later, standard library only. Both checkers are exact: words
in a free group, or integer vectors, with no floating point. Each prints one
JSON line at the end, `{"checker": ..., "kmax": ..., "checks": ...,
"failures": ..., "verdict": "ACCEPT" | "REJECT"}`, and exits with status 0
on ACCEPT and 1 on REJECT. `check.py` reads that line, so a crash never
counts as a rejection.

## The facts

The curves live on the sphere with five boundary components, modeled as the
disk $D$ with punctures $p_1, \dots, p_4$ on a diameter and the boundary
circle as the fifth. The curves $a, d, c, C', C$ are the round curves about
the punctures $\lbrace 1,2 \rbrace$, $\lbrace 2,3 \rbrace$,
$\lbrace 3,4 \rbrace$, $\lbrace 1,2,3 \rbrace$, $\lbrace 2,3,4 \rbrace$;
$f_k = T_a^k T_d$ and $t = T_a T_c^{\varepsilon}$ with
$\varepsilon = \pm 1$. Composition is right to left.

- F0. Each of $T_a, T_d, T_c, T_{C'}, T_C$ fixes its own curve.
- F1. In the cyclic order $a, d, c, C', C$, consecutive curves meet and the
  others are disjoint, tested as $T_u(v) \ne v$ or $T_u(v) = v$; the five
  curves are distinct.
- F2. $T_a T_c = T_c T_a$.
- F3. For each $k$ and $\varepsilon$: $t^0 f_k = T_a^k T_d$ fixes $C'$ and
  $t^{-k} f_k = T_c^{-\varepsilon k} T_d$ fixes $C$.
- F4. For each $k$: $T_a(f_k(a)) \ne f_k(a)$ and $T_c(f_k(a)) \ne f_k(a)$,
  so $f_k(a)$ meets $a$ and $c$.

The step from a disjointness test to intersection numbers uses
$i(u, v) = 0 \iff T_u(v) = v$ (Farb and Margalit, *A Primer on Mapping
Class Groups*, Prop. 3.2). The checkers test the facts for
$k = 1, \dots, 30$; the Lean proof in `../lean/` proves them for every $k$.
For F0–F4, the two checkers implement one list of facts in two models, so
they guard against errors of computation. The extension's finite diagram
checks are described below. The identification of the models and diagram
with surface curves, and the surface argument that turns these facts into
the theorem, remain part of the written proof in the paper.

## Checker A: the free group

`check_free_group.py` works in the fundamental group of the four-punctured
disk, free on loops $x_1, \dots, x_4$ around the punctures. The half twists
act by the Artin automorphisms
$\sigma_i: x_i \mapsto x_i x_{i+1} x_i^{-1}$, $x_{i+1} \mapsto x_i$, and the
twists about the round curves are $T_a = \sigma_1^2$, $T_d = \sigma_2^2$,
$T_c = \sigma_3^2$, $T_{C'} = (\sigma_1 \sigma_2)^3$,
$T_C = (\sigma_2 \sigma_3)^3$. A simple closed curve is its conjugacy class
up to inversion, compared by the least rotation of the cyclically reduced
word or of its inverse. The curves are the classes of $x_1 x_2$, $x_2 x_3$,
$x_3 x_4$, $x_1 x_2 x_3$ and $x_2 x_3 x_4$. Options: `--kmax K` (default 12;
`check.py` uses 30), `--curves FILE` to replace curve words from a JSON file
(the corruptions), `--quiet`.

## Checker B: Dynnikov coordinates

`check_dynnikov.py` was written separately, from the statement of the facts
alone, without access to checker A or the Lean proof. It uses nothing from
the free group.

- Curves. A multicurve in the four-punctured disk is encoded by its
  Dynnikov coordinates $(a_1, a_2; b_1, b_2) \in \mathbb{Z}^4 \setminus \lbrace 0 \rbrace$
  (Dynnikov 2002; Hall and Yurttaş 2009, arXiv 0808.3053). The encoding is a
  bijection, so two curves are isotopic exactly when their vectors are
  equal. The round curves have the hand-computed coordinates
  $a = (0,0;1,0)$, $d = (0,0;-1,1)$, $c = (0,0;0,-1)$, $C' = (0,0;0,1)$,
  $C = (0,0;-1,0)$, which the program re-derives from the arc counts.
- Braid action. The half twists $\sigma_i^{\pm 1}$ act by the update rules
  of Hall and Yurttaş (Lemmas 4 and 5), cross-checked against the uniform
  rule of Yurttaş and Hall 2018 (arXiv 1711.00895, Theorem 5). The twists
  are the same braids as in checker A.
- Intersection numbers. Computed exactly in two ways: by the twist test
  $i(u,v) = 0 \iff T_u(v) = v$, and by the formula of Yurttaş and Hall
  (Lemma 9) for the intersection number with a round curve, using
  $i(g(R), L) = i(R, g^{-1}(L))$ for other curves.

Before checking F0–F4, the program validates the model on 624 small
coordinate vectors, 300 random vectors and 300 random braid images of the
round curves: each $\sigma_i \sigma_i^{-1}$ acts trivially, the braid and
commutation relations hold, the full twist $(\sigma_1 \sigma_2 \sigma_3)^4$
acts trivially, and the arc counts are consistent. On 400 random cases it
checks $`i(T_R^m(v), v) = |m|\, i(R, v)^2`$, which confirms the update rules,
the intersection formula and that each twist is a single Dehn twist about
the intended curve. It then checks F0–F4 for $k \le 30$ and both signs,
including the literal products $t^0 f_k$ and $t^{-k} f_k$ (not only their
simplified forms), and the exact values $i(a, f_k(a)) = i(c, f_k(a)) = 4$.
The computed intersection numbers of the pentagon are 2 for the five
consecutive pairs and 0 for the others. Options: `--kmax K` (default 30),
`--corrupt K1|K2|K3|K4`, `--mirror` (every twist reversed), `--verbose`.

## Corruptions

Both checkers must reject each of these:

| | Change | Checker A input |
|---|---|---|
| K1 | $C$ replaced by $T_a(C)$ | `../data/corrupt/K1-C-moved.json` |
| K2 | $C'$ replaced by $T_c(C')$ | `../data/corrupt/K2-Cprime-moved.json` |
| K3 | $C$ and $C'$ exchanged | `../data/corrupt/K3-C-Cprime-swapped.json` |
| K4 | $c$ replaced by $T_{C'}^{-1}(c)$ | `../data/corrupt/K4-c-moved.json` |

Each JSON file gives the replaced curve words for checker A (positive
integer $g$ for $x_g$, negative for its inverse); checker B builds the same
four corruptions itself (`--corrupt`). In each case the pentagon pattern
and a fixed-curve fact fail, and both checkers report REJECT.

## Pseudo-Anosov-base extension

For $k \ge 1$, the extension uses

$$
g_k = T_a^{-1}T_c^{-(k+1)}T_d, \qquad t=T_aT_c.
$$

The entry point runs `extension/replay.py`, which can also be run directly:

```sh
python3 checks/extension/replay.py
```

`extension/check_free_group.py` imports the free-group model above and
checks $k=1,\dots,12$, both global twist handednesses, and the integer
exponents $-2,-1,0,1,2,k,k+1,k+2$. It checks the identity
$t^n g_k=T_a^{n-1}T_c^{n-k-1}T_d$ as an equality of free-group
automorphisms, the fixed curves $C$ at $n=1$ and $C'$ at $n=k+1$, and the
twist tests showing that $g_k(a)$ meets $a$ and $c$.

`extension/check_dynnikov.py` imports the independently written Dynnikov
model above. It validates that model, then checks $k=1,\dots,8$, both
global handednesses, and exponents $n=-3,-2,-1,0,1,2,3,k,k+1,k+2$.
For the identity it compares actions on nine specified coordinate vectors;
it also checks the two fixed curves and the exact intersection numbers
$i(a,g_k(a))=i(c,g_k(a))=4$. Both drivers reject the four original curve
corruptions. The free-group driver also rejects reversed factor order and
a wrong exponent. The Dynnikov driver rejects the six inputs
`extension/corruptions/model/*.json`, changing an exponent or a composition
order. Expected rejections must have the mathematical verdict and exit
status; a crash does not pass a negative control.

`extension/topology.json` gives exact rectangle boundaries and the five
punctures. `extension/check_topology.py` uses a rectilinear grid
decomposition. `extension/check_topology_independent.py` independently
reconstructs the crossings, directed edges, cyclic rotations and facial
boundaries using rational arithmetic. Both verify the specified pentagon
incidences and puncture partitions. For $a,d,c$, they establish four
crossings and six complementary disks on the capped sphere: four
punctured bigons, one unpunctured quadrilateral and one punctured outer
quadrilateral. Replacing the punctures by boundary circles makes the five
punctured regions peripheral annuli. They also check that $a,c$ cut the
surface into the specified three pairs of pants.

The complete independent facial certificate is
`extension/topology-independent-certificate.json`. The replay regenerates
it and compares all parsed fields. Both topology checkers must reject the
three supplied diagram corruptions (a moved puncture, changed crossings
and a deleted face). The independent checker also rejects seven mutations,
including a deleted occurrence of a crossing in its reconstructed graph,
and accepts a rational affine change of coordinates and a puncture moved
within its face.

These model checks cover only the stated finite parameter sets. The
Artin algebra for every $k$ and $n$ is proved separately in `../lean/V2.lean`;
it is not inferred from these samples. The diagram checkers establish
properties of the finite rational embedding. The written proof identifies
that embedding and the two algebraic models with the paper's actual
surface curves and twists, applies Penner's theorem to obtain the
pseudo-Anosov bases, and uses the pants classification, intersection and
fixed-curve facts to obtain filling and widely separated exceptions.
Those surface identifications and cited topological theorems are not
formalized by these Python checks or by the Lean algebra.
