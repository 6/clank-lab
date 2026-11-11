# Checkers

`sh checks/check.sh`, run from the result's folder after installing `checks/requirements.txt`, runs every program below and stops at the first failure. It requires each program's expected output, not only its exit status. The whole run takes about 26 CPU-seconds on one core and under 200 MB of memory, and ends with:

```
PASS: mu(G1) >= 6 and mu(G2) >= 6, and neither has a Heawood-family minor;
each has exactly one proper non-2-apex minor up to isomorphism (H = G1 - {1,10}), so G1 or H is an excluded minor for mu <= 5 outside the family;
G1 and G2 are 3-apex, so with the cited bounds mu(G1) = mu(G2) = 6
```

The upper bound $\mu \le 6$ and the step from the computations to the corollary are proved in the paper (Sections 5 and 1.3); the programs check the finite facts those proofs use.

## The data

- `data/graphs.g6`: the two graphs, ``G1 J?bFF`wNA{?`` and `G2 K?BD@jguAsBo`, in the graph6 format, with vertices numbered from 0.
- `data/G1-cert.json`, `data/G2-cert.json`: one certificate each. Fields: `graph6`; the split `S` (six vertices) and `T` (the rest); `C_rows_T_order`, the $T \times T$ block $C$ as exact rationals in the order of `T`; `B_fixed`, the fixed entries of the $S \times T$ block $B$, keyed by vertex pair; `unknowns`, the positions of the remaining edges between $S$ and $T$; `u_mid`, decimal values for those unknowns; and `box_radius`, the radius $10^{-40}$ of the box about `u_mid`. The field `format` repeats this description. The matrix $M$ has the blocks $A$ and $B$ in the rows indexed by $S$ and the blocks $B^{\mathsf T}$ and $C$ in the rows indexed by $T$, with $A = BC^{-1}B^{\mathsf T}$, as in Section 3 of the paper.
- `data/minor-controls.g6`: three graphs that do contain Heawood-family minors ($K_7$ plus an edge, a subdivided Heawood graph plus an edge, and $G_1$ plus the edge $`\{0,1\}`$), which the minor search must find.

## The programs

`check_cert.py CERT` reads only the certificate. It decodes the graph6 string itself, checks the sign pattern of $C$ and $B$ against the graph, and recomputes the non-adjacent pairs in $S$, one equation $f_{ij}(u) = b_i C^{-1} b_j^{\mathsf T} = 0$ for each. It computes the inertia of $C$ exactly from its characteristic polynomial (python-flint) by Descartes' rule of signs, then runs Krawczyk's test (Lemma 5 of the paper) at 300 bits in mpmath interval arithmetic, with $C^{-1}$ enclosed from exact rationals, requiring inclusion in the interior of the box. Over the whole box it checks that the unknowns and the entries of $A$ on edges inside $S$ are negative. Finally it proves the Strong Arnold Property (Lemma 6): the exact Gram matrix of $X \mapsto M_0 X$ at the rational box center, minus $10^{-6} I$, is positive definite, and $\lVert M - M_0 \rVert_F$ over the box is below $10^{-3}/2$.

`checker_a.py` was written separately, from a description of the certificate format only, and shares no code with `check_cert.py`. It works in exact rational arithmetic throughout. It computes the inertia of $C$ by symmetric elimination and by Descartes' rule and requires them to agree. It runs Krawczyk's test exactly, using that $f$ is quadratic with a constant Hessian, so the Jacobian over the box is bounded entrywise without interval arithmetic. It bounds the entries of $A$ over the box. It proves the Strong Arnold Property in two forms, directly as injectivity of $X \mapsto MX$ and through the kernel of $M$ (injectivity of $Z \mapsto KZK^{\mathsf T}$ restricted to the diagonal and edges, where the columns of $K$ span $\ker M$), each by an exact $LDL^{\mathsf T}$ factorization and Weyl's inequality. NumPy is used only to guess a rational number that is then checked exactly. With `--corrupt` it runs its own corruption suite: flipped signs in $C$, a moved box center, and every single-bit change of every graph6 character, 146 corrupted certificates in all, each of which must be rejected.

`family.py OUT` generates the Heawood family from $K_7$ and $K_{3,3,1,1}$ by closing under $\Delta Y$ and under those $Y\Delta$-transformations whose result is simple, and prints `78` graphs, 20 with 21 edges and 58 with 22. `checker_b.py family` generates it separately and prints the same counts.

`minor_exclusion.py GRAPHS FAMILY` lists, up to isomorphism, every graph obtained from each input graph by at most two edge deletions or contractions, with isolated vertices removed, keeping those with at least as many edges as the smallest family graph, 21 (Lemma 7 of the paper; 354 classes for $G_1$ and 455 for $G_2$, which `check.sh` requires), and compares each with the 78 family graphs. Every family graph has 21 or 22 edges, so the bound loses none of them; it drops graphs that lose more edges, as when an edge of a triangle is contracted. It must find a Heawood minor in each control graph and none in $G_1$ or $G_2$. `checker_b.py minors` decides the same question differently, by searching for branch sets of each Heawood graph in $G_1$ and $G_2$, and cross-checks by deletion and contraction; it also finds the planted controls.

`apex_minors.py GRAPHS` uses NetworkX's planarity test on all vertex pairs and triples. It checks that $G_1$ and $G_2$ are 3-apex, and searches their minors one deletion or contraction at a time, expanding only graphs that are not 2-apex (complete because minors of 2-apex graphs are 2-apex; Lemma 8 of the paper). It reports that the non-2-apex minors are $G_i$ itself and one graph isomorphic to $H = G_1 - \lbrace 1, 10 \rbrace$. `check.sh` then checks the facts the proof of Lemma 8 adds: $G_1$ and $G_2$ have 23 edges and minimum degrees 4 and 3, $H$ has 22 edges, and deleting or contracting any one edge of $G_1$ or $G_2$ leaves minimum degree at least 2.

`figure.py GRAPHS` draws Figure 1 of the paper as TikZ from `data/graphs.g6`. `figure.py --check GRAPHS paper/paper.tex` reads the drawing back from the paper and requires its two pictures to have exactly the edges of $G_1$ and $G_2$, the dashed edge to be $\lbrace 1, 10 \rbrace$ (so that removing it gives $H$), the thick edges of $G_1$ with it to form the triangle $\lbrace 1, 5, 10 \rbrace$, and the thick edges of $G_2$ to be the three edges at vertex 7, with the $\Delta Y$-transformation on that triangle relating the two graphs.

## Corrupted certificates

The paper summarizes these tests in one sentence; this is the full list. `corruptions.py DIR` writes corrupted copies of `data/G1-cert.json` and requires `check_cert.py` to reject each with a specific failure:

1. one edge entry of $C$ made positive: the sign check;
2. one graph6 character changed: a nonzero entry of $C$ on a non-edge;
3. the box center moved by $10^{-30}$: Krawczyk's test;
4. a fixed entry of $B$ made positive: the sign check;
5. the diagonal of $C$ increased by 100: Krawczyk's test;
6. $C$ given a second negative eigenvalue: the inertia check;
7. the Strong Arnold Property test applied to a matrix that lacks it: rejected.

## Further credits

- Y. Colin de Verdière, *Sur un nouvel invariant des graphes et un critère de planarité*, Journal of Combinatorial Theory, Series B 50 (1990), 11–21: the invariant, its minor-monotonicity and the planar case.
- H. van der Holst, L. Lovász and A. Schrijver, *The Colin de Verdière graph parameter*, in Graph Theory and Combinatorial Biology, Bolyai Society Mathematical Studies 7 (1999), 29–85; [preliminary version](https://homepages.cwi.nl/~lex/files/cdvsurvey_new2.pdf) (March 1997), whose numbering the paper uses: definition 1.1, statement 1.4, Theorems 2.4 and 2.7.
- L. Lovász and A. Schrijver, *A Borsuk theorem for antipodal links and a spectral characterization of linklessly embeddable graphs*, Proceedings of the AMS 126 (1998), 1275–1285, and N. Robertson, P. Seymour and R. Thomas, *Sachs' linkless embedding conjecture*, Journal of Combinatorial Theory, Series B 64 (1995), 185–227: the case $\mu \le 4$.
- H. van der Holst, *Graphs and obstructions in four dimensions*, Journal of Combinatorial Theory, Series B 96 (2006), 388–404, [doi:10.1016/j.jctb.2005.09.004](https://doi.org/10.1016/j.jctb.2005.09.004): the 4-flat graphs and the conjectures tested here.
- A. Georgakopoulos and M. Winter, *On 2-complexes embeddable in 4-space, and the excluded minors of their underlying graphs*, [arXiv:2408.12681v1](https://arxiv.org/abs/2408.12681v1) (August 22, 2024): Conjectures 1.1 and 1.4, footnote 1 and Theorem 6.1.
- T. W. Mattman and A. Pavelescu, *Three thousand obstructions to knotless embedding*, [arXiv:2607.01414v1](https://arxiv.org/abs/2607.01414v1) (July 1, 2026): Conjecture 4, the prediction of Section 3, and the list in Appendix A from which the two graphs are taken.
- H. Kim and T. W. Mattman, *Dips at small sizes for topological graph obstruction sets*, Discrete Applied Mathematics 360 (2025), 139–166, [doi:10.1016/j.dam.2024.08.022](https://doi.org/10.1016/j.dam.2024.08.022); section numbers as in [arXiv:2205.14255v2](https://arxiv.org/abs/2205.14255v2): the 23-edge graphs (their $G_2$ and $G_3$ are $G_1$ and $G_2$ here), the name $H_2$ for $H$, and the fact that every graph obtained from $G_1$ or $G_2$ by one edge deletion or contraction is 2-apex except $H$ (§§3.1, 3.3).
- T. W. Mattman and M. Pierce, *The $`K_{n+5}`$ and $`K_{3^2,1^n}`$ families and obstructions to $`n`$-apex*, in Knots, Links, Spatial Graphs, and Algebraic Invariants, Contemporary Mathematics 689 (2017), 137–158, [doi:10.1090/conm/689/13856](https://doi.org/10.1090/conm/689/13856); [arXiv:1603.00885v1](https://arxiv.org/abs/1603.00885v1), §2: the graph $H$ (their second 22-edge edge list, with labels shifted by one), found by computer search as minor-minimal among graphs that are not 2-apex.
- R. Krawczyk, *Newton-Algorithmen zur Bestimmung von Nullstellen mit Fehlerschranken*, Computing 4 (1969), 187–201, and R. E. Moore, *A test for existence of solutions to nonlinear systems*, SIAM Journal on Numerical Analysis 14 (1977), 611–615: the interval test.
- A. Hagberg, D. Schult and P. Swart, *Exploring network structure, dynamics, and function using NetworkX*, Proceedings of SciPy 2008, 11–15; F. Johansson and others, mpmath; the FLINT team, FLINT and python-flint; C. R. Harris and others, *Array programming with NumPy*, Nature 585 (2020), 357–362.
