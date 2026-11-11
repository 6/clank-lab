# Checkers

`sh checks/check.sh`, run from the result's folder, runs the three checkers on `data/certificate.json` and then on six corrupted copies of it, with Python's standard library alone, and prints `PASS: 3 checkers accept the certificate and reject all 6 corruptions`. It requires each checker's acceptance line in its output, not just its exit status, and a `REJECT:` line for each corruption. The whole run takes under a second on one core, with under 50 MB of memory.

The paper's proof (its Section 2) is written out by hand and does not depend on these programs. They check the same four pieces independently of that proof.

## The certificate

`data/certificate.json` holds, with every number an exact rational written as a string such as `"2/3"`:

- `S`: the five vertices of the simplex $S$ (in the order $v_2, v_3, v_4, v_1, v_0$ of the paper);
- `phi`: the matrix $\Phi$ of the map $\varphi(x) = (x_1+x_2, x_1-x_2, x_3+x_4, x_3-x_4)$, which is $\sqrt{2}$ times an orthogonal matrix, so $T = \varphi(S)$ is $S$ scaled by $\sqrt{2}$;
- `pieces`: four entries, each an orthogonal matrix `M`, a translation `t` and the five `vertices` of the piece $M S + t$, listed as the images of the vertices of `S` in order;
- `separators`: for each pair of pieces, a hyperplane (`normal`, `offset`) with the first piece on the side `side_of_first` and the second on the other;
- `claim`: one line of text, not read by the checkers.

The pieces are numbered from 0, as in the paper: piece 0 is $S$ itself, and pieces 1 and 3 are mirror images ($\det M = -1$).

## The programs

`check_certificate.py` checks that $S$ is nondegenerate, that $\Phi^{\mathsf T}\Phi = 2I$ and the volume of $T$ is four times that of $S$, that each `M` is orthogonal and the listed vertices are $M S + t$, that every piece vertex has nonnegative barycentric coordinates with respect to $T$, that each pair of pieces lies on opposite closed sides of its listed hyperplane, and that the four piece volumes add up to the volume of $T$. It prints the volumes and the four determinants $1, -1, 1, -1$.

`check_independent.py` was written separately and imports nothing from the other programs. It requires $S$ and $\Phi$ to equal the simplex and map of the paper's theorem, ignores the listed hyperplanes, and checks congruence twice (each `M` orthogonal with vertices $M S + t$, and the ten squared edge lengths of each piece equal to those of $S$). It checks containment by the five facet inequalities of $T$. For each pair of pieces it enumerates the vertices of their intersection exactly and confirms that it has dimension at most 3. Finally it checks that the volumes add up. It prints `vol(S) = 1/576` and `vol(T) = 1/144`.

`check_alcoves.py` ignores `M`, `t` and the separators. It evaluates all 48 roots $\alpha$ of $F_4$ (Bourbaki's coordinates: $\pm e_i$, $\pm e_i \pm e_j$ and $`\frac12(\pm e_1 \pm e_2 \pm e_3 \pm e_4)`$) on the vertices of $S$ and of each piece, and checks that for every root the five values $\langle \alpha, v \rangle$ lie in one interval $[n, n+1]$ with $n$ an integer, so that each simplex lies in one closed alcove of the arrangement of hyperplanes $\langle \alpha, x \rangle = n$. It also checks that the pieces have the volume of $S$ and four distinct vertex sets, that their vertices lie in $T$, and that $T$ has four times the volume of $S$. Since $S$ is an alcove (the paper, Section 3), the pieces are then four distinct alcoves inside $T$, and distinct alcoves have disjoint interiors.

Closed convex pieces inside $T$ with disjoint interiors and total volume equal to that of $T$ cover $T$. So each of the first two programs alone verifies that $T$ is tiled by four congruent copies of $S$; applying $\varphi^{-1}$ then tiles $S$ by four copies of itself scaled by $1/\sqrt{2}$.

## Corrupted certificates

`corrupt.py` writes six corrupted copies into a temporary folder, and `check.sh` requires each to be rejected by every program that reads the corrupted field:

1. `vertex-moved`: one vertex of piece 2 moved; rejected by all three programs.
2. `phi-not-similarity`: one entry of $\Phi$ changed; rejected by all three.
3. `piece-duplicated`: piece 3 replaced by a copy of piece 1; rejected by all three.
4. `piece-dropped`: piece 3 and its separators removed; rejected by all three.
5. `separator-shifted`: one listed hyperplane moved; rejected by `check_certificate.py`, the only program that reads the separators.
6. `M-not-orthogonal`: one entry of a matrix `M` changed; rejected by `check_certificate.py` and `check_independent.py` (the alcove check ignores `M`).

## Further credits

- J. Matoušek and Z. Safernová, *On the nonexistence of k-reptile tetrahedra*, Discrete & Computational Geometry 46 (2011), 599–609, [doi:10.1007/s00454-011-9334-z](https://doi.org/10.1007/s00454-011-9334-z); [arXiv:1006.1807](https://arxiv.org/abs/1006.1807) (June 9, 2010), Conjecture 1.2 and the three-dimensional theorem.
- J. Kynčl and Z. Patáková, *On the nonexistence of k-reptile simplices in* $\mathbb{R}^3$ *and* $\mathbb{R}^4$, Electronic Journal of Combinatorics 24(3) (2017), #P3.1, [doi:10.37236/6113](https://doi.org/10.37236/6113); [arXiv:1602.04668](https://arxiv.org/abs/1602.04668) (February 15, 2016): the definition of a $k$-reptile simplex, Theorem 1.3 ($k$ must be a square in dimension four), and the question answered here, Problem 1.4 of the published version and Problem 2 of the arXiv version.
- A. A. Felikson and P. V. Tumarkin, *Reflection subgroups of Euclidean reflection groups*, Sbornik: Mathematics 196 (2005), 1349–1369; [arXiv:math/0402403](https://arxiv.org/abs/math/0402403) (February 25, 2004), Lemma 10: the index-4 reflection subgroup of the affine reflection group of type F4 whose fundamental simplex is similar to the alcove. The tiling checked here is this subdivision.
- N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Springer, 2002, Plate VIII: the coordinates of the root system of type F4.
- H. Maehara, *Some replicating simplices other than Hill-simplices*, Beiträge zur Algebra und Geometrie 55 (2014), 429–432, [doi:10.1007/s13366-013-0152-8](https://doi.org/10.1007/s13366-013-0152-8): further reptile simplices, with $k = 2^d$ as Kynčl and Patáková describe them; not read in full.
- E. Hertel, *Self-similar simplices*, Beiträge zur Algebra und Geometrie 41 (2000), 589–595: Hill simplices and their $m^d$-reptile tilings. Hertel's *A class of self-similar d-polytopes*, Revue Roumaine de Mathématiques Pures et Appliquées 50 (2005), 647–655, extends this to H-simplotopes (pp. 650–652); its Conjecture 2 (p. 652), that for $d > 2$ an $f$-replicating simplex must have $f = m^d$ and be an H-simplex, is also refuted here.
- H. Maehara and H. Martini, *Circles, Spheres and Spherical Geometry*, Birkhäuser, 2024, Chapter 11, "Higher Dimensions": its reference list includes the Hill-simplex and replicating-simplex papers of Hadwiger, Hertel and Maehara; only its abstract and reference list were read.
