# Exact certificate and attainment checks

From the result's top directory, with Python 3.10 or later:

```sh
python3 checks/check.py
```

Only the Python standard library is used; `requirements.txt` is empty.
This entry point checks the finite certificates, their transcription into
Lean, six corrupted certificates, and the connected graph attaining four
pairwise strongly cospectral vertices. It also checks that the optional
illustration reproduces the graph. The Lean proof is checked separately
with the ordinary Lake commands in [lean/README.md](../lean/README.md).

`check_cert.py` is an independent exact checker. For every triple $(n,B,t)$
in the finite bracket problem, it builds all allowed brackets directly from
the case's own coset data, looks up the supplied weights, and evaluates the
weak-duality bound using unbounded Python integers. A sorted key finds the
weights; it does not replace the calculation for the original case. An
`EMPTY` entry is accepted only when some coset really has no allowed bracket.
Acceptance requires all 127,488 cases. The checker imports neither a search
program nor a certificate generator.

`data/d7k3.cert` contains 3,984 entries: 58 `EMPTY` entries and 3,926 weight
vectors. Its header specifies weights in units of $1/15000$ of a cost unit.
Each remaining line has the form:

```text
K n m mu1 r1 ... mu7 r7 ; EMPTY
K n m mu1 r1 ... mu7 r7 ; value:weight ...
```

The seven pairs are sorted coset means and residues; coset zero is determined
by $n$ and $m$. The single entry point compares these mathematical entries
with the committed Lean definitions. This comparison ignores comments and
source formatting. It then verifies that the independent checker rejects a
deleted entry, a false `EMPTY`, halved weights, zeroed weights, a negative
weight, and a duplicated entry. The default Lean build supplies a separate
kernel proof of the finite step and its own weight and cover controls.

`attainment.py` specializes Árnadóttir and Godsil's published construction
for odd dimension to dimension seven. It checks that the connection set has
20 elements and spans the seven-dimensional vertex group. It computes
$K=\lbrace 0,7,120,127\rbrace$ from the character criterion and independently obtains the
same strongly cospectral class from the adjacency matrix using `spectral.py`.
The latter finds every eigenvalue by exact rank computations and forms the
spectral projection polynomials with integer arithmetic. The sum of the
eigenspace dimensions must equal 128. It also rejects two incorrect class
claims, one missing a vertex and one adding a vertex.

The optional transcription program regenerates the Lean certificate modules
in a new directory without performing a search or invoking a solver:

```sh
python3 checks/transcribe.py data/d7k3.cert /tmp/cubelike-transcription
```

The optional illustration is separate from the proof checks. To check its
reproduction from the same published connection set:

```sh
python3 checks/figure.py --check
```

The [presentation checking notes](presentation-notes.tex) retain the detailed
formal definitions, logical dependencies, certificate-generation description,
and reproduction commands accompanying the paper.

## Sources used during development

Árnadóttir and Godsil posed the tightness question, proved the earlier upper bound, gave the abelian character criterion, and constructed the connected examples attaining four. The small-dimensional calibration examples came from Árnadóttir and Godsil's Example 8.4 and Appendix A. Their paper records their Sage computations and credits Gordon Royle's cubelike graph lists.

Arnbjörg Soffía Árnadóttir's 2022 thesis, [State Transfer & Strong Cospectrality in Cayley Graphs](http://hdl.handle.net/10012/18494), also records the cubelike bound (Theorem 5.6.5 and Corollary 5.6.6), its tightness in dimensions three through six (Table 5.1), and the question whether it is tight in every dimension (Section 7.1).

Hermie Monterde's [related remark](https://arxiv.org/abs/2111.01265v2), in Section 3 immediately after Theorem 3.11, suggests examining whether Árnadóttir and Godsil's normal-Cayley multiplicity bound (Theorem 6.1) extends to other graph classes and, more generally, to strong cospectrality for generalized adjacency matrices of weighted graphs. That bound is $|T|\leq |V(X)|/m$ for a pairwise strongly cospectral set $T$ in a normal Cayley graph $X$, where $m$ is the largest adjacency-eigenvalue multiplicity. This extension question differs from sharpness of their dimension-dependent cubelike bound (Corollary 8.3) considered here.

Bernasconi, Godsil and Severini's [Quantum networks on cubelike graphs](https://doi.org/10.1103/PhysRevA.78.052320) and Cheung and Godsil's [Perfect state transfer in cubelike graphs](https://doi.org/10.1016/j.laa.2011.04.022) provide the cubelike perfect-state-transfer background cited in the paper. The paper also credits Godsil's [State transfer on graphs](https://doi.org/10.1016/j.disc.2011.06.032) and Godsil and Smith's [Strongly cospectral vertices](https://ajc.maths.uq.edu.au/pdf/88/ajc_v88_p001.pdf) for the state-transfer and strong-cospectrality background.

Chris Godsil's [2012 answer to When Do a Few Eigenvectors of Graph Laplacians Not Determine the Graph?](https://mathoverflow.net/a/105020) describes cubelike character eigenvectors and relates their eigenvalues to the weights of binary codewords.

The [Subiono2021/Sagemath-Cells teaching README](https://github.com/Subiono2021/Sagemath-Cells/tree/08f5ca4d0198f2d1573df722283862ec80a31f49) presents a SageMath cubelike-graph constructor and a five-dimensional example.

Gabriel Coutinho, Emanuel Juliano and Thomás Jung Spier's [The spectrum of symmetric decorated paths (arXiv:2305.09406v1)](https://arxiv.org/abs/2305.09406v1) studies eigenvalue spacing in rooted products of paths. Under its reflected characteristic-polynomial-ratio hypothesis, Corollary 15 excludes perfect state transfer between the path endpoints, except for the two- and three-vertex paths.

Qihang Wang's [Integral Cayley graphs and abelian rigidity in cores of cubelike graphs (version 2.0)](https://doi.org/10.5281/zenodo.23445385), dated October 18, 2026, studies cores of cubelike graphs. Theorem 3.4 proves that such a core is cubelike when it admits a normal Cayley representation over a finite abelian group.

The underlying normal-Cayley character criterion is due to Peter Sin and Julien Sorci in [their earlier paper](https://arxiv.org/abs/2011.07566), first posted November 15, 2020.

Peter Sin's [large-set construction](https://arxiv.org/abs/2207.05211), first posted in 2022, establishes that strongly cospectral classes are unbounded as the dimension grows; the new upper bound concerns dimension seven. The formal proof uses Lean, described by Leonardo de Moura and Sebastian Ullrich in [The Lean 4 Theorem Prover and Programming Language](https://lean-lang.org/papers/lean4.pdf), and mathlib, described by the mathlib Community in [The Lean Mathematical Library](https://arxiv.org/abs/1910.09336). Research cross-checks also used Google OR-Tools [CP-SAT Solver](https://developers.google.com/optimization/cp/cp_solver). No third-party program or figure is reproduced.

The open-problems-lab repository, published under the maxime-fleury account, describes group-invariant multicolor Ramsey searches and proof-trace checking tools, including searches beyond cyclic groups. The retained README was read on October 28, 2026 at lines 1–535 and 630–1021; lines 536–629 were not read. This is background credit for the README-described tools, not an endorsement or a claim of historical use. No code, proof trace or Lean artifact was checked. An immutable README blob coordinate and the original HTTP retrieval time remain unavailable.

### Generalized-Hamming dissertation: primary access on October 28, 2026

Elham Sharifiyazdi's *The Clique Number of Generalized Hamming Graphs* is the online Clausthal doctoral dissertation cataloged as [2007], URN urn:nbn:de:gbv:104-1087818. The DNB and GBV copies retrieved on October 28, 2026 are byte-identical. The title page and selected introductory, chapter-opening, conclusion and bibliography pages were inspected; most proofs were not read. The graph definition uses positive Hamming distances at most d, not exactly d. The nearby clique-number results support the short README credit; no claim of historical use or non-use follows. The exact posting date is not authenticated, and the separately cataloged [2008?] print edition was not read. Earlier access failures describe earlier attempts. The dissertation's Godsil–Royle bibliography entry does not identify the unnamed historical Godsil HTML notes.
