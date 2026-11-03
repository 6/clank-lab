# Checking the counterexample

Run `python3 checks/check.py` from the result directory. Linux x86-64 and
AArch64 are supported; Python 3.10 or newer and GCC are required. No Python
packages are needed. The command fetches immutable upstream dependencies
listed in `requirements.txt`, compiles them in a temporary directory and
removes generated files when it finishes. Certificate data are included;
no SAT solver is needed. The first download requires HTTPS access to GitHub.

The statement checked is that the graph obtained by subdividing every edge
of the six-clique has independent monophonic-position chromatic number at
least 8, while its complement has that number at least 15. Their sum is
therefore at least 23, greater than order plus one, 22. The paper proves
these bounds by hand and gives explicit colorings attaining 8 and 15.
The unchanged certificate checks supplement that proof.

## What is checked

In the data files, vertices 0 to 5 are the original vertices and 6 to 20
are the subdivision vertices $b_{ij}$, $i<j$, with the pairs $(i,j)$ in
lexicographic order (`B_pairs` in `data/graph.json`).

`semantics.py` reconstructs the labeled graph, the complement clique, all
775 induced-path witnesses, the two ordered catalogs, every clause and
variable map of six formulas, and satisfying control assignments. It also
enumerates the subsets to check catalog coverage, tests deletion of a
catalog member, and checks the sequential counter exhaustively on small
instances. It imports no producer or solver code.

`check.py` checks the four UNSAT certificates with drat-trim, converts them
to LRAT and checks them with cake_lpr. Each checker must reject a truncated
certificate for each formula with the expected diagnostic; a successful
process exit alone never establishes acceptance. Additional corruptions
remove a graph edge and replace an induced path by repeated vertices.

| Formula | Variables | Clauses | Meaning of UNSAT |
|---|---:|---:|---|
| `h-catalogue` | 21 | 932 | Every relaxed independent class is contained in the catalog. |
| `complement-catalogue` | 21 | 211 | Every independent complement class is contained in its catalog. |
| h7 | 1134 | 2023 | Seven catalog members cannot cover the graph. |
| complement14 | 480 | 893 | Fourteen catalog members cannot cover the complement. |

The two satisfying controls at eight and fifteen members certify covers of
the relaxed catalogs. They do not establish upper bounds for the
monophonic parameters. A permitted color class must avoid each witnessed
triple; the argument does not assume the witness list contains every bad
triple. Extending classes to catalog members gives a cover, so a cover
obstruction proves the coloring lower bound. The hand proof in the paper establishes catalog completeness and the
cover obstruction directly; the encodings below cross-check that reduction. The complement also has an elementary 15-clique proof.

The trust assumptions are the mathematical interpretation and reduction,
the Python interpreter and semantic checker, the compiler and hardware,
and the standard checkers. CakeML supplies a verified certificate-checking
algorithm, not a formalization of the graph-theoretic reduction. This is
not a whole-theorem Lean proof.

## Further credits

Ullas Chandran S. V., Gabriele Di Stefano, S. Haritha, Elias John Thomas and
James Tuite, [*Colouring a graph with position sets*](https://arxiv.org/abs/2408.13494v2),
Definition 2.3 and Conjecture 9.3, supply the parameter and question.
The [published article](https://doi.org/10.26493/1855-3974.3454.a3c) appeared
online on August 28, 2026. In arXiv version 2 and the published version,
Lemma 4.1 and the remark before Conjecture 9.3 give the non-independent
sum bound, and the paragraph after the conjecture reports a computer
search by Grahame Erskine (private communication, 2021) confirming the
conjecture for all graphs with up to ten vertices.

Chandran, Klavžar, Neethu and Tuite's
[graph-products paper](https://doi.org/10.1007/s40314-026-03901-3), online
September 11, 2026, treats maximum monophonic sets: Lemma 3.4 and
Theorems 3.16, 3.18 and 4.4 of [arXiv version 3](https://arxiv.org/abs/2412.09837v3).
It does not address the independent-partition complement sum.

Thomas, Chandran, Tuite and Di Stefano's
[*On monophonic position sets in graphs*](https://arxiv.org/abs/2012.10330)
defines the maximum independent monophonic-set parameter in Section 5;
it is distinct from the minimum number of classes here. The
[2021 independent-position paper](https://doi.org/10.22199/issn.0717-6279-2021-02-0023)
uses shortest paths. Sadiquali and Sudhahar's
[2019 independent-monophonic paper](https://doi.org/10.12723/mjs.50.3)
concerns sets whose monophonic intervals cover the graph.

Yan's [circulant manuscript](https://doi.org/10.5281/zenodo.21995203),
August 18, 2026, answers Conjecture 4.5 of *On some extremal position
problems*, a different maximum-set question. Pedro M. M. de Castro's
[*Edge multiset dimension of subdivided complete graphs*](https://doi.org/10.5281/zenodo.22928011),
September 23, 2026, studies a different invariant of the same graph family.
The Omega Institute's
[vertex-position-ratio project](https://github.com/the-omega-institute/vertex-position-ratio/tree/e746d8ec8ed649e61d54e2c378abcc710ef51aa4)
studies observer-local maxima, not these color partitions. No argument from
these three sources is used. The notes on [prior work and unread sources](#prior-work-and-unread-sources) give the limits
of the prior-work search.

The certificates were produced with CaDiCaL, described in [*CaDiCaL 2.0*](https://cca.informatik.uni-freiburg.de/papers/BiereFallerFazekasFleuryFroleyksPollitt-CAV24.pdf), by Armin Biere, Tobias Faller, Katalin Fazekas, Mathias Fleury, Nils Froleyks and Florian Pollitt (CAV 2024, LNCS 14681, 133–152). DRAT checking and LRAT conversion use [drat-trim](https://www.cs.cmu.edu/~mheule/publications/drat-trim.pdf), by Nathan Wetzler, Marijn J. H. Heule and Warren A. Hunt, Jr. (SAT 2014, LNCS 8561, 422–429). Independent LRAT checking uses [cake_lpr](https://doi.org/10.1007/978-3-030-72013-1_12), by Yong Kiam Tan, Marijn J. H. Heule and Magnus O. Myreen. The sequential counter follows Carsten Sinz, [*Towards an Optimal CNF Encoding of Boolean Cardinality Constraints*](https://doi.org/10.1007/11564751_73) (CP 2005, LNCS 3709, 827–831).

## Certificate encodings

For catalog completeness, use one variable $x_v$ for each vertex, and let
$T$ be the set of witnessed triples and $\mathcal C$ the catalog. The
formula asserts independence, avoidance of every witnessed triple,
failure of containment in each catalog member, and nonemptiness:

```math
\begin{aligned}
&\neg x_u\vee\neg x_v &&(uv\in E(H)),\\
&\neg x_u\vee\neg x_v\vee\neg x_w &&(\{u,v,w\}\in T),\\
&\bigvee_{v\notin C}x_v &&(C\in\mathcal C),\\
&\bigvee_{v\in V(H)}x_v.&&
\end{aligned}
```

A nonempty permitted class outside the catalog would satisfy this formula.
Its UNSAT certificate therefore proves completeness; the empty set is
contained in every member. The complement formula is constructed in the
same way with its own edges, catalog and witnessed triples.

Order a catalog of size $N$ as $C_1',\ldots,C_N'$. A cover formula uses
$y_i$ to select member $i$ and a clause $\bigvee_{i:v\in C_i'}y_i$
for every vertex $v$. For a bound $k$, the sequential counter introduces
$s_{i,j}$ for $1\leq i\leq N$ and $1\leq j\leq k+1$, with clauses

```math
\begin{aligned}
&\neg y_i\vee s_{i,1} &&(1\leq i\leq N),\\
&\neg s_{i-1,j}\vee s_{i,j} &&(2\leq i\leq N,\ 1\leq j\leq k+1),\\
&\neg y_i\vee\neg s_{i-1,j-1}\vee s_{i,j}
  &&(2\leq i\leq N,\ 2\leq j\leq k+1),\\
&\neg s_{N,k+1}.&&
\end{aligned}
```

Any cover using at most $k$ members satisfies this formula: set $s_{i,j}$
true exactly when at least $j$ of the first $i$ members are selected.
Values with $j>i$ are false; every implication and the last clause hold.
This direction suffices for UNSAT to exclude a cover. DIMACS labels are
$i$ for $y_i$ and $N+(i-1)(k+1)+j$ for $s_{i,j}$.

## Prior work and unread sources

These notes record the October 31, 2026 assessment and its November 1, 2026
refresh. They expand the paper's related-work appendix; they are a bounded search
record, not a mathematical premise. The search found no earlier occurrence
of the result in the material read. It is not a complete literature census,
and not every version of every source was read. Each source below gives the
version read, the versions not read, and why the source is excluded.

| Source | Read | Not read | Why excluded |
|---|---|---|---|
| Tuite, Thomas and Chandran, [*On some extremal position problems for graphs*](https://doi.org/10.26493/1855-3974.3094.bc6), Ars Math. Contemp. 25 (2025) | Published version's introduction and extremal statements; [arXiv:2106.06827](https://arxiv.org/abs/2106.06827) | [Open Research Online (ORO) 92086, file 7](https://oro.open.ac.uk/92086/7/92086.pdf) | "We investigate some extremal problems for these parameters": maximum general-position and monophonic-position set sizes, and the order, size and diameter realizing them. No partition into independent sets. |
| Di Stefano, Klavžar, Krishnakumar, Tuite and Yero, [*Lower general position sets in graphs*](https://doi.org/10.7151/dmgt.2542), Discuss. Math. Graph Theory 45 (2025) | [Published version](https://dirros.openscience.si/Dokument.php?id=31644&lang=slv), including the monophonic discussion in Section 6; [ORO 96123, file 21](https://oro.open.ac.uk/96123/21/96123final.pdf) | [ORO 96123, file 7](https://oro.open.ac.uk/96123/7/96123.pdf) | The "smallest maximal general position set": one inclusion-maximal set, not a partition. |
| Klavžar, Tian and Tuite, *Builder-Blocker general position games*, [arXiv:2310.19949v2](https://arxiv.org/abs/2310.19949v2) | Version 2 statements; introduction, game definitions and outline of the final [ORO 99072, file 38](https://oro.open.ac.uk/99072/38/99072final.pdf) | The rest of file 38; the early-access [ORO 99072, file 20](https://oro.open.ac.uk/99072/20/99072_EA.pdf) | "A general position set is built through adversarial play": a game on one shortest-path position set. |
| Thomas, Chandran, Tuite and Di Stefano, [*On the general position number of Mycielskian graphs*](https://doi.org/10.1016/j.dam.2024.03.015), Discrete Appl. Math. 353 (2024) | Introduction, definitions and theorem statements of [arXiv:2203.08170v2](https://arxiv.org/abs/2203.08170v2); abstract of the final [ORO 96766, file 7](https://oro.open.ac.uk/96766/7/96766VoR.pdf) | The body of the final version | "We investigate the general position numbers of the Mycielskian of graphs": maximum shortest-path position sets. |
| Iršič, Klavžar, Rus and Tuite, [*General position polynomials*](https://doi.org/10.1007/s00025-024-02133-3), Results Math. 79 (2024) | Published version's definition, introduction, outline and conclusion | The rest of the published version; [ORO 95325, file 7](https://oro.open.ac.uk/95325/7/95325_VoR.pdf) | Coefficients give "the number of distinct general position sets of G with cardinality" i: counts of single sets. |
| Kruft Welton, Khudairi and Tuite, *Lower general position in Cartesian products*, [arXiv:2404.19451v1](https://arxiv.org/abs/2404.19451v1) | Version 1 introduction, outline and theorem statements; abstract of the final [ORO 98050, file 9](https://oro.open.ac.uk/98050/9/98050final.pdf) | The body of the final version | "The lower general position problem asks for a smallest maximal general position set", here in Cartesian products. |
| Thomas, Chandran, Tuite and Di Stefano, [*On monophonic position sets in graphs*](https://doi.org/10.1016/j.dam.2023.02.021), Discrete Appl. Math. 354 (2024) | [arXiv:2012.10330v4](https://arxiv.org/abs/2012.10330v4), Sections 1–6; abstract of the final [ORO 88147, file 9](https://oro.open.ac.uk/88147/9/88147final.pdf) | [ORO 88147, file 1](https://oro.open.ac.uk/88147/1/88147.pdf); the body of the final version | Section 5's "independent monophonic position" number is the largest size of one such set, not a minimum partition. Neither the subdivided 6-clique nor the sum appears in the version read. |
| Araujo, Dourado, Protti and Sampaio, [*The iteration time and the general position number in graph convexities*](https://doi.org/10.1016/j.amc.2024.129084), Appl. Math. Comput. 487 (2025) | [arXiv:2305.00467v5](https://arxiv.org/abs/2305.00467v5) in full | The published version: publisher access failed, and its updated references show it is not byte-identical to the preprint | Iteration time, and the complexity of maximum general-position sets in three convexities, the monophonic one in Section 5. |
| Hamed-Labbafian, Henning and Tavakoli, [*Edge general position in graphs: Graph products, integer linear programming and some applications*](https://doi.org/10.1016/j.dam.2026.01.008), Discrete Appl. Math. 386 (2026) | The publisher's abstract and introduction | The full text: publisher HTTP 403, no open copy found | A maximum set of edges with no three on a common shortest path; not vertex partitions under induced paths. |
| Zeyu Yan, [*Monophonic Position in Circulant Graphs: A Counterexample, an Induced-Path Criterion, and an Infinite Family*](https://doi.org/10.5281/zenodo.21995203), August 18, 2026 | Manuscript and supplement in full | The linked [implementation repository](https://github.com/zeliang314/monophonic-position-circulants): not found | "No circulant graph of order 15 has both diameter 2 and monophonic position number 2": a different conjecture. The supplement describes the code as a circulant census and certificate generator. |
| [MathDB 366898](https://mathdb.com/p/366898) and [MathDB 366901](https://mathdb.com/p/366901) | Both problem records, November 1, 2026: zero posted solutions | Nothing outstanding | 366898 asks the circulant question above; 366901 records the sum conjecture this result disproves, with no solution posted. |
| [Levain Arena](https://levainarena.org) reports, one per participating AI model (eight) | Public topic summaries | All eight reports: not publicly released | The summaries place them in union-closed families and an Erdős–Selfridge problem, Faulhaber and Bernoulli identities and Grundy domination, and counting polynomials of independent and dominating sets. None concerns monophonic-position colorings. |

Fifteen Semantic Scholar records carry only the title "Open Research
Online". Each record's open-access field links an ORO deposit, which
identifies the work. This identifies the work, not that different files of
one deposit are identical.

| Semantic Scholar record | ORO deposit and file | Work |
|---|---|---|
| [939b00f](https://www.semanticscholar.org/paper/939b00fe3c143d274fce3c09da0c13c4ffdf9ef9) | 92086 | *On some extremal position problems for graphs* |
| [10b34c4](https://www.semanticscholar.org/paper/10b34c4a5f40552adc5efb04e1c0472c9bb7a674) | 92086, file 7 | *On some extremal position problems for graphs* |
| [18eb0f8](https://www.semanticscholar.org/paper/18eb0f88196d82f4c51a0f438a5bc51e44f28d70) | 96123 | *Lower general position sets in graphs* |
| [4b66347](https://www.semanticscholar.org/paper/4b663474ffa19870c18d233d67d41558269802c0) | 96123, file 21 | *Lower general position sets in graphs* |
| [7fc7012](https://www.semanticscholar.org/paper/7fc7012bcdd221d6d45be7ea5a2c52242fdb9da0) | 96123, file 7 | *Lower general position sets in graphs* |
| [3ca55e9](https://www.semanticscholar.org/paper/3ca55e929379a91bdde8e08551488a0462808724) | 96123, file 7 | *Lower general position sets in graphs* |
| [3c0d343](https://www.semanticscholar.org/paper/3c0d3433ed49e1954e376882e76a2fb792c8a860) | 99072, file 20 | *Builder-Blocker general position games* |
| [be2d878](https://www.semanticscholar.org/paper/be2d878f5c61bc14a5eb20d6975560a7f1b6422a) | 96766, file 7 | *On the general position number of Mycielskian graphs* |
| [16fe5c7](https://www.semanticscholar.org/paper/16fe5c7850eee4661593c296abe3808a08a0561a) | 96766, file 7 | *On the general position number of Mycielskian graphs* |
| [4155b7a](https://www.semanticscholar.org/paper/4155b7a592ebb1a0e1d10a40abfea0805cf66ad1) | 95325, file 7 | *General position polynomials* |
| [48b2b77](https://www.semanticscholar.org/paper/48b2b779a219c73612e29dcb75526c3c11904f6a) | 98050, file 9 | *Lower general position in Cartesian products* |
| [fed834b](https://www.semanticscholar.org/paper/fed834bc671339352e8b3c30032e3fff1d026df7) | 88147, file 1 | *On monophonic position sets in graphs* |
| [c4f92f3](https://www.semanticscholar.org/paper/c4f92f3c987b3ff11e44632b33a663f976f35935) | 88147, file 1 | *On monophonic position sets in graphs* |
| [db843bb](https://www.semanticscholar.org/paper/db843bb2e17ef50ec08005643aae06812085aa86) | 88147, file 1 | *On monophonic position sets in graphs* |
| [9786c90](https://www.semanticscholar.org/paper/9786c9081f28cd68b3504a5a5e769d477fb0364a) | 88147, file 9 | *On monophonic position sets in graphs* |

Search coverage was further limited by CORE and Semantic Scholar rate
limits, capped broad searches, incomplete GitHub indexing and unexamined
binary PDFs in repository searches. These limits do not affect the proof or
the certificates, but they prevent an unqualified priority claim.
