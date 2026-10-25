# Certificate and mathematical reductions

The proofs, the search code, the certificate checkers and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

Run `sh checks/check.sh` from the bundle root. It requires Python 3.10 or
later (standard library only), `cc`, a POSIX shell and `mktemp`; see
`requirements.txt`. `PYTHON` and `CC` may name alternative executables.
All builds and generated files go into a temporary directory, removed on
exit. The check needs no network access, SAT solver, repository checkout,
environment-specific path or external proof input. The mathematical arguments are in the paper.

`data/graph.txt` begins with `82 136`, followed by the unordered edges on
vertices 0 through 81. Comments start with `#`. `data/rotation.txt` has one
line `v: neighbors in cyclic order` per vertex. Both files define the
specific labeled witness; the paper reproduces them.

`check_planar.py` and `check_planar.c` separately check the neighbor
permutations and connectivity, trace the dart permutation
`(u,v) -> (v,next_v(u))`, and obtain 56 faces. Gluing oriented vertex disks
and untwisted edge bands, then capping the boundary walks, gives a connected
closed orientable surface with Euler characteristic 82−136+56=2. It is the
sphere, so this is a planar embedding. This is a rotation-system check,
not a test of a drawing's coordinates.

`check_cycles.py` starts each simple path at its smallest vertex and counts
its closure only when its second vertex is smaller than its last.
`check_cycles.c` instead anchors a closing edge at the smallest vertex,
counts paths avoiding that edge, and divides by two for the two incident
edges of each cycle. These enumerate all simple cycles, including those
with chords, through length 14. Both give:

| Length | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| Count | 27 | 0 | 22 | 55 | 44 | 11 | 0 | 0 | 64 | 320 | 832 | 1824 |

`check_ore.py` is a single independent Python script, requiring only the
standard library. It checks the full structural theorem and the criticality
certificates without calling any other bundled program:

```sh
python3 checks/check_ore.py data/graph.txt data/ore-tree.json data/rotation.txt data/deletion-colorings.json
```

It traces the supplied rotation and enumerates all simple cycles through
length ten. It replays `ore-tree.json` from its 27 complete four-vertex
leaves and 26 Ore joins, checks that every child is used exactly once, and
compares the root with the input graph through the explicit bijection in
`isomorphism` (here the identity). The node array is in postorder. A `K4`
node lists its vertices. An `ore` node names its earlier `left` and `right`
children, the left edge `edge=[x,y]`, right vertex `split=z`, and the two
nonempty disjoint sets `x_neighbors` and `y_neighbors` partitioning the
entire neighborhood of z. The operands must be disjoint. Replay removes
xy and z, then joins the two specified sets to x and y. The same complete
tree is displayed in the paper; its table is generated from this JSON.

Non-three-colorability follows by induction: if an Ore composite were
three-colored, unequal colors at x,y would color the restored left graph;
equal colors would color the right graph after identifying x,y. Both
contradict the children's non-three-colorability, starting from K4. This
checks a finite construction, with no coloring search. The independently
retained DRAT and elimination paths provide additional checks.

`deletion-colorings.json` has one row for each edge, naming that edge and
all 82 colors, ordered by the vertex label. The checker verifies colors in
{0,1,2} on every retained edge and exact coverage of all 136 deletions. It
also derives and checks a four-coloring by giving one deleted-edge endpoint
a fourth color. No isolated vertex exists, so every proper subgraph omits
an edge and inherits a three-coloring. The graph is therefore four-critical.
The script checks `3*136=5*82-2`; the lower-bound theorem of Kostochka and
Yancey is a cited mathematical premise, rather than something the script
proves. The consequence is minimum size among 82-vertex four-critical
graphs, with no minimum-order assertion.

`check_col_elim.py` works directly over the three-color domain. Each edge
starts as the six allowed unequal pairs. At an elimination step all
relations containing a vertex are conjoined and that vertex is
existentially projected out, enumerating every assignment on the remaining
scope. All other relations remain. This preserves satisfiability; an empty
relation therefore proves non-colorability. The largest remaining scope
encountered here has size three. No SAT code is imported by this path.

`col3_cnf.py` independently generates a Boolean formula with variables
`x(v,c)=3*v+c+1`, for `0 <= v < 82`, `0 <= c < 3`. It adds, for every
vertex, one at-least-one and three at-most-one clauses; for every edge it
adds three clauses forbidding equal endpoint colors. These clauses are
equivalent to proper three-coloring. The lexicographically first triangle
is `(0,1,6)`; it adds the units `1`, `5`, `21`. Any proper coloring gives
these three vertices distinct colors and a permutation of color names
satisfies all three units. Thus satisfiability is unchanged. The formula
has 246 variables and 739 clauses, including the three symmetry units.
`data/col3.cnf` is the actual formula. `check_dimacs.py` compares its parsed
header and ordered clauses with the freshly generated formula, ignoring
comments; the two different input path comments are immaterial.

`data/col3.drat` is the unsatisfiability certificate, checked by the
unmodified vendored `drat-trim.c`. It is standard text DRAT; its additions,
deletions, literal order and final empty clause are a lossless transcription
of the binary certificate. See [THIRD_PARTY.md](../THIRD_PARTY.md) for credit
and the MIT notices. No solver is needed for replay. The entry point
requires both successful termination and the exact `s VERIFIED` status;
resource errors or a vanished process do not prove unsatisfiability.

The entry point also checks ten negative-control outcomes, with these
actual inputs in `data/controls/`:

- `minus-edge.txt`: deletes `(0,1)`. Elimination must find it colorable;
  drat-trim must reject the original proof on its new CNF.
- `plus-c4.txt`: adds `(0,12)`, closing `0–6–60–12–0`. Both cycle
  implementations must reject it.
- `plus-c9.txt`: adds `(0,7)`, closing
  `0–1–6–60–12–62–63–13–7–0`. Both cycle implementations must reject it.
- `rotation-swapped.txt`: swaps two neighbors at vertex zero. Both
  planarity implementations must reject the resulting Euler characteristic
  zero. This rejects the supplied embedding, not the graph's planarity.
- `col3-truncated.drat`: the first 45 complete proof steps, omitting the
  empty clause and the proof's remainder. drat-trim must report
  `s NOT VERIFIED`, with its normal rejection status.

- `ore-tree-invalid.json`: repeats a vertex in the first K4 leaf. The
  standalone checker must reject this invalid construction.

For the cycle, tree and rotation controls the entry point requires explicit
mathematical rejection, rather than accepting crashes as negative results.
The complete deletion-coloring file, rather than the single edge-deletion
control, certifies criticality.

The Lean proof is checked separately with `lake exe cache get` followed by
`lake build` from `lean/`; see [its documentation](../lean/README.md). It
checks non-three-colorability and exclusion of four- and nine-cycles for
the parsed graph, together with the explicit spherical rotation certificate.
The criticality, Ore reconstruction, ten-cycle exclusion and edge-bound
consequence retain the executable checks and written arguments described
above. The C and Python programs are independent implementation paths;
their compilers and checkers are not formally verified. Integer arithmetic
is used throughout. On this graph `n=82`, maximum degree 10, cycle bound 14;
even `82*10^14 < 2^63` bounds the C enumerator's raw counts. Its fixed array
and degree limits also exceed this input. The theorem concerns this fixed
input, not arbitrary malformed files or arbitrary graph sizes.

To rebuild the paper, install a standard LaTeX distribution with `amsmath`,
`amsthm`, `geometry`, `hyperref`, `multicol`, `fancyvrb`, `lmodern`,
`graphicx`, `appendix`, `tikz` (PGF) and `float`, then run from
`paper/`:

```sh
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

The PDF includes the graph and rotation via their relative paths in
`data/`. Paper rebuilding is separate from certificate checking.

## Reproduction and verification tests

The standalone executable check is `sh checks/check.sh`, run from the
bundle root. It needs Python 3.10 or later, a C compiler and a POSIX
shell; there are no third-party Python packages or network downloads.
It compiles the supplied C sources in a temporary directory, runs both
embedding checks, both cycle enumerators, the Ore replay and all deletion
colorings, elimination, CNF comparison and DRAT verification. The single
standard-library script `checks/check_ore.py`, given the graph, tree,
rotation and deletion-coloring files, also checks planarity, all simple
cycles through length ten, the Ore induction and four-criticality on its
own. It imports no other bundled code. The DRAT route requires successful termination and
the exact success status, not just an absent error message.

The same command exercises deliberate corruptions. Deleting edge $(0,1)$
must make the elimination result colorable and invalidate the original
DRAT proof on the modified formula. Adding $(0,12)$ creates the cycle
$0,6,60,12,0$; adding $(0,7)$ creates
$0,1,6,60,12,62,63,13,7,0$. Both cycle implementations must reject each
modified graph. Swapping two neighbors in the rotation at zero changes
the Euler characteristic to zero and must be rejected by both embedding
checks. This is rejection of a rotation, not a non-planarity claim for
the underlying graph. Finally a proper prefix containing only the first
45 complete proof steps must fail DRAT verification. A tenth control repeats a vertex in the first $K_4$ leaf of the tree;
the standalone checker must reject it. These are ten control outcomes. The certificate checks and the reductions in
the preceding sections establish Theorem 1.

The full statement of Theorem 1 remains computer-assisted.
For the executable routes in the paper, the rotation-system argument, enumeration
completeness, Ore induction, criticality argument, CNF reduction, color
symmetry and constraint-elimination argument are mathematical arguments
written in the paper. The Python and C implementations and DRAT-trim run as
ordinary programs and are not themselves formally verified. The
different implementations and non-colorability methods reduce shared
implementation risk.

## License

This work, including the
paper, is under Apache-2.0 (the repository's root LICENSE); the
unmodified DRAT-trim source retains MIT. The full applicable notices and
third-party provenance appear in THIRD_PARTY.md.

## Construction and formal statement

The following mathematical formulations are retained with the same hypotheses
and conventions; the paper gives the main proof and the detailed appendices.

The hard construction step is gluing small planar pieces along designated
contact vertices so that their allowed contact-color patterns become
incompatible, while avoiding new four- or nine-cycles. Tabulating the
patterns guides those identifications; the fixed graph, rotation and Ore
tree then permit the direct checks described in this guide.

The edge list defines the graph $G$ on $0,\ldots,81$.
A tree of complete four-vertex graphs, joined by Ore compositions,
reconstructs exactly this labeled graph. If a composite had a proper
three-coloring, the two identified vertices would have either different
colors, coloring the restored first operand, or equal colors, coloring
the unsplit second operand. Both contradict the non-three-colorability
of that operand. Induction from $K_4$ proves non-three-colorability.
Section 2 gives the operation and lemma; Appendix C describes the tree
reconstruction and induction, and Appendix G prints the full tree.

The supplied cyclic neighbor orders trace faces of a connected orientable
surface. Their Euler characteristic is two; the surface is a sphere,
giving a planar embedding. Two independent enumerators count all simple
cycles through length fourteen and find none of lengths four or nine.
Explicit proper three-colorings of every single-edge deletion, together
with non-three-colorability and absence of isolated vertices, prove
four-criticality. Finally the edge count attains Kostochka and Yancey's
bound (Kostochka–Yancey, arXiv:1209.1050v1, Theorem 3), also stated
in (Kostochka–Yancey, arXiv:1408.0846v3, Theorem 4). The paper gives the complete main proof; remaining verification details
follow in its appendices.

The pinned Lean and Mathlib project proves `Steinberg.counterexample`
in `lean/Check.lean`. For the parsed `SimpleGraph (Fin 82)`,
it states that `HasSphericalRotation graph rotation` holds,
every closed walk `p` from any vertex to itself satisfying
`p.IsCycle` has length different from four and nine, and
`graph.Coloring (Fin 3)` is empty. The constants parse
`data/graph.txt` and `data/rotation.txt`; there are no external
hypotheses. The first conjunct certifies exact cyclic neighbor orders,
connectedness and face orbits partitioning all darts, with Euler
characteristic two. The second uses Mathlib's simple-cycle convention,
including cycles with chords; the third excludes proper three-colorings.
Kernel reduction checks the certificate constants;
the guarded axiom list permits only `propext`,
`Classical.choice` and `Quot.sound`. No native/compiler proof
evaluation is used. The precise Lean scope is given in
Appendix E and `lean/README.md`.

## Illustration and attribution source excerpts

These retained source excerpts identify the unchanged drawing method and
credits; the paper integrates their explanation with the construction and
acknowledgments. Citation keys refer to the paper bibliography.

```tex
\paragraph{Drawing.} Figure~\ref{fig:graph} illustrates the embedding. The 82-vertex counterexample with its 136 edges. A Tutte
(barycentric) drawing is obtained by triangulating the bounded faces of
the published rotation system with temporary centers, then omitting the
added vertices and edges. The figure illustrates the graph and is not
part of the proof.

Drawing reference: W. T. Tutte, ``How to Draw a Graph''
(1963)~\cite{tutte}.

\section*{Acknowledgments}
The Ore-composition method and the sharp edge bound are credited to
the work discussed by Kostochka and Yancey~\cite[Section 1 and Theorem 4]{ky}.
Credit for posing and developing the forbidden-cycle questions belongs
to the researchers cited above, and for the earlier Steinberg disproof
to Cohen-Addad and coauthors. The formalization uses
\href{https://github.com/leanprover/lean4}{Lean 4 and its standard library}
and \href{https://github.com/leanprover-community/mathlib4}{Mathlib};
credit is due to their contributors. The hint-based certificate methodology
is credited to Cruz-Filipe, Heule, Hunt, Kaufmann and
Schneider-Kamp~\cite[abstract]{lrat}.
That abstract describes the format as extending DRAT ``with hints that
facilitate a simple and fast validation algorithm.''
The SAT certificate uses CaDiCaL and is
checked with Heule and Wetzler's DRAT-trim (deletion resolution asymmetric tautology).
```

## Historical build and implementation details

A source build of the Lean proof, using cached dependencies, took about
4.5 minutes on a 12-CPU allocation, with about 17 GiB peak memory
for the complete build. The retained build record identifies the allocation,
not the processor model; no new benchmark was run for this edition.
The standard Lake commands are in the accompanying Lean README.

The implementations also reject the specified alterations of the graph,
rotation and proof certificates, listed above. The programs and their compilers
are ordinary executable implementations rather than formally verified programs.

The paper retains the formal theorem identifier once to identify its
mathematical statement. Axiom names, evaluation details and commands are
documented here and in the formal-verification appendix.

## Retained related-work wording

The paper now quotes the checked title phrases for the following related
work. The prior formulation is retained here with the same citation keys:

```tex
Related work includes Kang, Jin, Liu and Wang on $(1,0,0)$-colorability~\cite{jklw},
Kang, Jin and Zhu on DP-3-colorability~\cite{kjz},
Dai, Wang and Xu on $(1,1,0)$-colorability~\cite{dai}, and
Chen, Dai, Nie, Wang and Yu on $(2,0,0)$-colorability~\cite{nie}.
```

## Retained formal and implementation disclosure

The following exact prior formal-development paragraph preserves all
mathematical wording and operational disclosures. The paper keeps its
mathematical explanation; build guards and axiom inventories are here.

```tex
The Lean theorem \file{Steinberg.counterexample} conjoins only three
properties of one \file{SimpleGraph (Fin 82)}: a spherical rotation
certificate, no simple $C_4$ or $C_9$, and non-three-colorability.
Lean parses the unchanged \file{data/graph.txt} and \file{data/rotation.txt}
to define this graph and rotation.
The planarity certificate is a fully checked connected genus-zero rotation,
including exact neighbor incidence, cyclic vertex orders, exhaustive face
orbits covering all darts, and $82-136+56=2$.
The correspondence with a topological embedding uses the surface argument
above and is not formalized in Lean.
Cycle exclusion covers all Mathlib \file{IsCycle} closed walks, including
cycles with chords. Non-colorability uses a proved coloring-to-CNF reduction
and kernel-proved equality with the symmetry-free input of a verified RUP
checker using LRAT-style hints. Deletion-erased RUP retains deleted clauses;
every retained clause is proved entailed by the input.
The Lean certificate constants are checked by kernel reduction; no SAT solver
is trusted. The standard Lake build guards the top statement's exact type and
\texttt{\#print axioms} using \texttt{\#guard\_msgs}, permitting only
\file{propext}, \file{Classical.choice} and \file{Quot.sound}.
No native/compiler proof evaluation or additional axioms are used.
Here RUP means reverse unit propagation; its hints specify which previously
justified clauses to use. LRAT is the hinted clausal-proof format cited below.
Retaining deleted clauses does not affect their entailment from the input.
Four-criticality, the Ore decomposition, the edge minimum, $C_{10}$
exclusion, and the full statement of Theorem~\ref{thm:main} lie outside
this Lean scope.
```

## Further passages relocated from the paper

These exact source passages retain the mathematical assertions and
implementation disclosures under the same conventions. The main paper gives
the proof and mathematical formal-statement bridge; implementation details
are here. Citation keys refer to the unchanged entries in the paper.

```tex
The Lean theorem \texttt{Steinberg.counterexample} concerns the same
parsed finite simple graph $G$ on $\{0,\ldots,81\}$. It proves the
conjunction of a spherical rotation certificate, the assertion that every
closed walk that is a simple cycle has length different from four and nine,
and the nonexistence
of a proper coloring by three colors. There are no external hypotheses.
The rotation condition means exact cyclic neighbor orders, connectedness
and face orbits partitioning all darts, with Euler characteristic two.
```

```tex
The Lean theorem \file{Steinberg.counterexample} conjoins only three
properties of one \file{SimpleGraph (Fin 82)}: a spherical rotation
certificate, no simple $C_4$ or $C_9$, and non-three-colorability.
Lean parses the unchanged \file{data/graph.txt} and \file{data/rotation.txt}
to define this graph and rotation.
The planarity certificate is a fully checked connected genus-zero rotation,
including exact neighbor incidence, cyclic vertex orders, exhaustive face
orbits covering all darts, and $82-136+56=2$.
The correspondence with a topological embedding uses the surface argument
above and is not formalized in Lean.
```

```tex
Cycle exclusion covers all Mathlib \file{IsCycle} closed walks, including
cycles with chords.
```

```tex
Four-criticality, the Ore decomposition, the edge minimum, $C_{10}$
exclusion, and the full statement of Theorem~\ref{thm:main} lie outside
this Lean scope.
```

```tex
The input \file{data/graph.txt}, reproduced in Appendix~\ref{app:graph},
defines $G$ on vertices $0,\ldots,81$ by 136 unordered edges. The
accompanying \file{data/rotation.txt} gives a cyclic order of the neighbors
at each vertex. The two planarity implementations separately validate
the edge count, simplicity, neighbor lists and connectivity.
```

```tex
In particular there is no $C_4$, $C_9$ or $C_{10}$. Since the maximum
degree of this input is 10, even the coarse bound $82\cdot10^{14}<2^{63}$
on raw enumeration counts is below the signed 64-bit limit used in C.
All Python counts use arbitrary precision integers.
```


The complete original enumeration paragraph, including its output table and
integer-width justification, is retained here as one source unit:

```tex
The C implementation instead chooses an edge $(s,t)$ with $s<t$, and
enumerates simple $s$--$t$ paths avoiding that edge, with all other vertices
greater than $s$. Closing by $ts$ gives a simple cycle. A cycle whose
smallest vertex is $s$ is found twice, once for each of its two edges at
$s$; division by two gives the count. The implementation checks that
each raw count is even. Both implementations run through length 14 and
return the same table:
\begin{center}\small
\begin{tabular}{c|rrrrrrrrrrrr}
length&3&4&5&6&7&8&9&10&11&12&13&14\\\hline
count&27&0&22&55&44&11&0&0&64&320&832&1824
\end{tabular}
\end{center}
In particular there is no $C_4$, $C_9$ or $C_{10}$. Since the maximum
degree of this input is 10, even the coarse bound $82\cdot10^{14}<2^{63}$
on raw enumeration counts is below the signed 64-bit limit used in C.
All Python counts use arbitrary precision integers.
```

## Archive and reproduction information

```tex
The unchanged graph, certificates and programs are archived with version 5
at \url{https://doi.org/10.5281/zenodo.23572996};
the accompanying README links the reproduction commands, bibliographic
context and reading limits.
```

## Retained neighboring-coloring formulations

```tex
Defective colorings are a different
notion: a $(d_1,d_2,d_3)$-coloring permits each color class to induce
maximum degree at most $d_j$.
The notation uses classes $\mathcal F_d$ of forests of maximum degree at most
$d$. Xiao and Huang's publisher abstract~\cite{xiao} states that
``planar graphs without 4- and 9-cycles are weakly
DP-$(\mathcal F_2,\mathcal F_2,\mathcal F_0)$-colorable.''
It likewise does not assert proper three-colorability.
DP-3-colorability implies
three-choosability, which implies ordinary proper three-colorability.
Consequently, failure of a list or DP coloring property alone would not
supply the obstruction required here.
Related work includes Kang, Jin, Liu and Wang on $(1,0,0)$-colorability~\cite[Theorem 1.4]{jklw}
and Kang, Jin and Zhu on DP-3-colorability~\cite[Theorem 1.1]{kjz}.
For the four-and-nine pair, Dai, Wang and Xu's title is
``Every planar graph without cycles of length 4 or 9 is $(1,1,0)$-colorable''~\cite{dai},
while Chen, Dai, Nie, Wang and Yu study $(2,0,0)$-colorability~\cite[Theorem 1.4]{nie}.
Jin, Kang, Liu and Wang described the cases $i\in\{6,7,8,9\}$ as
``still unsettled''~\cite[paragraph following Problem 1.2]{jklw}.
For further context see Ang and Leo~\cite{ang}, the survey of Bu, Wang
and Wang~\cite{survey}, and Li, Niu and Tian's work on the strong Bordeaux
conjecture~\cite{bordeaux}.
```

## Retained original credit wording

```tex
The Ore-composition method and the sharp edge bound are credited to
the work discussed by Kostochka and Yancey~\cite[Section 1 and Theorem 4, arXiv:1408.0846v3]{ky}.
Credit for posing and developing the forbidden-cycle questions belongs
to the researchers cited above, and for the earlier Steinberg disproof
to Cohen-Addad and coauthors. The formalization uses
\href{https://github.com/leanprover/lean4}{Lean 4 and its standard library}
and \href{https://github.com/leanprover-community/mathlib4}{Mathlib};
credit is due to their contributors. The hint-based certificate methodology
is credited to Cruz-Filipe, Heule, Hunt, Kaufmann and
Schneider-Kamp~\cite[author-hosted CADE 2017 version, abstract]{lrat}.
That abstract describes the format as extending DRAT ``with hints that
facilitate a simple and fast validation algorithm.''
The SAT certificate uses CaDiCaL and is
checked with Heule and Wetzler's DRAT-trim (deletion resolution asymmetric tautology).
```

## Retained original computational-dependence disclosure

```tex
The full theorem remains computer-assisted: the passage from the rotation
certificate to a topological embedding, Ore induction, criticality and
edge-minimum deduction are written arguments. The last uses the cited
Kostochka--Yancey theorem. The Python and C programs, their compilers and
DRAT-trim are ordinary trusted executable implementations; they are not
formally verified. Lean does not assert four-criticality, the Ore
decomposition, the edge minimum or the additional ten-cycle exclusion.
The independent implementations and non-colorability routes reduce shared
implementation risk. Search is unnecessary for reproduction.
```

## Retained general coloring implication and citation wording

```tex
DP-3-colorability of that class~\cite[Theorem 1.1]{kjz}. DP-3-colorability implies
three-choosability, which implies ordinary proper three-colorability~\cite[Definition 2.1 and Corollary 1.2]{kjz}.
Consequently, failure of a list or DP coloring property alone would not
supply the obstruction required here.
```

## Retained discovery-method wording

```tex
A search over small planar pieces tabulated their
color patterns on the vertices where the pieces were to be joined, and chose identifications
that made these patterns incompatible.
```

## Retained contextual-citation wording

```tex
For further context see Ang and Leo~\cite{ang}, the survey of Bu, Wang
and Wang~\cite{survey}, and Li, Niu and Tian's work on the strong Bordeaux
conjecture~\cite{bordeaux}.
```

## Retained earlier construction overview

```tex
The hardest step was combining the coloring obstruction with the
restrictions on cycles. The construction combines small planar pieces by the vertex identifications
specified below.
```

## Retained drawing-method attribution

```tex
\paragraph{Drawing.} The figure uses the barycentric method of Tutte's
``How to Draw a Graph''~\cite{tutte}. It is obtained by triangulating
the bounded faces of the published rotation system with temporary centers,
then omitting the added vertices and edges. The figure illustrates
the graph and is not part of the proof.
```

## Retained earlier composition acknowledgment

```tex
The composition is due to Dirac, Haj\'os, Gallai and Ore, as described by
Kostochka and Yancey~\cite[Section 1]{ky}.
```

## Retained formal-verification formulation

```tex
The formal coloring certificate is related to the reductions in
Appendix~\ref{app:additional} as follows.
The formal coloring formula has no color-fixing unit clauses; the
standalone formula in Appendix~\ref{app:additional} uses the color-permutation
argument given there. In the formal certificate check, deletion instructions
leave clauses available for subsequent steps.
Non-colorability uses a proved coloring-to-CNF reduction
and kernel-proved equality with the symmetry-free input of a verified RUP
checker using LRAT-style hints. Deletion-erased RUP retains deleted clauses;
every retained clause is proved entailed by the input.
Here RUP means reverse unit propagation; its hints specify which previously
justified clauses to use. LRAT is the hinted clausal-proof format cited below.
Retaining deleted clauses does not affect their entailment from the input.
Thus ``symmetry-free'' here means that no color-fixing unit clauses are
imposed, and ``deletion-erased'' means that deletion instructions are ignored.

```

## Retained earlier question-attribution wording

```tex
Immediately before Problem 1.2~\cite{kjw}, Kang, Jin and Wang attribute this more
general question to Lu, Wang, Wang, Bu, Montassier and Raspaud~\cite{lu}.
```

## Retained earlier full-graph figure pointer

```tex
The full graph is shown in Figure~\ref{fig:graph}.
```

## Retained earlier planarity closing sentence

```tex
embedding. This proves planarity; no geometric drawing or numerical
coordinate tolerance is involved.
```

## Retained full earlier surface-test formulation

```tex
To justify this test,
place an oriented disk at every vertex, attach an untwisted band for
each edge according to the cyclic orders, and cap each boundary walk
with a disk. The result is a connected closed orientable surface with
a cellular embedding of $G$. The boundary walks are precisely the
orbits of $\phi$, so its Euler characteristic is
\[
   |V|-|E|+|F|=82-136+56=2.
\]
By the classification of closed orientable surfaces this surface is the
sphere. Deleting a point outside the embedded graph gives a plane
embedding. This proves planarity; no geometric drawing or numerical
coordinate tolerance is involved.
```

## Retained earlier verification exposition

```tex
The finite checks and the formal statement establish the computational
properties used in the proof.
Independent implementations verify the rotation, cycle counts, Ore
construction and proper colorings of each $G-e$. Two further proofs of
non-three-colorability use exact constraint elimination and a
clausal-proof certificate checked by DRAT-trim (Appendix~\ref{app:additional}).
The rotation condition means exact cyclic neighbor orders, connectedness
and face orbits partitioning all darts, with Euler characteristic two.
The formal graph has vertex set $\{0,\ldots,81\}$ and adjacency given
by exactly the 136 unordered edges in Appendix~\ref{app:graph}; its rotation
is the cyclic neighbor list printed there. For this fixed graph $G$,
the theorem \texttt{Steinberg.counterexample} in Lean asserts:
\begin{enumerate}
\item $G$ has a spherical rotation certificate;
\item every closed walk in $G$ that is a simple cycle has length different
from four and nine;
\item $G$ has no proper coloring by three colors.
\end{enumerate}
There are no external hypotheses. The formal proof uses only Lean's standard
axioms and kernel checking; the exact axiom inventory and the pinned Lean
and Mathlib versions are given in the checking notes accompanying the paper.
The formal cycle and coloring definitions agree with the conventions in
the introduction, including cycles with chords. Appendix~\ref{sec:replay} describes the formal non-colorability certificate.
The first conjunct is a combinatorial rotation certificate. The
orientable-surface argument in Section~\ref{app:embedding} realizes it as a
plane embedding. Ore induction, criticality and edge-minimum
deduction remain written arguments; the last uses Kostochka and Yancey's
theorem. The graph and its certificates are in the
\href{https://doi.org/10.5281/zenodo.23572996}{version 5 archive}.
```

## Retained earlier embedding-appendix formulation

```tex
\section{The embedding certificate}\label{app:rotation}
Appendix~\ref{app:graph} gives the edge list and cyclic neighbor orders.
The planarity checks validate the counts, simplicity, neighbor lists and
connectivity before tracing the face permutation of Section~\ref{app:embedding}.

Both implementations count 56 orbits of $\phi$.

\paragraph{Drawing.} The figure is a Tutte (barycentric) drawing. For background see Tutte's
``How to Draw a Graph''~\cite{tutte}. It is obtained by triangulating
the bounded faces of the published rotation system with temporary centers,
then omitting the added vertices and edges. The figure illustrates
the graph and is not part of the proof.
```

## Retained earlier cycle-enumeration formulation

```tex
We count undirected simple cycles without multiplicity.
The Python enumerator grows every simple path from its smallest vertex
$s$, using only other vertices greater than $s$. It records a closure
to $s$ when the path has at least three vertices and its second vertex
is smaller than its last. Every undirected simple cycle has a unique
smallest vertex and exactly two orientations, exactly one of which meets
this last test. Thus each cycle is counted once.

The C implementation instead chooses an edge $(s,t)$ with $s<t$, and
enumerates simple $s$--$t$ paths avoiding that edge, with all other vertices
greater than $s$. Closing by $ts$ gives a simple cycle. A cycle whose
smallest vertex is $s$ is found twice, once for each of its two edges at
$s$; division by two gives the count. The implementation checks that
each raw count is even. Both implementations run through length 14 and
return the same table:
\begin{center}\small
\begin{tabular}{c|rrrrrrrrrrrr}
length&3&4&5&6&7&8&9&10&11&12&13&14\\\hline
count&27&0&22&55&44&11&0&0&64&320&832&1824
\end{tabular}
\end{center}
In particular there is no $C_4$, $C_9$ or $C_{10}$.
```

## Retained earlier decomposition-checking formulation

```tex
\section{The Ore decomposition and criticality}\label{app:decomposition}
The explicit tree in \file{data/ore-tree.json}, also printed in
Appendix~\ref{app:ore}, has 27 leaves and 26 internal nodes. Each leaf
is a $K_4$; each internal node specifies both operands, the deleted edge,
the split vertex and its neighborhood partition. Nodes are numbered in
postorder, so their operands have smaller numbers. Replay uses the
vertex labels stated in the tree. Its root has vertex set
$\{0,\ldots,81\}$ and exactly the edge set in \file{data/graph.txt};
the stated isomorphism is the identity $v\mapsto v$ for every vertex.
The standalone checker verifies four distinct labels and all six edges
at each leaf. At each join it checks that both operand indices are
smaller than the current index, the operand vertex sets are disjoint,
$xy$ is an edge of the first operand, $z$ is a vertex of the second, and
$N_x,N_y$ are nonempty and form an exact partition of $N_B(z)$. It then
performs precisely the deletion, split and identifications just defined.
Finally it checks root equality under the stated bijection and that every
non-root node is used exactly once, so every node contributes to the
induction.





This proof
requires no search for colorings and no unsatisfiability certificate.
The finite structural replay checks that the displayed construction
produces the particular published graph.
For each of the 136 edges
$e$, \file{data/deletion-colorings.json} supplies an explicit vector
$(c_0,\ldots,c_{81})\in\{0,1,2\}^{82}$ properly coloring $G-e$.
The checker verifies every edge other than $e$, and exact coverage of
all edges, without solving any coloring problem.
```

## Retained earlier edge-bound and scope discussion

```tex
\subsection{Four-criticality and the edge bound}
We specialize the cited bound to four-critical graphs and round up,
since edge counts are integers.

The tree proves that $G$ is a four-Ore graph.
Kostochka and Yancey's bound~\cite[Theorem 3]{kybound}, reproduced as Theorem 4
of the cited arXiv version of~\cite{ky}, states
that every four-critical graph $H$ satisfies
\[
 |E(H)|\geq\left\lceil\frac{5|V(H)|-2}{3}\right\rceil.
\]
For this graph,
\[
 136=\frac{5\cdot82-2}{3}.
\]
Thus, as an immediate consequence of the construction and the bound,
136 is the minimum possible number of edges of any 82-vertex
four-critical graph, including graphs without a planarity or
forbidden-cycle restriction. This is an edge minimum at fixed order.
Every four-Ore graph of this order shares this edge count; no uniqueness
is asserted. It does not assert that 82 is the minimum order of a planar
four-chromatic graph without four- or nine-cycles. The checker verifies
the equality arithmetic; the general lower bound is the cited theorem. The general four-Ore construction and its edge count are also discussed
in Kostochka and Yancey's Section 1~\cite{ky}.

This is a negative answer to the explicitly posed $i=9$ case. The
particular graph also excludes $C_{10}$, an additional checked property
recorded in the cycle table in Appendix~\ref{app:cycles}. It contains $C_5$, $C_6$, $C_7$ and
$C_8$, so it gives no information on $\{C_4,C_5,C_9\}$- or
$\{C_4,C_8,C_9\}$-free planar graphs, nor on the cases $i\in\{6,7,8\}$.
No assertion about minimum order is made. The non-colorability argument
above is elementary; planarity is certified by a rotation system and
cycle exclusion by finite enumeration.
```

## Retained earlier elimination implementation description

```tex
The implementation enumerates all $3^{|S|}$ assignments and all three
values of $c$. It chooses a vertex of minimum degree in the current
interaction graph, breaking ties by vertex label. This choice affects
cost, not correctness. On the specified graph it reaches an empty
relation; the largest remaining scope $S$ encountered has size three.
This route imports no SAT solver, CNF generator or DRAT checker.
```

## Retained earlier symmetry closing sentence

```tex
Adding these units thus preserves satisfiability. No graph automorphism
or unproved assertion about the search is used.
```

## Retained full earlier symmetry argument

```tex
The lexicographically first triangle is $(0,1,6)$. The generator also
adds $x_{0,0}$, $x_{1,1}$ and $x_{6,2}$, that is, unit clauses $1$, $5$
and $21$. Every proper coloring gives distinct colors to this triangle.
There is a permutation of the three color names taking them, in this
order, to $0,1,2$; the other clauses are invariant under this permutation.
Adding these units thus preserves satisfiability. No graph automorphism
or unproved assertion about the search is used.
```

## Retained earlier clausal-certificate operational description

```tex
The resulting formula has $3\cdot82=246$ variables and
$4\cdot82+3\cdot136+3=739$ clauses. The supplied
\file{data/col3.cnf} is compared with the generated formula by parsed
header and ordered clauses, ignoring comments. The certificate
\file{data/col3.drat}, generated with CaDiCaL~\cite{cadical}, is checked
by DRAT-trim~\cite{drat}. It contains 97 addition/deletion steps in
standard text DRAT, ending with the empty clause. Its ordered steps are
a lossless transcription of the binary proof. DRAT's checked redundancy
conditions preserve satisfiability under additions; deletions only
weaken the formula. Derivation of the empty clause therefore proves
unsatisfiability of the input. This permits replay without trusting a
solver's bare unsatisfiability answer or depending on a solver version. Together with the symmetry argument and
the exact reduction above, this separately proves that $G$ has no proper
three-coloring.
```

## Retained earlier formal-certificate description

```tex
\section{Formal verification}\label{sec:replay}
The formal coloring certificate is related to the reductions in
Appendix~\ref{app:additional} as follows.
The formal coloring formula has no color-fixing unit clauses; the
standalone formula in Appendix~\ref{app:additional} uses the color-permutation
argument given there. In the formal certificate check, deletion instructions
leave clauses available for subsequent steps.

Here RUP means reverse unit propagation; its hints specify which previously
justified clauses to use. LRAT is the hinted clausal-proof format cited below.

Non-colorability uses a proved coloring-to-CNF reduction
and kernel-proved equality with the symmetry-free input of a verified RUP
checker using LRAT-style hints.

Deletion-erased RUP retains deleted clauses;
every retained clause is proved entailed by the input.
Retaining deleted clauses does not affect their entailment from the input.
Thus ``symmetry-free'' here means that no color-fixing unit clauses are
imposed, and ``deletion-erased'' means that deletion instructions are ignored.


Hint-based certificate verification
follows Cruz-Filipe, Heule, Hunt, Kaufmann and Schneider-Kamp~\cite[abstract]{lrat},
whose format extends DRAT ``with hints that facilitate a simple and fast
validation algorithm.''
```

## Retained earlier graph-and-rotation table introduction

```tex
The graph list starts with the order and size, followed by every
edge. The rotation gives every neighbor in cyclic order. These are the
same input files used by the standalone check; no reconstruction from a
drawing is necessary.
```

## Retained earlier construction-table introduction

```tex
Each leaf row specifies the four vertices of a complete graph. Each join
row specifies $A,B,xy,z,N_x,N_y$ in the notation of
Section~\ref{sec:ore}. Operands are disjoint at every join.
The root-to-published isomorphism is the identity on $0,\ldots,81$.
```

## Retained earlier source-definition locator

```tex
the definition of Ore composition
```

## Retained original table specification

```tex
\clearpage
\section{Explicit graph and rotation}\label{app:graph}
The graph list starts with the order and size, followed by every
edge. The rotation gives every neighbor in cyclic order. These are the
same input files used by the standalone check; no reconstruction from a
drawing is necessary.
\subsection*{Graph}
\begin{multicols}{3}\footnotesize
\VerbatimInput[firstline=2]{../data/graph.txt}
\end{multicols}
\clearpage
\subsection*{Rotation}
\begin{multicols}{2}\footnotesize
\VerbatimInput[firstline=2]{../data/rotation.txt}
\end{multicols}
\clearpage
\section{The explicit Ore tree}\label{app:ore}
Each leaf row specifies the four vertices of a complete graph. Each join
row specifies $A,B,xy,z,N_x,N_y$ in the notation of
Section~\ref{sec:ore}. Labels at least 82 are temporary split vertices;
none survives at the root, node 52. Operands are disjoint at every join.
The root-to-published isomorphism is the identity on $0,\ldots,81$.
\input{../data/ore-tree-table.tex}
\end{appendices}
\clearpage
```

## Retained earlier color-pattern method wording

```tex
without creating the forbidden cycles. The choice was guided by tabulating
the restrictions of each piece's three-colorings to the vertices to be
identified, and composing these finite lists of color patterns.
```

## Retained earlier nine-cycle observation wording

```tex
The earlier construction does not itself give this exclusion: its $G_1$
component in Figure 1~\cite{steinberg} contains the nine-cycle
```

## Retained earlier formal coloring-formula wording

```tex
The formal coloring formula has the edge and vertex clauses of
Appendix~\ref{app:additional}, with no color-fixing unit clauses. The formal
```

## Retained earlier LRAT format wording

```tex
Schneider-Kamp~\cite[abstract]{lrat}, whose format extends clausal proofs
```

## Retained earlier archive and written-deduction wording

```tex
arguments; the last uses Kostochka and Yancey's theorem. The graph and the
finite certificates accompany the paper in the
\href{https://doi.org/10.5281/zenodo.23572996}{version 5 archive}.
```

## Retained earlier full-graph caption wording

```tex
The drawing illustrates the fixed edge list; the rotation system proves
planarity. }
```

## Retained original nine-cycle observation

```tex
The earlier construction does not itself give this exclusion: its $G_1$
component in Figure 1~\cite{steinberg} contains the nine-cycle
$a,f,k,n,m,j,i,h,g,a$ in the paper's own labels. This component is retained
in the published construction~\cite[proof of Theorem 3, arXiv:1604.05108v2]{steinberg}.
```

## Retained earlier construction-credit sentence

```tex
Kostochka and Yancey credit Dirac, Gallai and Haj\'os and say that Ore
``used it for a composition of complete graphs''~\cite[Section 1]{ky}.
```

## Retained earlier graph caption with SVG tooltip pointer

```tex
\caption{The counterexample. Dots mark vertices, including where edges meet.
The drawing was generated from, and checked against, the edge and rotation
data in Appendix~\ref{app:graph}; the rotation system proves planarity.
Vertex numbers appear as tooltips in the accompanying
\href{https://raw.githubusercontent.com/6/clank-lab/main/results/steinberg-c4-c9/data/graph.svg}{SVG drawing}.}
```

## Historical construction search and measurements

The graph was found by classifying small planar pieces by the possible
three-color patterns at their contact vertices and composing these finite
relations until the relation was empty. The retained discovery record reports
about 12 CPU-minutes for the initial census and 8 CPU-minutes for composing
the patterns, on two CPUs. The processor model was not retained. These are
historical discovery measurements, not computations performed for this edition.
The source-only cached Lean build took about 4.5 minutes on a 12-CPU allocation.
Separate timings for each remaining finite check were not retained; no new
benchmark is claimed.

Printed vertex labels in the journal-style paper are a static transcription
of the unchanged SVG's vertex titles and six-decimal coordinates, overlaid
on the unchanged vector PDF. The graph, coordinates, drawing assets and
accepted illustration checker remain unchanged. No drawing computation or
mathematical checker was replayed for the overlay.
