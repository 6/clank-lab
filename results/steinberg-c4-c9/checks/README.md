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
checks a crossing-free rational straight-line drawing, non-three-colorability
and exclusion of four- and nine-cycles for the parsed graph, together with
the retained spherical rotation certificate. The geometric segments range
over all real affine parameters, including both endpoints. The formal
axioms are exactly `propext`, `Classical.choice` and `Quot.sound`; no
compiled or native proof evaluation is used.
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

## Formal statement

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

Non-colorability uses a proved coloring-to-CNF reduction and a
kernel-checked equality between the reduced formula, without symmetry
units, and the input of a verified reverse-unit-propagation checker that
uses LRAT-style hints. Deleted clauses stay available to that checker, and
each one is proved entailed by the input. The embedding of the rotation in
the sphere, four-criticality, the Ore decomposition, the edge minimum and
the exclusion of $C_{10}$ lie outside the Lean statement; they rest on the
written arguments in the paper and the executable checks above.

## Build and implementation details

Both embedding implementations count 56 orbits of the face permutation.
A source build of the Lean proof, using cached dependencies, took about
4.5 minutes on a 12-CPU allocation, with about 17 GiB peak memory for the
complete build. The build record identifies the allocation, not the
processor model. The standard Lake commands are in the accompanying Lean
README. Separate timings for the remaining finite checks were not
recorded.

The graph was found by classifying small planar pieces by the possible
three-color patterns at their contact vertices and composing these finite
relations until the relation was empty. This search took about 12
CPU-minutes for the initial census and 8 CPU-minutes for composing the
patterns, on two CPUs; the processor model was not recorded.

The implementations also reject the specified alterations of the graph,
rotation and proof certificates, listed above. The programs and their
compilers are ordinary executable implementations rather than formally
verified programs.

The vertex labels printed in the paper's figure are transcribed from the
SVG's vertex titles and six-decimal coordinates and overlaid on the vector
PDF. The figure illustrates the graph and is not part of the proof.

The graph, certificates and programs are archived with version 5 at
<https://doi.org/10.5281/zenodo.23572996>.

The graph and its preexisting finite certificates are unchanged from the
[archived version 6](https://doi.org/10.5281/zenodo.23631783).

## Sources used during development

The earlier credit note retained these source qualifications: Lu and coauthors are credited for the question through Kang, Jin and Wang’s Problem 1.2; arXiv:2001.00166v1 has Jin first. Liu, Loeb, Rolek, Yin and Yu’s Theorem 1.3 proves DP-3-colorability without cycles of lengths 4, a, b, 9 for distinct a, b in {6, 7, 8}. It extends the 3-choosability results of Wang, Lu and Chen; Shen and Wang; and Wang, Wu and Shen (Theorem 1.2 abbreviates the last credit as Wang and Shen). These results impose two additional cycle exclusions. [Context and reading limits](context.md) records incomplete source coverage.

This DOI archives version 7; the linked corrected edition is version 8. The mathematical data and checks are unchanged.

## Further credits

- A. Kostochka and M. Yancey, [A Brooks-type result for sparse critical graphs](https://arxiv.org/abs/1408.0846v3) — supplies the Ore composition used in the construction.
- H. Lu, Y. Wang, W. Wang, Y. Bu, M. Montassier and A. Raspaud, [On the 3-colorability of planar graphs without 4-, 7- and 9-cycles](https://doi.org/10.1016/j.disc.2009.02.030) — poses the question attributed through Kang, Jin and Wang.
- Y. Kang, L. Jin and Y. Wang, [The 3-colorability of planar graphs without cycles of length 4, 6 and 9](https://arxiv.org/abs/1506.04629v1) — records the question as Problem 1.2.
- L. Jin, Y. Kang, P. Liu and Y. Wang, [(1,0,0)-colorability of planar graphs without cycles of length 4 or 6](https://arxiv.org/abs/2001.00166v1) — also records the question as Problem 1.2.
- V. Cohen-Addad, M. Hebdige, D. Král’, Z. Li and E. Salgado, [Steinberg’s conjecture is false](https://arxiv.org/abs/1604.05108v2) — supplies the contrasting cycle-pair result in Theorem 3.
- Y. Kang, L. Jin and X. Zhu, [Planar graphs having no cycle of length 4, 7, or 9 are DP-3-colorable](https://doi.org/10.1002/jgt.23123) — provides related coloring context.
- L. Dai, Y. Wang and J. Xu, [Every planar graph without cycles of length 4 or 9 is (1,1,0)-colorable](https://doi.org/10.1016/j.disc.2017.04.006) — provides related defective-coloring context.
- M. Chen, L. Dai, J. Nie, Y. Wang and W. Yu, [Planar graphs without cycles of length 4 or 9 are (2,0,0)-colorable](https://doi.org/10.1360/N012018-00129) — provides related defective-coloring context.
- Y. Xiao and M. Huang, [A weak DP-coloring of planar graphs without 4- and 9-cycles](https://doi.org/10.1016/j.dam.2023.10.004) — provides related weak-coloring context.
- R. Liu, S. Loeb, M. Rolek, Y. Yin and G. Yu, [DP-3-coloring of planar graphs without 4,9-cycles and two cycles from {5,6,7,8}](https://arxiv.org/abs/1809.07445v1) — supplies Theorem 1.3 with two additional cycle exclusions.
- Y. Wang, H. Lu and M. Chen, [A note on 3-choosability of planar graphs](https://doi.org/10.1016/j.ipl.2007.08.027) — is an earlier 3-choosability result extended by Liu and coauthors.
- L. Shen and Y. Wang, [A sufficient condition for a planar graph to be 3-choosable](https://doi.org/10.1016/j.ipl.2007.06.005) — is an earlier 3-choosability result extended by Liu and coauthors.
- Y. Wang, Q. Wu and L. Shen, [Planar graphs without cycles of length 4, 7, 8, or 9 are 3-choosable](https://doi.org/10.1016/j.dam.2010.11.002) — is an earlier 3-choosability result extended by Liu and coauthors.
- Marijn Heule and Nathan Wetzler, [drat-trim](https://github.com/marijnheule/drat-trim) — checks the SAT certificate.
- Armin Biere and collaborators, [CaDiCaL](https://github.com/arminbiere/cadical) — generates the SAT certificate.
- L. Cruz-Filipe, M. Heule, W. Hunt, M. Kaufmann and P. Schneider-Kamp, [Efficient Certified RAT Verification](https://doi.org/10.1007/978-3-319-63046-5_14) — supplies the LRAT verification methodology.
- Lean contributors, [Lean 4](https://github.com/leanprover/lean4) — supplies the proof assistant.
- Mathlib contributors, [Mathlib](https://github.com/leanprover-community/mathlib4) — supplies the formal-proof libraries.
