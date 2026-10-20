# Certificate and mathematical reductions

The proofs, the search code, the certificate checkers and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

Run `sh checks/check.sh` from the bundle root. It requires Python 3.10 or
later (standard library only), `cc`, a POSIX shell and `mktemp`; see
`requirements.txt`. `PYTHON` and `CC` may name alternative executables.
All builds and generated files go into a temporary directory, removed on
exit. The check needs no network access, SAT solver, repository checkout,
environment-specific path or external proof input. The mathematical
arguments are in Sections 2–5 of the paper.

`data/graph.txt` begins with `82 136`, followed by the unordered edges on
vertices 0 through 81. Comments start with `#`. `data/rotation.txt` has one
line `v: neighbours in cyclic order` per vertex. Both files define the
specific labelled witness; the paper reproduces them.

`check_planar.py` and `check_planar.c` separately check the neighbour
permutations and connectivity, trace the dart permutation
`(u,v) -> (v,next_v(u))`, and obtain 56 faces. Gluing oriented vertex discs
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

`check_col_elim.py` works directly over the three-colour domain. Each edge
starts as the six allowed unequal pairs. At an elimination step all
relations containing a vertex are conjoined and that vertex is
existentially projected out, enumerating every assignment on the remaining
scope. All other relations remain. This preserves satisfiability; an empty
relation therefore proves non-colourability. The largest remaining scope
encountered here has size three. No SAT code is imported by this path.

`col3_cnf.py` independently generates a Boolean formula with variables
`x(v,c)=3*v+c+1`, for `0 <= v < 82`, `0 <= c < 3`. It adds, for every
vertex, one at-least-one and three at-most-one clauses; for every edge it
adds three clauses forbidding equal endpoint colours. These clauses are
equivalent to proper three-colouring. The lexicographically first triangle
is `(0,1,6)`; it adds the units `1`, `5`, `21`. Any proper colouring gives
these three vertices distinct colours and a permutation of colour names
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

The entry point also checks nine negative-control outcomes, with these
actual inputs in `data/controls/`:

- `minus-edge.txt`: deletes `(0,1)`. Elimination must find it colourable;
  drat-trim must reject the original proof on its new CNF.
- `plus-c4.txt`: adds `(0,12)`, closing `0–6–60–12–0`. Both cycle
  implementations must reject it.
- `plus-c9.txt`: adds `(0,7)`, closing
  `0–1–6–60–12–62–63–13–7–0`. Both cycle implementations must reject it.
- `rotation-swapped.txt`: swaps two neighbours at vertex zero. Both
  planarity implementations must reject the resulting Euler characteristic
  zero. This rejects the supplied embedding, not the graph's planarity.
- `col3-truncated.drat`: the first 45 complete proof steps, omitting the
  empty clause and the proof's remainder. drat-trim must report
  `s NOT VERIFIED`, with its normal rejection status.

For the cycle and rotation controls the entry point requires explicit
mathematical rejection, rather than accepting crashes as negative results.
The edge-deletion control is not a claim of edge-criticality: no exhaustive
edge-deletion result is part of this bundle.

This is a computer-assisted proof. The mathematical reductions, graph
parsers, enumerators and executable checker are not formalized in a proof
assistant. The two languages for the geometric checks and the two different
non-colourability methods provide independent implementation paths, not a
claim of a formally verified compiler or checker. Integer arithmetic is
used throughout. On this graph `n=82`, maximum degree 10, cycle bound 14;
even `82*10^14 < 2^63` bounds the C enumerator's raw counts. Its fixed array
and degree limits also exceed this input. The theorem concerns this fixed
input, not arbitrary malformed files or arbitrary graph sizes.

To rebuild the paper, install a standard LaTeX distribution with `amsmath`,
`amsthm`, `geometry`, `hyperref`, `multicol`, `fancyvrb` and `lmodern`, then run from
`paper/`:

```sh
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

The PDF includes the graph and rotation via their relative paths in
`data/`. Paper rebuilding is separate from certificate checking.
