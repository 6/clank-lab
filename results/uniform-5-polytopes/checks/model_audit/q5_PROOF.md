# Exceptional models: full uniformity and exact indexed coordinates

Outcome: **CERTIFIED for the independent snub 24-cell and grand antiprism
models**, conditional only on the stated arithmetic implementations and
ordinary convex-polytope facts, with the known 3D classification used to
attach conventional cell names. This is not an unconditional Case A
classification. The separate snub-factor packet proves the algebraic
polyhedral factors; `wythoff_proof.md` proves the general constructions.
The execution contract for the general Wythoff indices must additionally
be checked in every dependent fresh adapter run.

The authoritative exact point sets are `tcert.sadi_exact()` and
`tcert.gap_exact()`, constructed in Q(sqrt 5) from explicit signed,
even-permuted coordinates. The first removes the coordinate 24-cell from
the 120-coordinate list; the second removes the decagon in an exactly
unit-edge plane and the decagon in its orthogonal plane, by exact rank
and dot products. No approximate zero or rounded point key defines these
sets. The input source identities are frozen in `SOURCE_SHA256SUMS`.

The finite claims are:

| Model | Vertices | Edges | Polygon ridges | Full cells |
| --- | ---: | ---: | ---: | --- |
| sadi | 96 | 432 | 480 | 120 tetrahedra, 24 icosahedra |
| gap | 100 | 500 | 720 | 300 tetrahedra, 20 pentagonal antiprisms |

The full `q5_certificate.json` is about 411 KB. It supplies exact rational
coefficient supporting functionals, affine frames, every cell and every
oriented polygon face of each cell, and exact metric permutations
witnessing vertex transitivity of the whole model and of each cell.
`q5_build.py` proposes these objects; neither checker imports it. The
builder's numerical hulls do not certify incidence, flatness or equality.

## Exact checker A and independent checker B

Checker A uses rational coefficient pairs for Q(sqrt 5). Its order test
uses rational signs and comparison of a² with 5b²; no floating-point sign
is used. Checker B independently constructs SymPy's number field
QQ(sqrt(5)), uses its algebraic arithmetic, verifies affine independence
by positive Gram determinants, and tests polygon convexity with intrinsic
Gram coordinates. Checker A instead performs exact Gaussian ranks and
uses injective coordinate projections for polygon orientation. They
share the authoritative exact-coordinate definitions, but no generator,
geometry-validation implementation or quadratic arithmetic.

Both check every distance-preserving permutation exactly and verify that
the generated action is transitive. They check full-dimensional affine
frames, common positive squared radius, distinct points and all pairwise
distances at least one. Full affine rank plus preservation of every
pairwise distance extends a permutation uniquely to an affine isometry.
For the full cospherical model this isometry fixes the unique
circumcentre. Hence the supplied permutations prove actual vertex
transitivity, not approximate matrix orthogonality.

Every proposed cell has a rank-three affine frame and an exact nonzero
supporting functional. Its listed points are exactly on the hyperplane,
and every other point of the full model is strictly on its inner side.
This establishes the complete vertex set of an actual hull facet. All
points are exposed hull vertices because they are distinct on a common
sphere. A tangent functional at a sphere point uniquely maximizes there.

For each polygon of a cell, both checkers similarly verify an exact
supporting functional relative to that cell, a rank-two affine frame and
a strict off-plane sign at every other cell vertex. In B the polygon
functional cannot be constant on the cell, since some cell vertex has a
strict sign; its intersection with the cell's rank-three hyperplane is
therefore a two-plane. Both checkers verify the cyclic order by strict
signs along every side, and every side has squared length exactly one.

A planar slice of the one common model sphere is a circle. Therefore
these convex equilateral cyclic polygons are regular: if their common
chord subtends the smaller angle theta, each consecutive arc is theta or
2*pi-theta; one larger arc and at least two other arcs would already
exceed 2*pi, so every arc is theta=2*pi/p. Triangles are included.

Every edge of each cell occurs in exactly two certified polygon faces.
The dual graph of a convex three-polytope is connected, so this nonempty
closed set is its entire polygon boundary. Every model polygon ridge
then occurs in exactly two certified model cells. By the same connected
dual-graph argument in dimension four the cell list is the entire hull
boundary, not just a selection of supporting faces.

Each cell is itself vertex-transitive by its exact metric permutations,
with regular unit-edge polygon faces; consequently each cell is uniform.
Its constant vertex configuration is checked to be 3.3.3, 3.3.3.3.3 or
3.3.3.5. The known uniform-polyhedron classification assigns respectively
the labels tet, ico and A5. The whole four-dimensional hull is therefore
uniform with unit edges, proving the actual construction properties
needed by R2. No Cauchy rigidity theorem or inferred model name from
radius/count overlap is needed for uniformity.

## The independent geometry's index correspondence

For each exact model point the certificate records its index in the
canonical exact 120-point list. Both checkers reconstruct that projection
exactly. They then check that `geom.polytope4(name)` returns precisely
those entries, in that order, of its original `geom.cell600()` list.
The latter coordinate formulas have the same signed/permutation order as
`tcert.cell600_exact()`, with the identity phi²=phi+1 accounting for the
reciprocal coordinate formula.

Additionally, both checkers evaluate every exact quadratic coordinate as
a rigorous 320-bit enclosure and require that enclosure to be
**contained** in the actual existing 160-bit geometry coordinate ball.
An enclosure of an exact coordinate contained in another ball proves
that coordinate belongs to that ball. A small distance or overlap between
two enclosures would not prove this assertion. Exact index projection and
coordinate containment remove the earlier arbitrary-close-point premise.
Thus subsequent interval calculations on these existing indexed geometry
balls really enclose the authoritative exact model.

The exact Q5 model's symmetry, seed and rank facts are properties of this
same indexed coordinate set. Its search implementation is only a source
of proposed global permutations here; the two checkers replay every
permutation as a full exact distance matrix identity.

## Controls, pricing, and limits

Both checkers reject eight corruptions: a wrong 600-cell index projection,
a nonmetric/nonbijective global permutation, missing transitivity,
a nonsupporting cell functional, a wrong polygon vertex, a wrong cell
label, a missing cell polygon and a missing whole hull boundary. A trial
control that reversed a triangle was correctly accepted: reversal is a
valid cyclic orientation, so the corruption was replaced with a genuinely
wrong vertex. This failed corruption attempt did not change a claim.

These are finite certificate replays, not searches over Case A signatures.

These certificates establish construction properties and index identities
for these two factors. They do not certify stage-2 completeness, every
known-polytope identification, the angle primitive, ROOT, local uniqueness
for all classes, or the 628-count claim. Source changes, including a
legitimate change to the pinned `ivla.py`, require a fresh identity
freeze and replay; do not merely reinterpret an old acceptance record.
