# Exact snub factors and indexed model correspondence

Outcome: **CERTIFIED for the two independent snub factors only.** This
supplies full uniformity, unit edges, complete indexed vertex sets and the
`SnubModel` exact facts for `check_u3/geom.py:177` and
`check_u3/tcert.py:233`. It addresses the snub-factor portion of referee R2
(the report's §1, with the dependency used in §3 and §5.6). It does not
close R2 for Wythoff constructions, other exceptional models, or products,
and establishes no classification, novelty or priority claim.

The authoritative input source is the three files and SHA-256 identities
in `snub_certificate.json`, from repository revision `18621310d`. Neither
checker edits them. The source identities are acceptance conditions; a
future source change requires review and a new correspondence certificate.
Only `snub_*` files are added by this unit. Case B is untouched.

## Claim

The indexed enclosures returned by `geom.snub_perm('B3')` contain the
vertices, in that order, of a convex unit-edge uniform snub cube, with
24 vertices, 60 edges, 32 equilateral triangular facets and 6 square
facets. Those returned for `H3` contain the vertices of a convex unit-edge
uniform snub dodecahedron, with 60 vertices, 150 edges, 80 equilateral
triangular facets and 12 regular pentagonal facets. “Contain” means
coordinate interval containment, or exact construction-word induction;
interval overlap is never used to assert equality.

In both cases the two generator permutations, the five exact unit-edge
seeds, and the planar rotation-orbit sets in `tcert.SnubModel` are exactly
those of this certified indexed model. They therefore supply the exact
symmetry, neighbor and affine-dimension facts used by the independent
route. The model's empty stabilizer generator list supplies the identity
subgroup, which is sufficient for the stated construction facts; no claim
that an empty list generates an arbitrary full stabilizer is required.

## Construction and proof

Write a physical vector as `T*x`, where the columns of `T` are the three
unit simple roots, in their existing Cholesky orientation. In coefficient
coordinates the Gram matrix is

```
G = [[1, -c01, 0], [-c01, 1, -c12], [0, -c12, 1]],
B3: (c01,c12)=(1/2,sqrt(2)/2),
H3: (c01,c12)=((1+sqrt(5))/4,1/2).
```

These are exactly the cosines used in `geom.roots`. In these coordinates
reflection `i` is `R_i*x=x-2*(G*x)_i*e_i`. Both checkers verify its
orthogonality or that of every generated group matrix. Set `A=R0*R1`,
`B=R1*R2`, `C=A*B=R0*R2`. All matrices are exact over `Q(sqrt(2))` or
`Q(sqrt(5))`. Exact breadth-first multiplication from the identity closes
a finite group of respectively 24 or 60 distinct matrices. This closure
does not identify points or use a separation lemma.

For any group matrix `M`, let `D_M=(I-M)^T*G*(I-M)`. The base point `x`
is the isolated root in the certificate's rational box of

```
x^T*(D_A-D_B)*x = 0,
x^T*(D_A-D_C)*x = 0,
x^T*G*x = 1.
```

Each checker evaluates a Krawczyk operator with an interval Jacobian,
checks strict inclusion in the box, and checks that the infinity-norm
bound for `I-Y*J(box)` is less than one. Brouwer applied to
`z -> z-Y*F(z)` gives a root, and the contraction bound gives uniqueness.
The same bound implies that the preconditioner is nonsingular. All
inequalities are outward-rounded intervals. The second checker uses only
integer/Fraction operations for them, rounded outward to dyadics with
512 fractional bits. It performs a second certified Krawczyk refinement;
there is no inference of exact equality from a small residual.

Set `e=sqrt(x^T*D_A*x)>0` and use the orbit of `T*x/e`. Both checkers
verify exact quadratic-form identities

```
D_M-D_A = a_M*(D_A-D_B)+b_M*(D_A-D_C)
```

for `M` equal to `A,A^-1,B,B^-1,C`. Consequently those five indexed
points have exact distance one from the base. Every other nonidentity
group element has a strictly positive interval bound for
`x^T*(D_M-D_A)*x`. Hence every other orbit distance from the base is
strictly greater than one. Transitivity gives these conclusions at every
vertex, and also proves that all 24 or 60 matrix images are distinct.
This proves separation from the equations and finite exact group,
rather than assuming uniformity to justify deduplication.

The certificate lists oriented cycles proposing every facet. For a
triangle, three exact unit edges prove equilateral regularity and
coplanarity is automatic. Every longer listed cycle is verified to be
an exact group translate of the base orbit of `A` or `B`, in generator
order or its reverse. The exact rotation orders are `(3,4)` and `(5,3)`.
The exact traces are `1+2*cos(2*pi/m)`, in particular `(1+sqrt(5))/2` for
order five; thus pentagonal cycles use the convex order, rather than a
pentagram order. A nontrivial orbit of such a rotation lies in an exact
plane perpendicular to its axis and is a convex regular polygon. The
strict-support determinant test includes a nondegenerate triple, so its
radius is nonzero. Every listed polygon edge is also checked against the
five exact unit-distance seed identities.

For each proposed facet, a cross product of its first two edges gives a
normal. All vertices outside that face have scalar products of one
strict sign with that normal, using certified interval inequalities.
On-plane equality follows from the exact triangle or rotation-orbit
construction, not from an interval containing zero. The point set is
full-dimensional because there is a nondegenerate facet with a vertex
strictly off its plane. Every orbit point is an exposed vertex: the
points are distinct and lie on a common sphere, so the tangent plane at
a point strictly separates it from all others. Thus a certified
supporting face contains exactly the listed hull vertices and is an
actual maximal hull facet, with the displayed cyclic edges.

Every undirected edge in the proposed facet boundary occurs exactly
twice. An edge of a three-dimensional convex polytope belongs to exactly
two facets. Therefore no certified facet has a dual-graph adjacency to
a missing facet. The dual graph of a convex polytope is connected, so
this nonempty closed family is the entire hull boundary. This proves
completeness, rather than just checking some known faces or comparing
hull software outputs. The Euler identity and expected face counts are
additional checked consequences.

The exact rotation group permutes the whole hull transitively. All
facets are regular, and all edges have length one; this proves recursive
uniformity. The per-vertex facet configurations are `3.3.3.3.4` and
`3.3.3.3.5`: transitivity and the certified incidence counts give four
triangles and one other polygon at every vertex. These are the snub
cube and snub dodecahedron constructions, including whichever mirror
orientation the fixed root selects. No radius-based naming inference is
used.

## Index and enclosure correspondence

The primary checker records the unmodified original `PointSet.add` return
history. It compares every insertion/lookup with exact group-matrix
breadth-first multiplication and checks every interval assignment
against the actual generator action. Thus the generator-index
correspondence follows inductively from construction words. Even if the
old point finder had returned a wrong rounded match, that history would
fail the exact group-index test.

For the root itself, the independent coefficient root enclosure maps
inside the original Cartesian root box, and the whole original
box maps inside the independent uniqueness box. The original Krawczyk
operator is recomputed and verified to be precisely the original `Kx`.
A root in the original box is contained in that operator by the
mean-value identity, so `Kx` encloses the independent exact root.
The original positive edge normalization then encloses its exact
normalized value. Interval arithmetic and the checked insertion history
complete the induction for every indexed output vertex.

The independent checker takes a separate and stronger numerical path:
it refines the exact coefficient root twice with its rational interval
kernel and verifies that the resulting coordinate intervals for **every**
indexed vertex are wholly contained in the existing `geom` output
intervals. These are set-containment predicates, not overlap predicates.
It independently reconstructs the matrix group and its words with
SymPy, then verifies the actual `SnubModel` generators, seeds and planar
sets against those indices. Both checkers pin all imported authoritative
source identities.

## Acceptance and controls

Install `snub_requirements.txt` in an environment, then run from any
working directory:

```bash
PYTHON=python3 bash checks/model_audit/snub_verify.sh
```

The three output records are primary `CERTIFIED`, rational independent
`CERTIFIED`, and nine corruptions rejected by both. `snub_acceptance.jsonl`
records the completed local run; `snub_SHA256SUMS` freezes the input,
checkers, proof and that evidence.

The nine deliberate corruptions are a source digest, deletion of a hull
facet, duplication of a facet, a wrong generator index, a wrong group
word, a wrong unit seed, a nonplanar pentagon, a collapsed triangle and a
root box missing the root. Both independent acceptance implementations
must reject every one. A failed control is not counted as a result.

`snub_build.py` is an untrusted optional proposal generator: SciPy's
floating hull proposes facets, and its result is accepted only through
the two exact/interval proofs above. It is never imported by either
checker. Regeneration additionally uses SciPy.
Acceptance downloads no inputs and performs no hull
search. This packet still needs fresh frozen-package verification before
being used as a fresh-verified classification premise; other portions of
R2 and the overall independent classification route remain separate.
