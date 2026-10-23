# Exact certificate checks

The checks require Python 3, Node.js, and GAP with its standard library and
SmallGrp identification package. GAP's conjugacy-class algorithms use
SmallGrp internally even though the checker calls core GAP functions.
On Debian or Ubuntu, install the native dependencies with:

```sh
sudo apt-get update
sudo apt-get install -y gap-core gap-libs gap-smallgrp nodejs
```

There are no third-party Python packages. From the result's top-level folder:

```sh
python3 checks/verify.py
```

The entry point regenerates all six exceptional intervals and runs all
semantic, chain, and corruption checks. It uses two concurrent group checks
by default; `--workers N` selects between one and six. `--work NEW_DIRECTORY`
retains the generated inputs, logs, and parsed report in a new directory.
Without that option, temporary output is removed. The Lean development is
checked separately with `lake build` in `lean/`.

## Data and independent checks

The six `data/*.chains.json.gz` files give explicit chains. Every vertex is
an exact element label: the images of an ordered spanning basis in the
sorted exact root list. A basis-image list determines a unique matrix.
`models.g` specifies the root order and basis. The representation of $G_{33}$
retains its fixed coordinate, so its matrices have size six and essential
rank five.

The six `data/*.interval.json.gz` files record exact labels, ranks, and all
cover edges. Every check regenerates them from scratch and compares parsed
mathematical payloads, then audits the regenerated intervals semantically.
Agreement with the supplied payload is an additional reproducibility check;
the independent semantic audit establishes completeness.

`models.g` constructs real Coxeter groups from their Gram matrices, and
$G_{33}$ and $G_{34}$ from Oura and Sekiguchi's roots and generating
reflections ([their paper](https://arxiv.org/abs/2302.09695), Sections 2 and
6.1). These are new constructions from the mathematical data, not copies
of their programs. The chain partitions were found separately; the search
program and its traversal and cover tables are not loaded by any checker.

`generate.g` starts from the explicit Coxeter element and tests every right
reflection multiplication, retaining exact rank descents. It uses GAP's
exact `RankMat` and constructs the whole graph without reading the supplied
intervals or chains.

`check_semantic.g` imports no generator. It reconstructs each vertex as an
exact matrix and permutation and uses its own row elimination for rank.
It verifies the faithful root action, essential rank, group membership,
distinctness, and exact ranks. It computes all conjugacy classes and checks
that every member of every rank-one class belongs to the reflection set.
It also checks a reflection word of the required length for the Coxeter
element, its order, and a primitive regular eigenvector outside every
reflection hyperplane. Every vertex/reflection pair is checked for exact
equality of the entire cover set, and decreasing paths from the top and
to the identity certify interval membership.

For $H_4$, two actual edited interval inputs are passed through the whole
semantic checker: one removes an interior vertex and renumbers its incident
edges; the other removes a genuine edge. Both must be rejected with the
expected closure or complete-cover failure.

`check_chains.py` and `check_chains.js` independently check partition,
saturation, and symmetric endpoint ranks, with different graph indexing.
For every group, both reject four actual corruptions: an omitted chain,
a repeated chain, noncover order, and an asymmetric endpoint.

## Scope and trusted components

There are no unresolved search outcomes in these certificates. Rank sizes
and Catalan cardinalities are outputs, not acceptance premises. The complete
reflection census uses GAP's exact permutation-group conjugacy algorithms
and class sizes; it does not infer completeness from a lookup table or a
single root orbit. The exhaustiveness of GAP's `ConjugacyClasses` is part
of the trusted computational base. The checker additionally verifies the
total class size and every rank-one class.

The group/type identifications and largest invariant degrees use the
mathematical references in the paper. Exact arithmetic, GAP group algorithms,
and the small executable checkers remain trusted computational components.
The matrix-rank inequality and the connection between reflection walks and
absolute order are written arguments in the paper; the associated abstract
closure theorem is checked in Lean. The finite computations are not imported
into Lean.

A complete report contains all six group records, both chain-check results,
all corruption outcomes, and the semantic counts. Exceptions, partial runs,
missing outputs, and unsuccessful checks cannot produce an accepted report.
GAP runs with `-T`; explicit checker rejections exit with status one.
