# Checking the 4-flatness counterexample

Run `sh checks/check.sh` from the result folder after installing
`checks/requirements.txt` with `pip --require-hashes`. Python 3.12 or later,
GNU `time` and GNU `timeout` are required. Python optimization is refused.
The only Python package required is NetworkX 3.7.

## Data and mathematical meaning

`data/h.json` specifies an undirected graph on vertices 0 through 10,
46 simple cycles and 79 unordered pairs of vertex-disjoint cycles. The graph
has 22 edges and graph6 encoding ``J?bFF`wN?{?``. Attach a disk along each
listed cycle. Each pair denotes an unordered product of two disks in the quotient of the
deleted product by swapping factors, over the field with two elements.
The ordered lift contains both orders of every pair. Both checkers verify
that its boundary is zero and its intersection invariant is one.

This nonzero invariant obstructs an embedding of the resulting finite
two-dimensional complex in four-dimensional space. The cited topological
inputs are Lemma 12 and Theorem 18 of van der Holst and Pendavingh,
*On a graph property generalizing planarity and flatness*, Combinatorica
29 (2009), 337–361, [DOI](https://doi.org/10.1007/s00493-009-2219-6).
The numbering refers specifically to their April 26, 2008 author manuscript,
which was the text consulted. An open account of the same necessary condition and the crossing/invariant identity is [Kaluža–Tancer, arXiv:1907.05055v2, Appendix B.1, pages 25–26](https://arxiv.org/abs/1907.05055v2). The programs verify finite premises of these
theorems; they do not formalize the topological theorems themselves.
The [paper](../paper/paper.pdf) gives the bridge from these premises to
non-4-flatness, including the required triangulation and general position.

`checker_a.py` triangulates each disk by its own new cone vertex and uses
the alternating order of six points on the moment curve to count triangle
intersections modulo two. `checker_b.py` instead applies the deleted-product
boundary and half-chain recurrence from dimension four to dimension zero.
It does not call checker A or construct its fan triangulation. The programs
share the exact graph, cycle list and pair list in the JSON, and the
mathematical disk-boundary specification. They share no checking code.
Only A computes triangles; B works with unsplit cells. Both independently check graph and cycle validity,
disjoint supports, zero boundary, and an odd invariant. `data/k7.json` is a
positive control and `data/g1.json` is a second positive certificate.
Removing a selected pair from either H or G1 must fail the boundary test
in both implementations. A further control takes two disjoint copies of the K7 certificate: its nonzero chain has zero boundary and even invariant. A must reject it with `even intersection`, and B with `invariant is zero`. No floating-point arithmetic is used.

The paper's appendix lists all 46 cycles, 79 pairs, and the moment-curve
coefficient of every pair. Counting each edge–disk boundary incidence
modulo two gives zero; the 79 coefficients sum to one. `certificate.py`
regenerates this human-readable table and checks that it matches the paper.
This is a presentation consistency check, not a third independent proof.

## The minor exclusion

The replay verifies exactly that H is obtained from G1 by deleting the edge
with endpoints 1 and 10, with labels matching the published graph6 data.
The minor exclusion for G1 therefore implies the exclusion for H.
Five files from [heawood-family-mu5 v1](https://doi.org/10.5281/zenodo.24128771)
are downloaded from its release tag and checked against `prior.json`.
That file records the version, DOI, URLs and SHA-256 hashes.

The first published program regenerates all 78 Heawood-family graphs,
checks three positive minor controls, and enumerates the 354 relevant
G1 minors. The second program independently regenerates the family and
tests the minor exclusion, and must report no Heawood-family minor in G1.
The edge-count argument limiting the enumeration is explained in the paper.
These programs are reused unchanged, not presented as newly written code.

`minor_details.py` additionally compares H itself and all 44 single-edge
minors with the regenerated family. The family has twenty 21-edge and
fifty-eight 22-edge graphs. Every proper minor of H with at least 21 edges
arises from one edge deletion or contraction, so these comparisons suffice.
It also checks the circulant description in the paper, including the relabeling by multiplication by three modulo eleven. The same program checks two edge orbits of size eleven and supplies a
planarizing vertex pair for each of the 44 minors. The established
2-apex-implies-4-flat theorem then proves that all proper minors are 4-flat;
vertex deletion is covered because H has no isolated vertices. This
rechecks Mattman–Pierce's computer-search result, recalled by Kim–Mattman
and also established by the preceding paper's Lemma 8.

To use a local copy of that published result and retain per-command CPU,
peak-memory and output-hash receipts:

```sh
sh checks/check.sh --prior ../heawood-family-mu5 --receipts receipts
```

The local files must match the same hashes. Each child command has an
external ten-minute time limit. The replay checks all expected return
codes and parsed conclusions; an unexpected result stops the replay.
Receipts are saved before their bounded summaries are printed.

## Model and role credits

The work was produced under P. Graham's direction. The following identifies
the model and role of each contribution; computational acceptance is distinct
from review by a human expert.

| Files or contribution | Model and role |
| --- | --- |
| Reduction from the obstruction to the stated counterexample | GPT-6 Astra, mathematical lead |
| `data/*.json`, `checker_a.py` | GPT-6.1 Sol, certificate-search and direct-checker builder |
| `checker_b.py` | GPT-6.1 Sol, separately prompted independent-checker builder |
| Initial mathematical cold read | Anthropic Opus 5.5, cold reader |
| Certificate and semantic acceptance | Anthropic Sonnet 5.5, acceptance reader |
| Literature and source screening | GPT-6.1 Sol, novelty and source helpers; GPT-6 Astra, release source reader |
| Assessment of the exact result's public significance | GPT-6.1 Sol, fresh blind significance helper |
| `paper/paper.tex` and the graph figure | GPT-6.1 Sol, paper builder and revision builder; GPT-6 Astra, referee-response revision writer |
| Source clarification for the revision | GPT-6.1 Sol, source-audit helper |
| Abstract and introduction review before the publication referee round | Anthropic Opus 5.5, cold reader |
| `certificate.py`, `minor_details.py` and certificate appendix | GPT-6 Astra, release revision builder |
| `replay.py`, dependency lock, workflow and release documentation | GPT-6 Astra, release lead |
| Published `family.py` and `minor_exclusion.py` | Anthropic Opus 5.5, preceding-result builder |
| Published `checker_b.py` | Anthropic Opus 5.5, preceding-result independent-checker builder |
| Preceding-result cold reads and computational acceptance | Anthropic Opus 5.5, cold readers; Anthropic Sonnet 5.5, acceptance reader |

The two new obstruction programs were written in separate helper contexts,
but use the same model family. Their independence is by implementation and
mathematical checking mechanism, not by model family. Three Anthropic model readers passed the frozen paper in the publication referee, writing and source roles. The exact model identifiers were not exposed to this revision writer; this limitation is recorded rather than inferred. Their findings are addressed in this revision; acceptance of the revised bytes is pending. These AI reads do not constitute review by human experts.
