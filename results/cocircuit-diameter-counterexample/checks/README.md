# Technical checking guide

The proofs, the Lean formalization, the certificate checkers and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

This directory checks exact source geometry and a bounded control. The theorem concerns a rational 80-by-41 matrix, all its real signed cocircuits, and the absence of a walk of at most 41 edges between complementary endpoints. The certificate describes the designated pair in the 40-row source factor. It does not enumerate the final graph. The final rational matrix is chosen nonconstructively by the Lean perturbation argument; there is no decimal matrix export.

The supplementary mathematical source inventory has SHA-256
`663daa4f3e4880d88075887d7cbe031bbf53731424576d0d9394abde959ab411`.
It pins 155 source, input and checking files, including the per-output
manifest for the omitted Lean modules. The ordinary quick check verifies
these bytes and this guide's inventory hash before checking the geometry.
To check the inventory separately, from the bundle root run:

```sh
python3 -I checks/check_proof_sources.py --guide checks/README.md
```

Install Python 3.11 or newer and the pinned Python dependencies. From the bundle root:

```sh
python3 -m pip install -r checks/requirements.txt
cd lean
lake exe cache get
cd ..
python3 -I checks/quickcheck.py --cpus 2 --work /tmp/cocircuit-quick --checkpoint /tmp/cocircuit-results/quick.json --cpu-hours 1
```

Set `--cpus` to the actual allocated CPU count. Work and checkpoint directories must be outside the bundle. `--geometry-only` omits the Lean control and needs no Lean installation. The full quick command is suitable for hosted CI: it checks both source and control geometry, all 28 semantic corruption rejections, source transcription, the small finite Lean certificate, the seven published-definition bridge guards, and rejection of a deliberately false proposition by kernel reduction. It does not rebuild or establish the rank-41 theorem. A quick CI pass must be described as a quick check.

The independent checkers use integer Bareiss elimination and scalar arithmetic (`check_fraction.py`), and rational matrices supplied by python-flint (`check_rational.py`). Neither imports the other or a search. They check exact feasible rays, active labels, invertible active bases, ridge closure, edges, a 1-Lipschitz potential, designated endpoints, and a matching path. They exhaustively enumerate all bases only for the small control. At source size, full geometric cover follows from the Lean source-cover theorem and its checked local premises, rather than a Python exhaustive-basis claim.

The paper's appendix specifies the integer source matrix and a compact
positive-functional witness. Check its 41 sets of weights using Python's
standard library, and compare the matrix with the pinned source data:

```sh
python3 checks/check_written_certificate.py --data data --check-paper paper/paper.tex --output /tmp/cocircuit-written-certificate.json
```

The checker prints a clear PASS or FAIL status on standard error and writes
the detailed JSON report to the requested output file. It evaluates every
stated determinant, verifies the identities
by direct integer sums, checks all weight bounds, and binds the appendix
tables to the constants it checks. This written witness differs from
the one in the unchanged formal certificate; see the
[formal checking note](../lean/FORMAL_STATEMENT.md).
That note also distinguishes the standard oriented-matroid interpretation,
the written attaining upper bound and the two perturbation constructions
from the matrix lower bound proved in Lean.

Successful runs produce this certificate status on standard error and the
following fields in the quick check's JSON summary (excerpt; timings and
source signatures vary):

```text
PASS written certificate: 41 cones; 861 Cramer ratios; all identities and weight bounds verified.
```

```json
{
  "complete": true,
  "source_geometry": true,
  "control_geometry": true,
  "semantic_rejections": 28,
  "bounded_lean_control": true,
  "full_endpoint_rebuilt": false
}
```

A changed printed appendix fails with a nonzero exit and, for example:

```text
FAIL written certificate: AssertionError: printed certificate differs from checked constants
```

The quick command above uses Python's isolated mode. It imports the
checking modules from this bundle's resolved directory, without using the
working directory or `PYTHONPATH` to locate those modules.

`corruptions.py` changes a coordinate, deletes an active label, alters the input matrix, consistently deletes a vertex together with all its incident edges and index references, deletes an edge, changes the endpoint potential, or reverses the endpoints. Each checker must reject through an assertion, value error, or index error inside its semantic verification. Import failures and failed subprocess setup are failures of the checking command, never successful rejections.

The source certificate is stored as two parts smaller than 2 MB.
Regenerate all omitted finite Lean modules with:

```sh
python3 checks/bootstrap_kernel.py
```

Bootstrap authenticates the input files and generator recipes, reconstructs
all 1,148 modules in a temporary directory, and checks every output against
`generated-kernel-sha256.json` before installation. It never invokes Lean.
Existing mismatched files are rejected; explicitly delete a damaged
generated file before regenerating it. To check an already materialized
source tree, or materialize only the small control, use:

```sh
python3 checks/bootstrap_kernel.py --check
python3 checks/bootstrap_kernel.py --scope control
```

The generator preserves all source labels, integer-scaled rays, neighboring
labels and potentials. `prepare_kernel.py --public-export` converts its
ordinary `decide` chunks to kernel-reduction modules with the public import
names. It uses the same transformation as
`check_source_kernel.py --kernel-reduction --async-kernel`, calls
`Lean.Meta.mkDecideProof` and submits the resulting term to the kernel.
It does not use `native_decide` or admit an externally evaluated Boolean.
The quick command materializes its six control modules before recording
its source signature; the bounded full driver materializes all modules
before fresh or resumed builds. Adding full source modules after a quick
checkpoint requires a new quick-check checkpoint.

Packaging controls, including altered input/recipe/manifest rejection and
missing or changed generated-module rejection, run without Lean:

```sh
python3 checks/test_bootstrap_kernel.py
```

For the complete theorem, use the [Lean guide](../lean/README.md). All data, code and Lean sources needed for checking are inside this bundle; only the public pinned toolchain, mathlib dependencies and Python packages are external. License and numerical-source provenance are in [THIRD_PARTY.md](../THIRD_PARTY.md).

The [source geometry checking guide](../lean/SOURCE_CERTIFICATE.md) maps the
source certificate facts used by the paper to their exact Lean statements
and separates them from the independent printed-witness arithmetic.

## Sources used during development

Adler, De Loera, Klee and Zhang record the general conjecture as folklore
on the basis of Fukuda's personal communication to them. Their
Proposition 8 and its proof supply the earlier uniform nonantipodal
lower-bound example and sign-transition argument. They already answer
Finschi's Open Problem 2 and the equality half of Felsner and
collaborators' Question 4.2. Their proof uses a distance-21 source pair;
this bundle supplies an explicit attaining path for its numerical instance
and extends the count to negative coordinates visited by a short walk.

Matschke, Santos and Weibel's Theorem 1.3 in the cited arXiv version
constructs a 20-prismatoid with 40 vertices and width 21 whose polar is
non-Hirsch. Identification of the numerical instance with that polytope
rests on attribution. The Coq-Polyhedra numerical file has no author line;
attribution to Weibel follows Allamigeon, Canu and Strub's account of
supplied inequality instances. Our transcription was compared entrywise
with the pinned file, but not with MSW's table or the original Coq input.
Our certificate checks this matrix independently. Allamigeon, Canu and
Strub's source-graph certification is in Section 5, page 12 of the cited
arXiv version. Santos's product amplification is Lemma 6.1, which cites
Klee–Walkup; the Klee–Walkup original was not read.

Knauer's 2010 dissertation states the uniform questions in Question
3.3.2. Klee's Oberwolfach contribution, Report 39/2019, pp. 2424–2426,
states the general bound as Conjecture 1 on p. 2425 and attributes its
introduction to Fukuda and Terlaky. The report became available in
September 2020; the original posing was not recovered. Knauer's later
Conjecture 18 is on p. 69 of a manuscript dated November 17, 2021;
its first posting is unverified. Zhang's June 2022 dissertation gives
Conjecture 1.4.1 on p. 21 and Proposition 1.4.7 on p. 24. These selected
passages supplied historical corroboration; no proof from either
dissertation is imported.

The [literature notes](../lean/LITERATURE.md) record the exact source
versions, locators and reading limits, including adjacent work. These
limits and the comparisons not made remain part of the source record.
