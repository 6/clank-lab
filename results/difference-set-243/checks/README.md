The claim is restricted to (243,121,60) difference sets in
C3 × C9 × C9, with element encoding 81x + 9y + z. A difference set has
121 points and represents each nonzero group element exactly 60 times among
ordered differences. No assertion about another group or parameter follows.

Run from the public subtree root. Python 3.10 or later and GNU g++ with C++20
and OpenMP support are required; Python uses only its standard library. Run with assertions enabled (no `-O` or
`PYTHONOPTIMIZE`).
See [requirements.txt](requirements.txt). Set N to all allocated CPU cores.
Each output directory must be new, outside the public subtree. All generated
binaries, checkpoints, and results go there.

```sh
python3 checks/check.py quick --threads N --work /chosen/new/quick
```

Quick checks the finite certificate and actual input structure, all compiled
options, eight fixed depth-12 IDs in each of the three complete kernels,
same-group positive-prefix controls, a genuine positive discovery control in
C121, and corruptions. It ends with
`QUICK CHECK ONLY` and never claims exhaustive lifting replay. Allow roughly
one minute, depending on compilation and available cores. Its finite artifact
check validates the supplied maps and cover; it does not establish that the
singleton and quotient enumerations are complete.

For the complete executable check, including independent finite enumeration,
the fixed 10,000-ID sample, and exhaustive lifting in all three complete kernels:

```sh
python3 checks/check.py full --threads N --work /chosen/new/full
```

This is a substantial computation: allow hundreds of CPU-hours for all three
complete lifting passes. It starts each pass from empty tasks, visits every
range, compares every range's actual canonical row digest and counters, and
runs fresh range-0 digest corruptions. It reads no previous search output.
Completed full-search evidence is represented by the expected mathematical
range rows in `data/ranges.json`; checking that file alone is not a replay.

The same checks can be separated without changing their mathematics:

```sh
python3 checks/check.py frontend --threads N --work /chosen/new/frontend
python3 checks/check.py sample --threads N --work /chosen/new/sample
python3 checks/check.py replay --kernel all --threads N --work /chosen/new/replay
python3 checks/check.py corruptions --threads N --work /chosen/new/corruptions
```

`frontend` regenerates the singleton classification and all quotient images,
checks equality with every mathematical field of `data/frontend.json`, rejects
38 input mutations, and accepts an equivalent case representative. It also runs
the separate singleton enumeration over all 20,058,300 thirteen-element subsets,
two distinct quotient constructions, full-group cover checks, and 1,000
fixed-seed round trips of disguised leaves through centering, singleton and
quotient normalization, and digit recovery. Expect several minutes.

The frontend/full checks also run the separate exhaustive cover package.
It derives every scalar-fixed subset of each nine-point cell, checks all actual
compiled options, and proves the Cartesian-product bijection. It exports the
actual production decoders with their mutable search states replaced only by
always-accepting tracers, then independently compares every one of the 4,251,528
17-byte ID/case/digit records from each decoder. Independent rank/unrank and
prefix-cylinder adjacency checks cover all 3^24 words per case. This computes
no tail search. The observation exporter is a production adapter; the separate
cover checker imports no production code.

Three shape-preserving semantic gaps must be rejected with concrete missing
witnesses: omit ID 4095 while compensating the total interval length, duplicate
an option while retaining its size and scalar invariance, and duplicate a case
while retaining eight representatives. This complete check is available alone:

```sh
python3 checks/check.py cover --threads N --work /chosen/new/cover
```

It regenerates about 290 MB of temporary decoder streams outside the public
subtree; none are distribution inputs. A 1,000-trial normalization control is
additional evidence and does not replace these all-ID comparisons.

`replay` supports `--kernel fast`, `direct`, or `independent` and disjoint
`--first-range A --stop-range B` pieces, where 0 ≤ A < B ≤ 1038. Partial pieces
say `BOUNDED REPLAY ONLY`. Supply all disjoint output directories to
`summary --kernel all --pieces DIR1 DIR2 ...` to check complete matching range
records for each kernel. Summary reads records; only replay executes search.
Checkpoints preserve partial task rows for inspection, but commands always
start fresh and do not resume previous results. Keep long-run output directories
on durable storage. There is no cutoff that counts an unfinished ID as clear.

The production implementations in `campaign.cpp` share their wrapper, case
representatives, cell order, option tables, prefix-ID rule, and range decomposition.
The fast kernel counts in 49 difference classes with precomputed contributions;
the direct kernel counts individual elements and 243 signed differences. Their
agreement alone cannot check the shared decomposition. `independent_kernel.cpp`
has its own option construction and recursive tail DFS. It validates the input
multiplier orbits and uses the same ordered mathematical cases. It is available
for complete replay, not just sampling. `sample_kernel.cpp` additionally derives
its own scalar orbits without reading `p243.txt`; its fixed sample contains the
first and last 25 IDs of each case, filled to 10,000 distinct IDs with seed
20261020. A sample is never described as exhaustive.

Both compiled production option dumps are compared against independent
ordered definitions for every one of the 8 × 24 × 3 options, including the
coefficient-6 omit-orbit convention. A deliberately dropped compiled option
must fail. The separate cover implementation also compares the complete option
families. These comparisons exercise compiled tables, not a transcription of
their source. The input partition is checked structurally as the exact ordered
27 singleton and 72 triple multiplier orbits. Cases must hit the eight quotient
orbits once, with exact weights 27,27,9,9,27,27,9,9. Regrouped triples, duplicate
cases, changed weights, bad maps, omitted cover entries, and malformed fields
are explicit failures. `discovery.cpp` separately enumerates all unions of eight of the 24 nonzero
multiplication-by-3 orbits in C121, receiving no witness. It must recover exactly
88 distinct (121,40,13) sets. Python independently checks every recovered set's
40 distinct points, multiplier invariance, and all ordered difference counts.
This separate discovery control has no instrumented search-node counter; the
older three-implementation observation of 996,935 nodes uses a different
traversal and is not asserted by this command. The public discovery control
makes no claim about C11 × C11.

The relaxed-bound positive-prefix tests are compiled
with `TEST_ONLY`, use their own independently computed point sets, test adjacent
IDs and the insufficient bound M−1, and never serve as difference-set witnesses.
Production replay binaries contain no `TEST_ONLY` flag.

At depth 12, ID = case·3^12 + prefix, with big-endian ternary prefix digits.
The 1,038 ranges are [4096r, min(4096(r+1), 4,251,528)). Each final row is
`id valid nodes solutions`, in ascending ID order, decimal ASCII with single
spaces and a final LF. Nodes count valid tail nodes, including the tail root;
prefix construction is excluded. Range SHA-256 values identify these canonical
mathematical row streams. They are computation evidence, not file-integrity
or inventory checks. All three complete kernels must match the range fields
and find zero solutions. Missing, partial, duplicate, malformed, or mismatched
rows fail.

Lean is a normal, separately checked Lake project:

```sh
cd lean
lake exe cache get
lake build
```

Lean and Mathlib are pinned by the standard project files. Elan installs the
pinned toolchain. The default build includes the proof, exact statement types,
definition controls for the group, difference-set predicate, mask, cases,
prefix digits and all 576 ordered options, an admissible survivor that cannot be
dropped from the witness table, plus `#guard_msgs` axiom checks
allowing only `propext`, `Classical.choice`, and `Quot.sound`. It also builds
proofs refuting the dropped-last-range, weak-pruning, and weak-leaf rules.

`DS243.coverage` proves the reduction to the ranges from the group definitions.
`DS243.no_difference_set` is conditional on 1,038 `Receipt` hypotheses;
`Receipt r label` contains `RangeClear r`. Its string label is the canonical
row digest, not a proof of its contents. The default build checks the equivalent
statement using `∀ r, r < 1038 → RangeClear r`. The exhaustive negative range
assertions are supplied by the computation, not proved in Lean. Do not describe
the final negative result as an unconditional Lean proof.

The checked sources in `lean/DS243/` contain the mathematical proofs and finite
witness tables. No table generator is needed to build them: each finite claim
is checked in the Lean kernel. Mathematical data and executable checks have no
path into any other repository. Build Lean in a working copy; generated `.lake/`
files are not part of the public source bundle.

Third-party dependency and data license details are in
[THIRD_PARTY.md](../THIRD_PARTY.md).
