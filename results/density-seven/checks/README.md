# Checking the computer-assisted proof

The proofs, the search code, the certificate checkers and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

The entry point is `check.py`. Run it with ordinary Python, without `-O` or `PYTHONOPTIMIZE`: assertions are proof checks. `requirements.txt` records that no Python packages are required. Linux with Python 3.10+, Git, C/C++, Make, Rust/Cargo and network access to upstream sources and crates.io is required to build the external tools. For builds and quick mode, allow 16 GB RAM and about 3 GB of disk for builds, transient formulas and control proofs. Full checking needs substantially more RAM, as detailed below. Keep tools and work directories outside the bundle. Work directories must start empty.

From the bundle root:

```sh
python3 checks/build_tools.py /tmp/density-tools
python3 checks/check.py --quick --tools /tmp/density-tools --work /tmp/density-quick
python3 checks/check.py --full --tools /tmp/density-tools --work /tmp/density-full
```

`--quick` checks all nineteen formulas under explicit set-count semantics, the exact sixteen-case cover, all six global alphabet permutations on all 14,197 lines, both witness checkers, and negative controls. It also regenerates the L5 refutation and requires FRAT-rs, drat-trim and cake_lpr to accept it and to reject literal, hint and truncation corruptions. It does not replay any main-case refutation. This is the same check run by CI.

`--full` first runs those checks, then regenerates and checks every refutation. Each streamed obligation is semantically audited again, and the very same CNF file is passed to the solver and all checkers without regeneration. Every case must be UNSAT (solver exit 20), and FRAT-rs, drat-trim's `lrat-check` and cake_lpr must all accept every one of the nineteen obligations. FRAT-rs must exit 0; `lrat-check` must exit 0 with `c VERIFIED`, and cake_lpr must exit 0 with `s VERIFIED UNSAT`. The final `PASS full theorem computation (19 UNSAT obligations)` appears only after all nineteen pass. `--case k1303_s450` instead checks just that one obligation with the same three required checkers and its case-specific heap; it is useful for a short end-to-end streaming test and does not establish the theorem. `data/cases.json` is the small formula specification, not a list of checked verdicts. The entry point validates its exact arguments against the endpoint.

Each case is independent and can run in a separate empty work directory on a different computer using `--case NAME`. To establish the computational upper bound this way, run the quick audit and all nineteen named cases. A failed or interrupted case is unverified and must run again. There is no mid-case solver checkpoint, and the entry point does not trust or skip a case based on previous result files. Keep successful case outputs if splitting the run. A disappeared process is not a certificate.

`--part K/N` with `--quick` or `--full` runs share K of N of the independent steps (the symmetry check, each formula's audit, the cover, each negative control, each witness checker, the proof controls and, with `--full`, each case), balanced by their running time; `--list` prints the steps a part would run. Every part from 1/N to N/N must pass, each in its own empty work directory; together they run exactly the checks of the whole run. A part with no proof step needs no tools. The public CI runs the quick check this way, as eight parts.

## What carries the proof

`encode.py` is the unchanged formula encoder used for the accepted endpoint. Its point variables use the alphabet 0,1,2. `reduction.py` is a standalone adaptation of the independently written semantic auditor: it imports no encoder code, executes the encoder, then justifies every clause. Repository-specific integrity and receipt handling have been removed; the mathematical clause checks are retained. It also rejects a removed line, a weaker L5 cap, a shifted slice premise and a weaker size premise. The case audit establishes the implication from a hypothetical set counterexample to a satisfying assignment. Unsatisfiability supplies the contradiction.

`symmetry.py` independently checks the repaired reduction symmetry and the arithmetic cover. One alphabet permutation acts simultaneously in all coordinates. A permutation in coordinate 1 alone need not preserve lines; a counterexample is included. The cap chain is conditional on the three auxiliary UNSAT obligations, which the full replay discharges in order. Witness files use the equivalent alphabet 1,2,3. The two witness programs independently enumerate all lines and require 1302 distinct points; missing-point and line-insertion controls must fail.

The written mathematical proof, including soundness of the encoding rules and induction, remains part of the trust boundary. There is no whole-theorem Lean proof. FRAT-rs and drat-trim are independently implemented proof checkers. cake_lpr is the additional verified checker for all nineteen obligations; its verification does not formalize this entire theorem or our set-to-CNF reduction.

## Exact external tools

The builder fetches these upstream Git revisions, then builds locally:

| Tool | Repository | Revision | Role |
|---|---|---|---|
| CaDiCaL | https://github.com/arminbiere/cadical | `c60730422e758ef1cebe7aeddf2dda31c996bf04` | Generates text LRAT using `-q --lrat=true --binary=false` |
| FRAT-rs | https://github.com/digama0/frat | `aa18581497830b49a6ab6cbc9e0dc778c14885b5` | `frat-rs lratchk FORMULA PROOF` |
| cake_lpr | https://github.com/tanyongkiam/cake_lpr | `a36874a8b750b43fe4b385b8ddbf5b033e46a3fa` | `cake_lpr --CML_HEAP_SIZE=HEAP --CML_STACK_SIZE=1024 FORMULA PROOF` (heap by case below) |
| drat-trim | https://github.com/marijnheule/drat-trim | `2e3b2dc0ecf938addbd779d42877b6ed69d9a985` | Bundled unmodified `lrat-check.c`, compiled with `cc -O2` |

CaDiCaL is built with `./configure` and `make`; FRAT-rs with `cargo build --release --locked` using the supplied standard Cargo dependency lock. This lock is generated for this distribution; the historical acceptance used the same FRAT-rs source with a different dependency resolution. We do not claim byte-identical checker binaries or proof outputs across builds. Checked proof validity, not a proof-stream hash, is the public replay criterion. The builder uses cake_lpr's ARMv8 target on aarch64 and the x86-64 target otherwise. Its upstream pre-generated assembly and C runtime are compiled directly, as documented there; rebuilding its formal development is not a step in this replay.

FRAT-rs has no license notice at this revision. Its source is fetched as an external dependency, not redistributed or relicensed here. The replay requires it: a network or upstream-access failure is a real missing dependency, never a successful check. CaDiCaL and cake_lpr are likewise fetched at the pinned revisions. The bundle contains the actual standalone drat-trim checker source and all target-specific checking code; no private repository paths, historical receipts or private binaries are needed.

## Resources and acceptance scope

All nineteen refutations have accepted FRAT-rs checks from the historical independent regeneration, and the original computation checked all nineteen with drat-trim. Eleven also had historical cake_lpr checks: L1/L4/L5 and s443..s450. Eight subsequent cake-only runs checked s435..s442, requiring their audited CNF hashes and complete streamed proof hashes and byte counts to match the archived independent checks. These eight runs did not repeat FRAT-rs or drat-trim. Together the retained checks and identity-bound streams give cake_lpr coverage of all nineteen; they are not a new full nineteen-case replay. The public entry point now requires all three checkers on every obligation in both `--full` and `--case`.

All nineteen proofs total 1,557,693,107,853 bytes (largest about 419 GB). Historical independent regeneration used about 64 solver CPU-hours, 9.7 FRAT-rs CPU-hours and 0.9 cake_lpr CPU-hours for the eleven then checked by cake_lpr; encoder/auditor time and the original drat-trim checking are additional. Its largest single case took about 21.4 wall hours. These measurements describe that historical campaign, not the cost of the amended three-checker public replay.

The subsequent eight cake-only runs measured the following resources. CPU-hours include solver, cake_lpr, semantic audit and relay; wall hours are elapsed per run. Peak RSS is for the cake_lpr process alone (Linux KiB converted to GiB), not a simultaneous whole-machine peak.

| Case | CakeML heap (MiB) | cake_lpr peak RSS (GiB) | Wall hours | Total CPU-hours |
|---|---:|---:|---:|---:|
| s435 | 32768 | 32.035 | 24.900 | 34.908 |
| s436 | 40960 | 40.030 | 11.450 | 16.364 |
| s437 | 60000 | 58.620 | 10.082 | 13.441 |
| s438 | 60000 | 58.622 | 11.295 | 13.631 |
| s439 | 60000 | 58.620 | 6.496 | 8.453 |
| s440 | 40960 | 40.026 | 4.820 | 6.961 |
| s441 | 60000 | 58.618 | 2.938 | 4.402 |
| s442 | 60000 | 58.619 | 1.688 | 2.518 |

These eight runs used 100.678 CPU-hours in total, including 67.960 solver and 25.090 cake_lpr CPU-hours. Their longest run took 24.900 wall hours. These are additional measurements, not a replacement or an estimate for the historical full checks. Memory-event counters were unavailable for s437, s439, s441 and s442; the other four reported no memory-event increases.

The entry point uses the listed heaps, and 5000 MiB for each of the historical eleven obligations, with a 1024-MiB CakeML stack throughout. A heap setting is not an entire-machine RAM bound: runtime overhead, the stack, solver, semantic audit and relay also need memory, and the public replay runs FRAT-rs and drat-trim concurrently with cake_lpr. Their concurrent memory use is additional and was not measured by these cake-only runs. Allow more than the largest measured 58.622-GiB checker RSS for a large case; the 16-GB allowance above is for builds and quick controls only. Sequential full checking can take several days, and the amended full replay has not been timed end to end.

Streaming buffers are bounded; the LRAT streams are not saved. Transient formulas are removed only after successful checking; logs and per-case result records stay in the chosen work directory. Large generated proofs are intentionally absent from Git and the distribution.

To rebuild the manuscript, use a standard TeX installation:

```sh
pdflatex -output-directory=/tmp paper/paper.tex
pdflatex -output-directory=/tmp paper/paper.tex
```

The resulting `/tmp/paper.pdf` is the paper. This typesetting step is separate from the theorem check.
