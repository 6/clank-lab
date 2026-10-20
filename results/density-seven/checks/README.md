# Checking the computer-assisted proof

The proofs, the search code, the certificate checkers and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

The entry point is `check.py`. Run it with ordinary Python, without `-O` or `PYTHONOPTIMIZE`: assertions are proof checks. `requirements.txt` records that no Python packages are required. Linux with Python 3.10+, Git, C/C++, Make, Rust/Cargo and network access to upstream sources and crates.io is required to build the external tools. Allow 16 GB RAM and about 3 GB of disk for builds, transient formulas and control proofs. Keep tools and work directories outside the bundle. Work directories must start empty.

From the bundle root:

```sh
python3 checks/build_tools.py /tmp/density-tools
python3 checks/check.py --quick --tools /tmp/density-tools --work /tmp/density-quick
python3 checks/check.py --full --tools /tmp/density-tools --work /tmp/density-full
```

`--quick` checks all nineteen formulas under explicit set-count semantics, the exact sixteen-case cover, all six global alphabet permutations on all 14,197 lines, both witness checkers, and negative controls. It also regenerates the L5 refutation and requires FRAT-rs, drat-trim and cake_lpr to accept it and to reject literal, hint and truncation corruptions. It does not replay any main-case refutation. This is the same check run by CI.

`--full` first runs those checks, then regenerates and checks every refutation. Each streamed obligation is semantically audited again, and the very same CNF file is passed to the solver and all checkers without regeneration. Every case must be UNSAT (solver exit 20), and both FRAT-rs and drat-trim must accept; cake_lpr must also accept L1/L4/L5 and s443 through s450. The final `PASS full theorem computation (19 UNSAT obligations)` appears only after all nineteen pass. `--case k1303_s450` instead checks just that one obligation; it is useful for a short end-to-end streaming test and does not establish the theorem. `data/cases.json` is the small formula specification, not a list of checked verdicts. The entry point validates its exact arguments against the endpoint.

Each case is independent and can run in a separate empty work directory on a different computer using `--case NAME`. To establish the computational upper bound this way, run the quick audit and all nineteen named cases. A failed or interrupted case is unverified and must run again. There is no mid-case solver checkpoint, and the entry point does not trust or skip a case based on previous result files. Keep successful case outputs if splitting the run. A disappeared process is not a certificate.

## What carries the proof

`encode.py` is the unchanged formula encoder used for the accepted endpoint. Its point variables use the alphabet 0,1,2. `reduction.py` is a standalone adaptation of the independently written semantic auditor: it imports no encoder code, executes the encoder, then justifies every clause. Repository-specific integrity and receipt handling have been removed; the mathematical clause checks are retained. It also rejects a removed line, a weaker L5 cap, a shifted slice premise and a weaker size premise. The case audit establishes the implication from a hypothetical set counterexample to a satisfying assignment. Unsatisfiability supplies the contradiction.

`symmetry.py` independently checks the repaired reduction symmetry and the arithmetic cover. One alphabet permutation acts simultaneously in all coordinates. A permutation in coordinate 1 alone need not preserve lines; a counterexample is included. The cap chain is conditional on the three auxiliary UNSAT obligations, which the full replay discharges in order. Witness files use the equivalent alphabet 1,2,3. The two witness programs independently enumerate all lines and require 1302 distinct points; missing-point and line-insertion controls must fail.

The written mathematical proof, including soundness of the encoding rules and induction, remains part of the trust boundary. There is no whole-theorem Lean proof. FRAT-rs and drat-trim are independently implemented proof checkers. cake_lpr is the additional verified checker within its evidenced scope; its verification does not formalize this entire theorem or our set-to-CNF reduction.

## Exact external tools

The builder fetches these upstream Git revisions, then builds locally:

| Tool | Repository | Revision | Role |
|---|---|---|---|
| CaDiCaL | https://github.com/arminbiere/cadical | `c60730422e758ef1cebe7aeddf2dda31c996bf04` | Generates text LRAT using `-q --lrat=true --binary=false` |
| FRAT-rs | https://github.com/digama0/frat | `aa18581497830b49a6ab6cbc9e0dc778c14885b5` | `frat-rs lratchk FORMULA PROOF` |
| cake_lpr | https://github.com/tanyongkiam/cake_lpr | `a36874a8b750b43fe4b385b8ddbf5b033e46a3fa` | `cake_lpr --CML_HEAP_SIZE=5000 --CML_STACK_SIZE=1024 FORMULA PROOF` |
| drat-trim | https://github.com/marijnheule/drat-trim | `2e3b2dc0ecf938addbd779d42877b6ed69d9a985` | Bundled unmodified `lrat-check.c`, compiled with `cc -O2` |

CaDiCaL is built with `./configure` and `make`; FRAT-rs with `cargo build --release --locked` using the supplied standard Cargo dependency lock. This lock is generated for this distribution; the historical acceptance used the same FRAT-rs source with a different dependency resolution. We do not claim byte-identical checker binaries or proof outputs across builds. Checked proof validity, not a proof-stream hash, is the public replay criterion. The builder uses cake_lpr's ARMv8 target on aarch64 and the x86-64 target otherwise. Its upstream pre-generated assembly and C runtime are compiled directly, as documented there; rebuilding its formal development is not a step in this replay.

FRAT-rs has no licence notice at this revision. Its source is fetched as an external dependency, not redistributed or relicensed here. The replay requires it: a network or upstream-access failure is a real missing dependency, never a successful check. CaDiCaL and cake_lpr are likewise fetched at the pinned revisions. The bundle contains the actual standalone drat-trim checker source and all target-specific checking code; no private repository paths, historical receipts or private binaries are needed.

## Resources and acceptance scope

The accepted independent computation checked all nineteen regenerated proofs with FRAT-rs and eleven with cake_lpr: the three auxiliary lemmas and eight main cases s443..s450. The original computation also used drat-trim on all nineteen. It is inaccurate to say that cake_lpr checked the remaining eight. The full public entry point requires both FRAT-rs and drat-trim for every obligation and cake_lpr for those same eleven; preparation exercises the adapted entry point on short obligations, using the existing accepted evidence for the large cases.

All nineteen proofs total 1,557,693,107,853 bytes (largest about 419 GB). Historical independent regeneration used about 64 solver CPU-hours, 9.7 FRAT-rs CPU-hours and 0.9 cake_lpr CPU-hours; encoder/auditor time and the drat-trim replay are additional. Expect hardware-dependent costs of at least that order. The largest single case took about 21.4 hours. Sequential full checking can take several days. Streaming buffers are bounded; the LRAT streams are not saved. Transient formulas are removed only after successful checking; logs and per-case result records stay in the chosen work directory. Large generated proofs are intentionally absent from Git and the distribution.

To rebuild the manuscript, use a standard TeX installation:

```sh
pdflatex -output-directory=/tmp paper/paper.tex
pdflatex -output-directory=/tmp paper/paper.tex
```

The resulting `/tmp/paper.pdf` is the paper. This typesetting step is separate from the theorem check.
