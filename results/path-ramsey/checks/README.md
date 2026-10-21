# Executable checks

The Lean development in [`../lean`](../lean) proves R(P10, P10, P10) = 18
from nine UNSAT facts about explicit formulas: seven ladder rungs
R(P_m, P_m, P_m) ≤ n, the cover of the K_18 cube list, and the 15,956 K_18
cubes. Lean checks each fact from a certificate with its own verified LRAT
checker. The certificates total about 60 GB, so they are not shipped: the
script here regenerates them with the bundled solver and hands them to
Lean. It also runs a separate cross-check that does not use Lean.

## Requirements

Python 3.9 or later (standard library only, see
[requirements.txt](requirements.txt)), git, gcc, g++ and make, network
access to GitHub, and Lean through [elan](https://github.com/leanprover/elan)
with `lake` on the path. Run `lake exe cache get` in `../lean` once first
(the script also runs it).

## Commands

Run from the folder above this one. `--work` names a directory outside the
bundle for the tools and temporary files (default: one under the system's
temporary directory). Certificates and generated Lean modules go to
`../lean/generated/`.

```sh
python3 checks/check.py quick --work /tmp/path-ramsey-work
python3 checks/check.py full --work /tmp/path-ramsey-work
```

`quick` takes about ten to fifteen minutes on two to four cores, most of it
the K_17/P_9 rung. `--part K/N` runs the K-th
of N balanced parts and `--list` lists a part's steps; leaving `--part` off
runs everything. `--sample S` and `--seed X` choose the sampled cubes
(default: 8 cubes, a random seed that is printed).

`full` re-solves every one of the 15,956 cubes and checks every cube in
Lean, then the ladder and the cover: about 250 CPU-hours, using every core
(`--jobs`). With `--cross-check` it also runs the independent check that
doesn't use Lean on every cube (`check_paths.py`, `check_inputs.py` and
cake_lpr). It splits the cubes into the 162 chunks of
[`../data/chunks.json`](../data/chunks.json), one Lean module
`R3P10Cubes.C<k>` each, and builds each chunk as soon as its cubes are done;
a chunk's certificates are deleted once its module is built, since the
`.olean` file contains them. Rerunning the same command resumes from the
records in the work directory. Plan for about 70 GB of free disk space in
`../lean` (the chunk `.olean` files) and up to about 7 GB of memory per
Lean build (`--lean-jobs`, default 2). `--chunks 0-40,77` restricts a run
to some chunks. When every chunk is built,
the script writes `../lean/generated/R3P10Cubes.lean`, which joins the
chunk ranges, and runs `lake build R3P10Final`, whose `R3_P10_eq_18 :
ramsey3Path 10 = 18` must have exactly the axioms `propext`,
`Classical.choice`, `Lean.ofReduceBool`, `Lean.trustCompiler` and
`Quot.sound`.

## What `quick` checks

| Step | What it checks |
| --- | --- |
| `inputs` | `encode.py` prints every formula in `../data/cnf` byte for byte; `lower_bound.py` prints `../data/k17-coloring.txt`; the final cube list has 15,956 cubes. |
| `checkers` | `check_paths.py` accepts `controls/paths-good.txt` and rejects the ten `controls/paths-bad-*.txt`; `check_inputs.py` rejects a formula with an extra or a missing unit clause; `check_colouring.py` accepts the K_17 coloring, finds a P_9 in it, and finds a P_10 after edge {0, 9} is recolored. |
| `audit` | The independent encoding auditor (below), its 30 corruption controls and its mutation test. |
| `cubes` | `p3path --gencubes 10` regenerates `../data/k18/cubes.txt` and its generation log; splitting the 16 parents regenerates the 656 children and their log. |
| `ladder` | The seven rungs re-solved whole and the cover re-derived by CaDiCaL; each proof checked by drat-trim and cake_lpr, its clause log by `check_paths.py` and the auditor, its input by `check_inputs.py`; then `lake build R3P10Ladder` checks all eight certificates in Lean. |
| `sample` | Randomly chosen K_18 cubes, checked the same way, then `lake build R3P10Sample`. A cube whose solve takes over 300 seconds (about 1 in 70) is skipped and another drawn; `full` does every cube. |
| `planted-certs` | From the K_10/P_6 certificate: a negated lemma literal, a dropped hint, a repeated path vertex, the certificate against the K_13/P_7 formula, and the K_18 formula compared with the wrong file are each rejected by Lean, and the unchanged certificate is accepted. cake_lpr rejects a corrupted lemma and a swapped formula. |
| `planted-lean` | Seven unsound edits to the Lean development (a path clause missing an edge, a dropped clause, a generator that moves the fixed path, a fixed path one edge too long, the lex comparison reversed, a skip test ignoring the color map, a recolored K_17 edge) each make `lake build` fail in the expected declaration. |

## The pipeline for one refutation

1. `p3path` (CaDiCaL with an external propagator) solves a formula of
   `../data/cnf`, optionally with a cube's literals as assumptions. It
   adds path clauses lazily, writes each one to a clause log, and writes a
   DRAT proof of the formula plus the log plus the cube's unit clauses.
2. `check_paths.py` checks that every logged clause says "not every edge of
   this path on m vertices has color c".
3. `check_inputs.py` checks that the file given to the proof checkers is
   exactly the formula, the log and the units.
4. drat-trim turns the DRAT proof into LRAT, and cake_lpr (verified in
   CakeML) checks it.
5. `pack.py` repacks the LRAT proof for Lean: the formula plus the log
   clauses the proof uses, each given as a color and a vertex sequence, and
   the proof steps, in one compact string. In Lean, `checkUnsat_sound`
   (`../lean/R3P10/Sat.lean`) turns a successful check into the fact
   `UnsatWithPaths n m F`: Lean rebuilds every path clause from its path and
   checks the path is valid, so nothing outside Lean decides what counts as
   a path clause. Steps 2 to 4 are a separate cross-check; the Lean proof
   does not depend on them, on the solver or on `pack.py`.

The cover is the same with CaDiCaL in place of `p3path`: the K_18 formula,
both generation logs and the negation of every cube of the final list.

## The encoding

A coloring gives each edge of K_n one of the colors 0, 1, 2. Edges (i, j),
i < j, are numbered row-wise, and variable 3e + c + 1 means "edge e has
color c". The formula `encode.py n m --fix k` has:

- exactly one color per edge;
- with k > 0, color 0 on the path 0, 1, ..., k-1. This is sound because the
  rung below gives R(P_k, P_k, P_k) ≤ n: any coloring of K_n has a
  monochromatic P_k, and relabeling vertices and colors moves it there;
- lex-leader constraints X ≤lex g(X), with an auxiliary variable per
  compared position meaning "X and g(X) agree up to here", for generators g
  that map the set of colorings above to itself: with k > 0, the
  transpositions of {k, ..., n-1}, the reversal of the path and the color
  swap 1 ↔ 2; with k = 0, every vertex transposition and the color swaps
  0 ↔ 1 and 1 ↔ 2. The least coloring of each orbit satisfies all of them.

Path clauses are not in the files: the solver adds the ones it needs and
logs them. In Lean, `encode n k` (`../lean/R3P10/Defs.lean`) is the same
formula in closed form, proved sound for all n and k, and `Checks.lean`
checks that its DIMACS text equals each file byte for byte.

## The encoding auditor

[`audit/audit.py`](audit/audit.py) was written from the problem and the
statement of the encoding alone, without reading the encoder, the solver or
`check_paths.py`. It checks these lemmas, the first column naming them as
the auditor's messages do:

| Lemma | Statement | How |
| --- | --- | --- |
| L1 | Relabeling vertices and colors preserves "no monochromatic P_m". | Argued; exhaustive on K_4 and K_5. |
| L2 | A fixed P_k can be moved to color 0 on 0..k-1. | Argued; each rung's premise comes from a lower rung solved whole (`ladder`). |
| L3 | Every generator maps the fixed-path set to itself. | Checked for every generator of every rung. |
| L4 | The lex-least coloring of an orbit meets every generator inequality. | Argued; exhaustive on small instances. |
| L5 | Every clause holds for every admissible coloring, auxiliaries at their meaning. | Checked clause by clause on all eight formulas; 12,000 mutated clauses on small instances (`audit/soundness_fuzz.py`). |
| L5' | The clause multiset is exactly the one the stated meaning generates. | Checked on all eight formulas. |
| L6 | Every logged clause is a path clause. | Checked on the generation logs and every log the checks produce. |
| L7 | A refuted formula with fewer path clauses refutes the one with all of them. | Argued (monotonicity); exhaustive on small instances. |
| L8 | Together these give R(P10, P10, P10) ≤ 18. | Argued. |

[`audit/corruptions.py`](audit/corruptions.py) runs 30 controls, each of
which must be rejected (one, an incomplete lazy log, is accepted by design,
by L7). The Lean proof now covers L1 to L8 formally; the auditor remains an
independent check of the formula files.

## Files

- `check.py`: the entry point.
- `p3path.cpp`: the solver (CaDiCaL is downloaded and built at a pinned
  commit, see [../THIRD_PARTY.md](../THIRD_PARTY.md)).
- `encode.py`: the formula generator.
- `check_paths.py`, `check_inputs.py`, `check_colouring.py`: the
  independent checkers; `lower_bound.py`: the K_17 coloring.
- `pack.py`: the certificate packer for Lean.
- `planted_certs.py`, `planted_lean.py`: the planted errors.
- `audit/`: the encoding auditor; `controls/`: the path-clause controls.
