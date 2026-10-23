# Checking the exhaustion record

The entry point is `python3 checks/check.py`, run from the result's root.
Install the Python packages with `python3 -m pip install -r checks/requirements.txt`.
Requirements are Python 3.10 or newer, GCC and G++ with OpenMP, and OpenSSL
development headers and `libcrypto`. On Debian or Ubuntu the system packages
are `build-essential` and `libssl-dev`. Use little-endian Linux, IEEE double
arithmetic, and no fast-math compiler options. Allow about 8 GB of memory and
8 GB of temporary disk space. The ordinary check takes tens of minutes
on a recent computer; it does not rerun the complete order-65 search.

The programs compile into a temporary directory and delete it after success.
`--work DIRECTORY` instead creates a new directory and retains the regenerated
data and check outputs there. `--threads N` sets the OpenMP thread count.
`--list` lists the checks; `--part K/8` runs one of eight independent parts,
as used by continuous integration. Without `--part`, all eight run.

## What the ordinary check establishes

1. The first implementation regenerates all normalized symmetric rows,
   checks its cosine table by interval arithmetic, and reconstructs the
   class census and compressed-unit table. `cover_check.py`, written
   separately from `units.py`, derives compressed vectors from row masks and
   exhaustively checks that every admissible tuple has a representative.
   `check_receipts.py` checks all receipts against regenerated class sizes
   and its own kernel-multiplier census.
2. The second implementation, in `checker2/`, independently regenerates
   rows using certified integer cosine coefficients, enumerates the exact
   compressed cover, and checks every receipt. Its source shares no
   implementation with the first checker. The two generated row files are
   compared byte for byte when both parts run together.
   This part also runs the production search on order-65 unit 5200 with
   keys truncated to 32 bits. `collision_check.py` independently regenerates
   its filtered pairs with the NumPy implementation, counts equal keys by
   sorting, and checks each matched quadruple exactly. It requires equal
   nonzero key-match counts, equal list sizes and survivor counts, and zero
   exact solutions. A modified expected match count must be rejected.
   Only the mathematical key definition and its fixed constants are shared
   with the production search. Truncation tests the join; the production
   exhaustion uses full 64-bit keys.
3. Both checkers must reject corrupted copies: deleted and duplicated
   receipts, incorrect list sizes or pair counts, nonproduction hash
   settings, a removed covering unit, and a false solution. The first also
   rejects a missing batch, incorrect classes, and an unreported solution;
   the second also rejects a removed row mask. Both exhaustive cover
   enumerators are rerun with a planted gap.
4. At odd orders 3 through 33, an independently structured baseline search
   regenerates the published equivalence-class counts and computes symmetry
   closures. It uses only rowsum grouping through order 23, and additionally
   the conservative row spectral filter at orders 25 through 33. Order 1 is
   checked directly: row negation normalizes its unique class to four ones.
5. Stored control solutions at orders 39, 45, and 55 are checked by exact
   integer matrix multiplication and their complete symmetry closures.
   These are witness checks, not rediscovery at order 55. The next control
   freshly rediscovers the classes at orders 39 and 45 without receiving
   these solutions as search inputs; their stored closures are used only
   afterward for comparison.
6. All ten search variants at orders 9 and 15 agree with an unfiltered
   baseline. The variants remove individual reductions, remove sorting
   and orbit selection together, keep compression alone, weaken hash keys,
   and apply a constrained-capacity setting. These small ordinary controls
   need not exercise the restart path. The option named `--cap 64` has an
   effective initial capacity of 1,024; it is not a literal 64-entry buffer.

The published counts are from Table 1 of Holzmann, Kharaghani, and
Tayfeh-Rezaie, *Williamson matrices up to order 59*, Designs, Codes and
Cryptography 46 (2008), 343–352,
[doi:10.1007/s10623-007-9163-5](https://doi.org/10.1007/s10623-007-9163-5).
For orders 3, 5, …, 33 they are respectively
1, 1, 2, 3, 1, 4, 4, 4, 6, 7, 1, 10, 6, 1, 2, 5.
The odd-order equivalences are independent row negation, row permutation,
and a common invertible multiplier of the cyclic coordinates.

## Longer reproduction

```sh
python3 checks/check.py --full-controls --work controls-output
python3 checks/check.py --full-search --threads 2 --work search-output
```

The first command also rediscovers order 55 with compression factor 5,
tests the ten reduction variants at order 27 with compression factor 9,
and uses the unfiltered baseline at every odd order through 33. The order-27
constrained-capacity variant exercises repeated passes. The order-55
search previously took about 1.5 CPU-hours. To run the discovery checks
alone, including order 55, use `--part 8/8 --full-controls`.
The second command repeats the complete order-65 search, regenerating its
inputs and receipts. The recorded search took about 271 CPU-hours; wall
time depends on the processor and available cores. Keep at least 16 GB of
memory available for the two-thread full search, with additional memory per concurrent
search unit depending on its surviving pair lists. Reduce `--threads` if
memory is limited. No data download is required for either command.

The full search can also be divided into disjoint intervals after building
and regenerating its inputs with the entry point. The executable command is
`WORK/src/search 65 5 WORK/data WORK/data/units.tsv BEGIN END OUTPUT --threads N --batch 64`.
Intervals are half-open subsets of `[0,70699)`; their union must be that
entire interval. Completed batch files permit resumption with the same
command. Merge their batch files without overwriting duplicates and
concatenate `solutions.tsv`, then run both receipt checkers. The exact
standalone commands are those in `check.py`: `check_receipts.py` takes
order, compression factor, regenerated data directory, units file, and
receipt directory; `checker2/verify.py` takes the independently generated
classes, units, results, and receipt directories. A partial interval is
not evidence of complete exhaustion.

`unit_recheck.py` supplies a separately written NumPy implementation of the
per-unit pair filtering and join. It is an optional, more costly diagnostic
with its command-line usage in the source. It does not use the product
theorem. Receipt accounting does not replace this kind of re-execution.

## Scope and trust

The complete cover contains 423,527 sorted compressed tuples in 70,699
multiplier orbits. There are 396,050,997 retained rows in 15,251 classes.
The 70,699 receipts record 70,830,746,132,488 enumerated pairs,
1,645,891,558,124 survivors, zero matching keys, and zero solutions.
Every recorded search unit used one pass.

These are computer-checked coverage and accounting facts. The decisive
additional dependence is the correctness of the exhaustive search execution:
the receipt checkers cannot reconstruct every filtering, insertion, and
probing operation from its totals. The result is an exhaustion record
supported by separately written implementations and controls, not a short
proof certificate or a formally verified program. The paper gives the
mathematical reductions and floating-point error bounds. In particular,
the lower spectral enclosure after clamping at zero is at most the true
scaled squared eigenvalue; the stronger negative-offset bound applies only
before clamping.

Per-class digests commit to the mathematical row sets and are checked after
independent regeneration. They are part of the row-census comparison, not a
file-inventory verification wrapper. The programs, compiler, runtime,
interval-arithmetic implementation, and recorded execution remain in the
trust base. See [the data description](../data/README.md) for the certificate
formats and the optional full dataset.
