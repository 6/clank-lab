# Checking the computed premises

The Lean theorem `EKG3.conj3_of_computations` (see
[`../lean/README.md`](../lean/README.md)) has four premises, which are
computed rather than proved in Lean. This folder holds the programs that
establish them and one entry point that runs them.

Requirements: Python 3.10 or later, GNU g++ (C++20) and gcc, and
`pip install -r checks/requirements.txt` (python-flint, for Arb ball
arithmetic). Run from the result's folder, with a new work directory
outside it:

```sh
python3 checks/check.py quick --work /tmp/ekg-bounds-quick   # a few minutes
python3 checks/check.py full  --work /tmp/ekg-bounds-full    # about three hours
python3 checks/check.py cover --work /tmp/ekg-bounds-cover   # seconds: the certificate only
```

`full` runs everything `quick` does first. Its two long runs need about
72 GB (`ekg_gen`) and 33 GB (`ekgv`, which also writes tens of GB of
paging files to the work directory); `--program gen` or `--program ekgv`
runs one of them, so they can be run on different machines. The compilers
can be changed with `CXX`, `CC` and `CXXFLAGS` (default `-O3`).

## The programs

| File | Role |
|---|---|
| `ekg_gen.cpp` | generates $a(1..N)$ by the pointer rule with a smallest-prime-factor table and one pointer per prime; checks the bounds with exact integers; reports equalities, the frontier $E$ and early-even count $K$, thresholds, and a checkpoint every $10^8$ terms |
| `ekgv.cpp` | a second generator, written independently from the definition: segmented factorization with a cache, a paged store of per-prime cursors, a paged bitmap of used values, and a different formula for $K$; same reports |
| `ekg_check.cpp` | checks a generated prefix directly against the definition, using neither pointers nor factorization: $a(1)=1$, $a(2)=2$, values distinct, $\gcd(a(n),a(n-1))>1$, and every smaller multiple of each prime factor of $a(n-1)$ appears before index $n$; recomputes the bounds and thresholds |
| `fnvcheck.c` | FNV-1a 64-bit hash of a prefix file, compared with a recorded checkpoint |
| `cover_check.py` | checks the middle-range certificate against `CoverChain` and `CoverRow.Conditions` in `../lean/Statement/TheoremTP3.lean` and `../lean/Statement/PiBoundsP3.lean` |

The recorded results are in `../data/prefix-checkpoints.txt`: the bound
violations (none), the equality cases, seven frontier thresholds, and 160
checkpoints $(n, a(n), E, K, \max K, \text{hash})$ at multiples of
$10^8$ up to $1.6 \times 10^{10}$. Both generators produced exactly these
lines.

## What each mode establishes

`quick`:

1. The certificate `../data/cover-p3-13328000000.csv.xz` is accepted:
   every row condition is proved with Arb balls at 256 bits (upper end of
   the left side below the lower end of the right side), with exact
   integers and rationals where Lean has them; the rows abut, start at
   $e_0 = 13{,}328{,}000{,}000$ with $M \ge 329$, have nondecreasing $M$, and
   end beyond $10^{205}$. Seven corrupted copies are rejected: a gap, a
   decreased $M$, $Q$ above its bound, $b_q = 5$, $h_c = 14$, a moved
   start and a short end. This is the premise `CertifiedCoverP3`.
2. Both generators and the direct checker, run to $N = 10^8$, agree with
   the recorded checkpoint, the threshold $E \ge 10^8$ and the equality
   cases, and report no violations. Swapping two adjacent terms, or raising
   one term by 2, at $n = 54{,}321{,}988$ is rejected both by the hash and
   by the direct checker.
3. Every value plotted in the figure (`../data/figure-data.csv`) is a term
   of the generated sequence.

`full` then runs both generators to $L = 1.6 \times 10^{10}$ and compares
every line with `../data/prefix-checkpoints.txt`. The premises follow:

- `FiniteFa`: no violations up to $L$, and the only equalities are
  $a(7) = 12$ (upper) and $a(28) = 13$ (lower); $n = 1, 2$ are checked by
  hand.
- `FiniteFbP3`: $E$ first reaches $1.413 \times 10^{10}$ at
  $n = 13{,}928{,}388{,}828 \le L - 2$. Since $E$ is nondecreasing,
  $E(L-2) \ge 1.413 \times 10^{10} > e_0$.
- `FiniteFcP3`: the largest $K$ at states with $E < 1.413 \times 10^{10}$
  is 329. Every state with $E < e_0$ comes before the first state with
  $E \ge 1.413 \times 10^{10}$, so the bound holds at all such states, not
  only those up to $L$.

## How the programs match the Lean definitions

This correspondence was checked by reading the code; it is part of the
trusted base.

- Both generators use the pointer rule: $a(n)$ is the minimum, over the
  primes $q$ dividing $a(n-1)$, of the least unused multiple of $q$. This
  is the definition, because a number sharing a factor with $a(n-1)$ is a
  multiple of one of those primes. Pointers only move past used multiples.
  `ekg_gen` caps values at $\lfloor 12N/7 \rfloor + 2$: a term above the
  cap would itself violate the upper bound and stop the run, which never
  happened. `ekgv` has no cap.
- States: both programs update $E$ and $K$ right after placing $a(n)$, so
  their state $n$ is Lean's archive state `u = n - 1`.
  `frontier canonical u` is the least positive even number not among
  `actualA 0 .. actualA u`, and `earlyEvenCount canonical u` counts the
  used even numbers above it. `ekg_gen` keeps $K$ by incrementing it for
  each even term placed above $E$ and decrementing it for each used even
  number $E$ passes; `ekgv` computes it as the number of used evens minus
  $E/2 - 1$.
- `ekg_gen`'s `first_t_E_ge X` and `ekgv`'s `first_n` are the first state
  with $E \ge X$; `maxK_E_below` and `maxK_below` are the largest $K$ over
  the earlier states.
- Values are 64-bit; the bound comparisons $28a(n)$ against $13n$ and
  $7a(n)$ against $12n$ use 128-bit products.

FNV-1a is not collision resistant. Here it compares two independent honest
computations; agreement at 160 checkpoints, each hashing the whole prefix,
makes an accidental match negligible. The direct checker covers the first
$10^8$ terms (its arrays for the full prefix would exceed one machine), so
beyond that the definition is checked only through the two generators,
which could in principle share a misreading of it.

## Supplementary notes

The [checking notes relocated from the paper](checking-notes.tex)
retain the implementation details, precise resource estimates, theorem
identifiers and certificate margins. Their references use the labels in
`paper/paper.tex`; the notes are documentation and are not read by a
proof or checker.
