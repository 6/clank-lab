# Exact certificate checks

The proofs, the certificate checkers and the text were produced by AI models
(from OpenAI and Anthropic), working under the author's direction.

The supplied polynomial and monomial certificate data and the locally
reconstructed transformation matrix establish the finite identities used in
the [paper](../paper/paper.pdf). The computation is over
$\mathbf F_{1009}$; the paper proves the reduction to characteristic zero
and applies the prior results for the other reflection groups.

## Running the checks

Requirements are Python 3.11 or later, SymPy, a C++17 compiler with OpenMP,
FLINT 3.x and GMP development libraries, Singular 4.x, and GNU time at
`/usr/bin/time`. For Debian or Ubuntu, install the native requirements with:

```sh
sudo apt-get install g++ libflint-dev libgmp-dev singular time
```

From this result's directory, install the Python requirement and run:

```sh
python3 -m pip install -r checks/requirements.txt
python3 checks/verify.py --workers 2
```

Set `--workers` to the number of CPU cores available for this check. Allow
about ten minutes with two cores and several gigabytes of temporary space.
The command reconstructs the large transformation matrix in a fresh temporary
directory using the supplied Singular recipe, compiles the C++ checker, and
runs every check. It downloads nothing. Reconstruction invokes `liftstd`;
acceptance independently checks every resulting identity and uses no basis
search. Temporary files are removed after success or
failure. To retain arithmetic batches, receipts and logs, add `--work DIR`,
where `DIR` does not yet exist. To reuse an existing full `certificate.txt`,
add `--certificate-from CERTIFICATE_DIR`; this skips reconstruction entirely.
Only its transformation records are used, together with the polynomial and
monomial data supplied in this package. Run Python normally, without `-O`.

`--list` prints the checks. `--part K/N` selects one of up to eight parts
for CI; all parts together run the same obligations as the full command.
For example, `--list --part 1/8` shows the first part. Independent steps are
assigned by estimated arithmetic cost; a dependent step repeats its prerequisite
when run alone. Each part needs its own fresh temporary directory.

## Certificate format

`data/polynomials.txt.gz` supplies the polynomial certificate's header and
all six input and 534 basis polynomials. `data/unit-order.txt`,
`data/unit-initial.txt` and `data/unit-starts.txt` supply the order, leading
exponents and monomial chains. The six modular inputs also appear separately
in `data/inputs/` so each arithmetic checker binds them independently.

`checks/generate.py` is the deterministic reconstruction recipe for the large
transformation matrix: it writes a Singular script that uses `liftstd` on
those inputs and exports the nonzero matrix entries. The entry point runs
this recipe in a separate temporary directory, combines its transformation
records with the supplied polynomial data, and gives that certificate to the
two independent arithmetic checkers. The supplied basis, order, initial
exponents and chain starts are preserved. The producer is not imported by
either arithmetic checker, and its output is accepted only through the full
coefficientwise and finite-cover checks below.

The polynomial stream begins with `CFG_POLY_V1`, followed by
`1009 6 6 534`: the prime, variable count, input count and basis count.
The variables are `a,b,c,d,y,z`, with weights `3,4,6,9,1,1`.
Records have the forms:

```text
I i polynomial
G j polynomial
T i j polynomial
```

The six `I` records are bound coefficient by coefficient to the six polynomials
in `data/inputs/`. The 534 `G` records and nonzero `T` records certify
`G[j] = sum(I[i]*T[i,j])`. The transformation records are grouped by increasing
column `j`; omitted entries are zero. Coefficients are interpreted modulo
1009. The order file declares positive weighted degree followed by reverse
lexicographic order, with `z` last. Leading exponents are supplied in the
initial file and independently recomputed from every `G`. The starts file
supplies candidates for the complete chains of standard monomials in `z`.

The first arithmetic checker constructs an additional `CFG_PAIRS_V1` record.
It covers all 142,311 unordered pairs exactly once: 1,690 product pairs,
138,012 chain pairs with earlier dependencies, and 2,609 direct reductions.
The second implementation checks this cover and its acyclic dependencies,
then recomputes the direct arithmetic. This extra polynomial-basis equality
check is stronger than the leading-ideal inclusion used by the paper.

## What the entry point checks

- `check_groups.py` constructs the 756 Eisenstein-integer vectors, verifies
  every reflection image exactly, and computes the group and subgroup orders
  by faithful permutation actions. It also checks the fixed vector,
  inclusions, and a nonzero spanning determinant.
- `check_symbolic_inputs.py` identifies all coefficients of the six input
  polynomials of degrees 6,12,18,24,30,42 with the orbit sums after substitution.
  It exhausts all 729 residue characters and rejects coefficient corruptions.
- `check.cpp` uses FLINT/GMP to verify every transformation identity and
  independently implements sparse polynomial reduction and the complete
  product/chain/direct pair argument. The positive weights and maximum
  reduction degrees are checked before using packed exponents.
- `check_second.py` has a separate polynomial parser and drives Singular's
  exact multiplication and reduction. It imports neither the C++ checker nor
  a certificate producer, and calls no `std` or `liftstd` basis search.
- `check_chains.py` and `check_monomials_independent.py` independently exhaust
  the standard monomials. The first reconstructs the complete starts by
  breadth-first traversal; the second uses a constrained depth-first traversal
  without reading the starts. Both verify the Hilbert functions of all 81
  quotients in every degree, including finite support.
- `rank_chain.py` and `rank_dfs.py` independently recompute the explicit
  quotient table, with the strict convention `exponent(z) < k`.
- `corrupt.py` and `audit_mutations.py` require both arithmetic implementations
  to reject altered input, basis and transformation coefficients, a false
  declared leading term, an omitted pure-power generator, and a zero weight.
  Both cover implementations reject an altered initial ideal; both rank
  implementations reject the quotient for `k=2` substituted at `k=1`.

The complete cover consists of 60,480 standard monomials in 1,440 chains.
The pure-power bounds are `(2,3,3,4,68,82)`. All quotient coefficients are
checked for `k=1,...,81` and degrees `0,...,108`, with no unexamined tail.

## Trusted boundary

These are distinct implementations of exact finite calculations. Execution
trusts Python and its integer arithmetic and parsers, SymPy's permutation-group
algorithms, the C++ compiler and OpenMP, FLINT/GMP, Singular arithmetic, gzip
decoding, and the operating system. The reconstruction recipe is supplied with the package, but is outside the
acceptance boundary: its transformations must satisfy every checked identity. The corruption tests exercise
specified error paths; they do not constitute a proof of checker correctness.

The paper's characteristic-zero argument remains written mathematics: the
integral invariant presentation, specialization inequality, generation of the
invariant ring, averaging and free-module argument, Hilbert-function squeeze,
and application of the free-extension theorem. Classification names,
invariant degrees and the earlier strong Lefschetz theorems are cited
literature premises. In particular, the computation here does not reprove
Wachi's result for the G33 coinvariant algebra. There is no Lean proof of the
whole theorem in this package.
