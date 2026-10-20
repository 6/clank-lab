# Checking the EKG theorem

Install [elan](https://github.com/leanprover/elan#installation), which selects
and installs the Lean version pinned by `lean-toolchain`. From this directory:

```sh
lake exe cache get
lake build
```

The first command obtains mathlib's compiled cache. Lake resolves the
public dependencies at the revisions in `lake-manifest.json`; the build
then checks `Check.lean` and all the proofs it imports. Python is not needed.

`Statement.lean` independently fixes the theorem: with the EKG sequence
starting 1, 2, replace p and 3p by 2p for odd primes p, leaving other values
unchanged, to obtain b(n). For every real epsilon > 0, some natural N >= 3
satisfies, for every natural n >= N,

```text
|b(n) - n - n/(3*Real.log(n))| <= epsilon*(n/Real.log(n)).
```

`CorollaryStatements.lean` independently fixes the paper's consequences of
that theorem, for the one-based sequence `a` (A064413):

- `EventualSignStatement`: for all large n, a(n) < n if a(n) is prime and
  a(n) > n if not (Ordowski's first conjecture on A064413);
- `OrdowskiDensityStatement`: #{1 <= k <= N : k < a(k)} / N tends to 1
  (his second conjecture). The paper's sharper form,
  #{k <= N : a(k) > k} = N - (1/2 + o(1)) N/log N, follows from the next
  statement and the finiteness of {k : a(k) = k} but is not a separate
  Lean theorem;
- `BelowDiagonalCountStatement`: #{1 <= k <= N : a(k) < k} divided by
  N/(2 log N) tends to 1;
- `JasinskiFinitenessStatement`: each of {k > 0 : 2a(k) = k},
  {k > 0 : a(k) = k} and {k > 0 : 2a(k) = 3k} is finite (A152458, A152519);
- `ExceptionalFinitenessStatement`: {n > 0 : a(n) not prime, a(n) <= n - 1}
  and {k > 0 : a(k + 1) = k} (A064420) are finite;
- `A155549FinitenessStatement`: A155549, the set of values a(n) over that
  first index set, is finite;
- `ShortCyclesStatement`: for each L, finitely many orbits
  {m, a(m), a(a(m)), ...} of positive m with a^[l](m) = m for some
  1 <= l <= L.

Their proofs are `SolutionSign.lean`, `SolutionDensity.lean` and
`SolutionCycles.lean`.

`Check.lean` checks each proof against its statement and uses `#guard_msgs`
to require the exact `#print axioms` output for each of fourteen theorem roots:
`ekg_sharp_all_index`, `ekg_pnt_compatibility`, `ekg_part_a`, `ekg_part_b`,
`ekg_exact_counting`, `ekg_weak_pnt`, `ekg_endpoint_control`,
`ekg_eventual_sign`, `ekg_ordowski_density`, `ekg_below_diagonal_count`,
`ekg_jasinski_finite`, `ekg_exceptional_finite`, `ekg_a155549_finite`,
and `ekg_short_cycles_finite`. Each uses
only `propext`, `Classical.choice`, and `Quot.sound`; an added axiom or a
`sorry` on one of these proofs' dependency paths makes the build fail.
`ControlEndpoint.lean` also checks the initial sequence and smoothing:
values 2 and 6 stay fixed, unlike the convention of OEIS A256417.

Haver's estimates and the prime number theorem are imported proved theorems,
with no added mathematical hypotheses. The PNT sources contain unrelated
admitted declarations `prelim_decay_2`, `prelim_decay_3`, and `decay_alt`;
none belongs to the audited proofs' dependency paths. The build certifies
these theorem roots, not every declaration in the upstream project.
[Source attribution](../THIRD_PARTY.md) identifies Haver's files and
the PNT sources.

The numerical illustration in [data/](../data/README.md) is optional and is
not an assumption or certificate for the theorem.
