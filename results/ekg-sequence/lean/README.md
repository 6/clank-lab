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

`Check.lean` checks the proof against that statement and uses `#guard_msgs`
to require the exact `#print axioms` output for each of seven theorem roots:
`ekg_sharp_all_index`, `ekg_pnt_compatibility`, `ekg_part_a`, `ekg_part_b`,
`ekg_exact_counting`, `ekg_weak_pnt`, and `ekg_endpoint_control`. Each uses
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
