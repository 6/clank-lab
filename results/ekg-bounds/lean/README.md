# The Lean proof

A standard Lake project, pinned by `lean-toolchain` (Lean 4.34.0) and
`lake-manifest.json` (mathlib). With [elan](https://github.com/leanprover/elan#installation)
installed:

```sh
lake exe cache get
lake build
```

`lake build` builds the default target `Check`, and with it every module
the proof depends on. It takes about an hour on two cores, with up to about
7.5 GB of memory per Lean process.

## The statement

`Statement/TheoremT.lean` defines the conclusion:

```lean
def Conj3Statement : Prop := ∀ i : ℕ,
  (13*(i+1) ≤ 28*EKG.actualA i ∧ 7*EKG.actualA i ≤ 12*(i+1)) ∧
  (13*(i+1) = 28*EKG.actualA i ↔ i+1 = 28) ∧
  (7*EKG.actualA i = 12*(i+1) ↔ i+1 = 7)
```

The sequence is zero-based: `EKG.actualA i` is the paper's $a(i+1)$, with
`actualA 0 = 1`, `actualA 1 = 2`, and then the least positive integer not
yet used that shares a prime factor with the previous term
(`vendor/EKG/Basic.lean`, `vendor/EKG/Canonical.lean`). `EKG.canonical`
packages it with proofs of exactly that specification (the structure
`GreedySeq`: seeds, injectivity, a shared prime with the previous term, and
minimality). `FirstTerms.lean` checks its first thirty terms against
OEIS A064413, including `a(7) = 12` and `a(28) = 13`.

The main theorem, in `EKG3/AssemblyComputations.lean`, is

```lean
theorem EKG3.conj3_of_computations :
  FiniteFa → FiniteFbP3 → FiniteFcP3 → CertifiedCoverP3 → Conj3Statement
```

Its premises are computed facts about the actual sequence, with no free
parameter (`Statement/TheoremT.lean`, `Statement/TheoremTP3.lean`). The
archive state `u` (entries `0..u` placed) is the paper's state $t = u+1$;
`EKG.frontier canonical u` is $E(u+1)$ and `EKG.earlyEvenCount canonical u`
is $K(u+1)$.

- `FiniteFa`: for every `i+1 ≤ L = 16000000000`, both bounds and both
  equality characterizations.
- `FiniteFbP3`: `13328000000 ≤ frontier canonical (L-3)`, the paper's
  $E(L-2) \ge e_0$.
- `FiniteFcP3`: every state `u` with `frontier canonical u < 13328000000`
  has `earlyEvenCount canonical u ≤ 329`.
- `CertifiedCoverP3`: there is a list of integer rows `CoverChain e0 Kfin`
  starting at `e0 = 13328000000` with `M ≥ 329`, each row satisfying
  `CoverRow.Conditions`, consecutive rows abutting, `M` nondecreasing, and
  the last endpoint at least `10^205`.

These are checked by the programs in [`../checks/`](../checks/README.md);
the certificate for the last one is `../data/cover-p3-13328000000.csv.xz`.
Two comments in `Statement/` name the directories where the programs and
the certificate were first written; their files here are in `../checks/`
and `../data/`. `Statement/TheoremT.lean` also defines an earlier variant
of the premises (with constants `2239000000` and `182`, and published
prime-counting bounds as hypotheses); `conj3_of_computations` does not use
it, apart from `Conj3Statement` and `FiniteFa`.

## What `lake build` checks

`Check.lean` fails the build unless:

- `EKG3.conj3_of_computations` has exactly the type above, and
  `Conj3Statement` unfolds to the displayed formula;
- the prime-counting bounds (`EKG3.piBoundsP3_holds`) and the arithmetic
  large sieve (`EKG3.arithmeticLargeSieve_holds`) are proved;
- `a(7) = 12` and `a(28) = 13` for `EKG.actualA`;
- each audited theorem depends only on `propext`, `Classical.choice` and
  `Quot.sound` (`#guard_msgs in #print axioms ...`): the main theorem, the
  middle-range Theorem T (`EKG3.P3.theoremT`), the far-range Lemma F
  (`EKG3.P3.lemmaF`), Lemmas A, C and D, the bootstrap
  (`EKG3.boundedCorollaryA`), the prime-counting bounds, the large-sieve
  Brun–Titchmarsh bound (`EKG3.largeSieveBT`), `G(Q) > log(Q+1) + 1.07`
  (`EKG3.G_gt_log_add_107`) and the first-terms checks.

## Layout

| Path | Contents |
|---|---|
| `Statement/` | definitions of the statement, the premises and the lemmas |
| `EKG3/` | the proofs: Lemmas A, C, D, the bootstrap, Theorem T, Lemma F, the prime-counting bounds, the large-sieve inequalities and the assembly |
| `vendor/EKG/` | the EKG sequence foundation (Haver's archive with the earlier second-order result's additions) |
| `vendor/OAI/` | the arithmetic large sieve, from OpenAI's mathematics formalizations |
| `vendor/IEANTN/` | Rosser–Schoenfeld's Theorem 12 and Chebyshev's lower bound, from IEANTN and LeanCert |
| `FirstTerms.lean`, `Check.lean` | the unit tests and the statement and axiom checks |

Where each vendored file comes from and what was changed is in
[`../THIRD_PARTY.md`](../THIRD_PARTY.md). The finite certificate behind
`G(Q) > log(Q+1) + 1.07` for `6 ≤ Q < 1440` is split into eighteen modules
(`EKG3/SieveWeightFiniteChunk*.lean`) so that no Lean process needs more
than a few GB.
