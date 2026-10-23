# Lean proof

From this directory, with [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get
lake build
```

`lean-toolchain` selects Lean 4.32.2. `lake-manifest.json` fixes Mathlib v4.32.2
at commit `905b95818eb32af7874a58b427f50c1711a5e96c` and fixes its transitive
dependencies. Lake downloads the dependencies; they are not bundled here.
The certificate checks can use several gigabytes per parallel Lean process.
For a machine with limited memory, set `LEAN_NUM_THREADS=1` before building.

`CubelikeSC.endpoint_sc` in `CubelikeSC/Proof.lean` proves the entire upper
bound from the definitions: for every connection set in
$(\mathbb{Z}/2\mathbb{Z})^7$ excluding zero, every set of pairwise strongly
cospectral vertices has at most four elements. No connectivity assumption is
made. `CubelikeSC/Statement.lean` defines the adjacency matrix and strong
cospectrality using orthogonal projections onto its eigenspaces. The endpoint
type is:

```lean
def EndpointSC : Prop :=
  ∀ S : Finset V, (0 : V) ∉ S → ∀ P : Finset V,
    (∀ u ∈ P, ∀ v ∈ P, StronglyCospectral S u v) → P.card ≤ 4
```

The proof first bounds the character-defined subgroup `K S`.
`CubelikeSC/R1.lean` proves the direction needed to transfer that bound to
strongly cospectral sets. The spectral identities, frame construction, bracket
extraction, and weak-duality argument are all formalized. The finite step uses
3,984 exact certificates: each is checked with `decide +kernel`, and separate
kernel computations prove that all 127,488 cases are covered. The certificate
data are included as Lean definitions; building does not execute Python or
trust a solver.

The default build includes `CubelikeSC/Checks.lean`. It checks the exact
`EndpointSC` type, its expanded quantifiers, and guarded axiom reports for
`endpoint_sc`, `endpoint`, `main`, and `lemmaF`. These reports allow exactly
`propext`, `Classical.choice`, and `Quot.sound`. Five kernel controls check
that an intact weight vector and an intact cover pass, that zeroed and halved
weight vectors fail, and that deleting an entry leaves a case uncovered.
The proof uses no `native_decide` and has no `sorry` dependency.

The converse character criterion and the construction attaining four vertices
are outside the Lean formalization. The independent exact Python checks in
[checks/README.md](../checks/README.md) verify the connected attaining example
directly from its adjacency matrix. Thus the upper bound is fully formalized;
the sharpness assertion also uses the supplied exact computation and the
published construction.

For an optional second kernel pass after building, Lean's standard
`leanchecker` accepts module names, for example:

```sh
lake env leanchecker CubelikeSC.Proof CubelikeSC.Checks
```

To replay every module in this project, including every certificate check:

```sh
find CubelikeSC -name '*.lean' | sed 's/\.lean$//; s#/#.#g' | sort | xargs -n 1 lake env leanchecker
lake env leanchecker CubelikeSC
```
