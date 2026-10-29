# Lean checking guide

`lean-toolchain` pins Lean 4.19.0. `lakefile.lean` and `lake-manifest.json` pin mathlib to `c44e0c8ee63ca166450922a373c7409c5d26b00b` and pin its transitive dependencies. Install Lean with elan, then run from this directory:

```sh
python3 ../checks/bootstrap_kernel.py
lake exe cache get
LEAN_NUM_THREADS=6 lake build
```

This is the full proof build. It includes all 119 support modules, 570 finite source chunks, their 570 data blocks, final assembly, the exact endpoint type, seven published-definition bridges, and axiom guards in `Proof.lean`. Use at least 12 allocated CPUs and 88 GiB of memory. The configuration gives each Lean process two threads; the command gives Lake six scheduling threads. A clean portable replay of the exact generated proof sources completed in about nine hours elapsed, with a conservative charge of 54.2 CPU-hours and peak summed process memory of 43.9 GiB. The small control build is separate; the quick check does not substitute for the full theorem build.

The 1,148 generated SourceKernel and ControlKernel modules are omitted
from the committed bundle. Bootstrap reconstructs them from the supplied
inputs and certificates, using explicitly pinned generator recipes, then
checks every file's name, byte length and SHA-256 against the replayed
source manifest. It rejects changed inputs, recipes, manifests and existing
generated files. Generation and matching hashes connect the source bytes
to the replay; only the Lean build checks their proof terms.

`ADKZPricing` is the retained formal namespace. Its name has no mathematical significance. `Endpoint.lean` defines `ProposedEndpoint`, with real sign covectors, minimal nonzero cocircuits, composition-based adjacency, complementary 40-element zero sets, and walks over every signed cocircuit. `SourceKernelCompleteKernelAsync.lean` proves the unconditional `ADKZPricing.Generated.source_frozen_endpoint : ADKZPricing.ProposedEndpoint`. The graph's exact diameter is not asserted. `PublishedFaithfulness.lean` proves the seven bridges to literal support minimality, empty separation, at least 39 common zeros, and the bounded-walk definition. `Proof.lean` applies its endpoint transfer and requires the expected axiom output for the endpoint and all seven bridges: `propext`, `Classical.choice`, and `Quot.sound`.

For an allocated replay with resource guards and resumable progress, first obtain the mathlib cache, then from the bundle root run:

```sh
python3 checks/bounded_build.py --cpus 12 --workers 6 --cpu-hours 70 --work /tmp/cocircuit-build --checkpoint /tmp/cocircuit-results/build.json
```

The bounded driver requires Linux with cgroup v2. Its allowance is a cumulative upper bound, not an estimate or permission to spend it. Choose the allowance before starting. It charges the allocation's monotonic CPU counter, including completed descendants and any other work in the same accounting scope, and reserves CPU for shutdown. Resume with the same command and `--resume` in the same cgroup and boot session. The original counter is retained, so work after the last checkpoint and during an interruption remains charged. A legacy checkpoint or changed accounting scope is rejected before launch; it needs independently verified prior accounting before a new allowance can be assigned.

Keep the bundle's `.lake/build` directory outside any retained-checkpoint directory. Lake validates incremental dependency traces and rebuilds missing products; a checkpoint itself cannot authorize proof reuse. Ten-minute atomic checkpoints record source identities, observed completed object hashes, process-tree peak RSS, cumulative CPU time and logs. Compiler products stay outside the checkpoint directory. If compiler products are lost, Lake rebuilds them from sources.

The bounded driver authenticates and regenerates the finite sources before
forming its fresh or resumed source signature. It stops a Lean process
before ten minutes of uninterrupted work, and enforces process-count,
per-module RSS, assembly RSS, aggregate memory and CPU guards. If a module
reaches a guard, that invocation is incomplete; inspect the failure before
choosing a new checking allocation or module decomposition. The completed
portable replay's longest module took about 421 seconds.

`lake build ControlCheck` builds the bounded certificate only. `checks/FalseControl.lean` must fail when invoked with `lake env lean ../checks/FalseControl.lean`; its false equality is an intentional negative test outside the default build. The quick checking entrypoint runs both commands and checks their outcomes.

To regenerate the actual finite sources from the split certificate, follow [the checker guide](../checks/README.md). The optional `check_source_kernel.py` retains the explicit finite-module dispatcher, kernel axiom inspection and per-object resume checks. Its paths are supplied explicitly with `--generated`, `--mathlib`, `--build` and `--keep`; set `PROOF_CPUS`, `PROOF_SCRATCH` and `ADKZ_PROOF_BUILD` to the allocation, scratch directory and freshly built support-object directory. For long allocated work use the bounded Lake command above, whose ten-minute checkpoints include peak memory. The optional dispatcher alone does not provide the outer checkpoint policy.

The [formal statement and interpretation](FORMAL_STATEMENT.md) give the exact
endpoint, sign-vector conventions, definition bridges, logical principles
and the distinction between the formal and written constructions.
It identifies the standard oriented-matroid interpretation and the written
attaining upper bound separately from the lower-bound theorem in Lean.
