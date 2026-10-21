# Completion record

The full check was completed on October 21, 2026, from a clean copy of the
sources, with nothing reused from earlier builds.

## Final theorem

```lean
theorem R3_P10_eq_18 : ramsey3Path 10 = 18
```

It was proved by `lake build R3P10Final` (`lean/R3P10Final.lean`), together
with `K18_has_mono_P10`, the statement that every 3-coloring of the edges of
$K_{18}$ has a monochromatic path on 10 vertices.

## Coverage

All 15,956 of 15,956 cubes of the final list were re-solved and checked in
Lean, in 162 modules covering the indices 0 to 15,955 with no gap or
duplicate. The seven smaller cases and the cover were checked in Lean too.
Each regenerated proof and clause log matched the earlier run byte for byte.

## Axioms

The exact `#print axioms` output (line wrapping normalized):

```text
'R3P10.K18_has_mono_P10' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
'R3P10.R3_P10_eq_18' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
```

The lower bound `K17_no_mono_P10` uses only `propext`, `Classical.choice`
and `Quot.sound`. `Lean.ofReduceBool` and `Lean.trustCompiler` come from the
natively evaluated certificate checks.

## Toolchain

| Tool | Version |
| --- | --- |
| Lean | `leanprover/lean4:v4.32.2` |
| Mathlib | commit `905b95818eb32af7874a58b427f50c1711a5e96c` (tag `v4.32.2`) |
| CaDiCaL | commit `c60730422e758ef1cebe7aeddf2dda31c996bf04` |
| drat-trim | commit `2e3b2dc0ecf938addbd779d42877b6ed69d9a985` |
| cake_lpr | commit `a36874a8b750b43fe4b385b8ddbf5b033e46a3fa` |

## Cost

About 300 CPU-hours in all: re-solving the cubes took 229, converting their
proofs to LRAT 50, packing the certificates 5, and the Lean checks 18. The
work ran as six independent batches of 12 cores each; the longest took
7.5 hours.
