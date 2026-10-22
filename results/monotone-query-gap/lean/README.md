# Lean proof

Run these commands in this directory, with [elan](https://github.com/leanprover/elan)
installed:

```sh
lake exe cache get
lake build
```

The pinned toolchain is installed by elan. Mathlib is a Lake dependency to
provide its standard cache executable; the proof itself imports only Lean
core and uses no Mathlib theorem. The build checks `KS24.lean`, the exact
endpoint types in `Statement.lean`, the small definition checks in
`Examples.lean`, and the axiom guards in `Axioms.lean`.

The function is
$f(x)=x_1x_2x_3\lor x_0x_4(x_1\lor x_2\lor x_3)$.
Points are integers from 0 through 31, with coordinate $i$ given by bit $i$.
All costs below are summed over the 32 equally likely inputs. Divide by
32 to obtain expectations at fair coins.

`KS24.answer` proves that this function is monotone, every correct adaptive
algorithm has total query cost at least 104, one such algorithm has total
cost 104, and an explicit monochromatic subcube partition has total
codimension 102. `KS24.gap` proves that the partition's total codimension is
strictly smaller than every correct algorithm's total cost. Thus Lean proves
$a(f,\pi_{1/2})=13/4$ and $sc(f,\pi_{1/2})\le 51/16<13/4$.
The reverse inequality for $sc$, and hence its exact value, is proved by the
linear-programming dual certificate in [the exact checkers](../checks/README.md).

## Definitions and the source question

The meanings follow Section 2 of Laurin Köhler-Schindler and Jeffrey E.
Steif's [paper](https://arxiv.org/abs/2408.12995). `Alg` is a finite adaptive
binary decision tree. `Determined m x` means that the value of $f$ is fixed
by the queried bits in mask $m$. `cost` stops counting as soon as this holds,
and `Correct` forbids a leaf before it holds. Repeated queries are permitted
and counted. A source algorithm truncated when $f$ is determined gives such
a tree; a tree can be completed by querying any remaining bits without
changing the cost counted here. The source algorithms are deterministic.

A cell `(m, v)` contains the points `y < 32` satisfying `y &&& m = v`.
`IsPartition` requires every point to occur in exactly one cell, and
`Determines` says that $f$ is constant on each cell. `codim` counts only the
five input coordinates. Empty cells or high mask bits do not enlarge the
class of partitions: delete empty cells and mask bits above coordinate 4
to obtain ordinary subcubes with the same codimension at every point.

The guards require the endpoint theorems to use exactly `propext` and
`Quot.sound`. The finite computations use `decide +kernel`, not native
evaluation. The trusted base is Lean's kernel together with the stated
identification of the definitions with the source question. No claim is
made here about biased coins or the smallest possible number of inputs.
