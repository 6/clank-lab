# Lean proof

The project uses Lean 4.19.0 and Mathlib revision
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. Install Lean through
[elan](https://github.com/leanprover/elan), then run in this directory:

```sh
lake exe cache get
lake build
```

The default build compiles every module below, including `Statement`,
`Examples` and `Axioms`. With the Mathlib cache it takes about two minutes of
wall time on two cores, with peak memory near 6 GB.

## Definitions

`Endpoint` represents an $m\times n$ zero-one matrix by the set of rows of
each column, `Fin n → Finset (Fin m)`. `matrixProb m n p E` is the finite sum,
over all matrices satisfying `E`, of the product over columns of
`columnMass m p`, the probability of a column's exact set under independent
Bernoulli($p$) entries. `G` is the length of `greedyTrace`, which repeatedly
takes the first column of maximum gain and stops when no rows remain or the
maximum gain is zero. `L` is the real infimum of $\sum_j x_j$ over
$0\le x_j\le1$ with every row covered at least once; it is the LP value
itself, not a bound. `SourceEndpoint` states Assumption 2 of Arpino, Dmitriev
and Grometto as printed, for the sequence $m(n)=\lfloor n^{1/10}\rfloor$,
$p(n)=n^{-2/5}/10$, and convergence in probability of the ratio for an
arbitrary assignment of values on infeasible matrices. `UniformEndpoint`
defines uniform tie-breaking as a recursive kernel averaging, at each step,
over the columns of maximum positive gain, and the joint probability
`jointProb` of matrix and choices.

## Main theorems

- `GreedyLPHittingSet.leftmost_explicit` (in `Statement`): Theorem 1 of the
  paper, with $c$ = `Uniform.c` $=1/(196608\cdot10^9)$, gap $c/8$, probability
  $c/4$ and threshold $10^{20}$.
- `ADG.full_frozen_endpoint` (in `FullConstruction`): the probability
  theorem with existential constants, Assumption 2 for the sequence above,
  the identities $m(k^{10})=k$ and $p(k^{10})=1/(10k^4)$, $m(n)p(n)\to0$, and
  failure of convergence in probability for every assignment on infeasible
  matrices.
- `ADG.Uniform.uniform_probability_endpoint` and
  `ADG.Uniform.full_uniform_endpoint` (in `UniformConstruction`): the same for
  uniform tie-breaking, with gap $c/8$ and probability $c/8$.

## Modules

- `Probability`, `PathProbability`, `QuantitativeProbability`: normalization
  of the finite law, the exact probability of a fixed isolated path, and the
  numerical estimates.
- `Greedy`: the phase structure of leftmost greedy when columns have at most
  three rows and every two-row column is present.
- `PathDefinitions`, `GreedyPaths`, `DeterministicExchange`,
  `DeterministicGap`: isolated paths, selection of their middles, the
  simultaneous exchange and the resulting gap.
- `PathCounting`, `ExpectationConstruction`, `ExpectationTail`,
  `BadMiddleBound`: the eightfold count, the expected number of paths, the
  global bound on their number and the tail estimate.
- `LP`, `SourceTransport`, `SourceConsequence`, `FullConstruction`: LP facts,
  the source assumptions and the leftmost theorem.
- `ConflictCoupling`, `PermutationScan`, `UniformKernel`, `UniformPhase`,
  `OrderedPhase`, `UniformCount`, `UniformInvariance`, `UniformTransport`,
  `UniformGoodLaw`, `UniformConstruction`: uniform choices with conflicts
  equal a scan in uniformly random order, the identification of both greedy
  rules with such scans, invariance under column permutations, and the
  uniform theorem.

`Statement` restates the theorems with the constants and definitions
unfolded. `Examples` checks small matrices: one isolated path followed by
every two-row column, where greedy and the exchange both use three columns,
and two paths, where greedy uses six columns and a five-column cover gives
$L\le5$; and leftmost tie-breaking. `Axioms` makes the build fail if a main
theorem depends on anything beyond `propext`, `Classical.choice` and
`Quot.sound`.

The kernel checks the formal statements; their correspondence with the
published conjecture is explained in the paper. No `sorry`, added axiom or
compiled evaluation is used.
