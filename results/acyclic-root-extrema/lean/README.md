# Formalization

The project pins Lean 4.32.0 and Mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997`. Lake's manifest pins all transitive dependencies. Run `lake exe cache get` and `lake build` in this directory. The default target includes every proof module and `Checks.lean`.

`Endpoint.lean` defines a graph from its missing unordered edges. Its `A` sums one monomial for each vertex subset whose induced graph satisfies Mathlib's `SimpleGraph.IsAcyclic`. Thus coefficients count induced forests, including the empty forest. `candidate` is the complement of a four-cycle and two three-leaf stars; `J n` is the complement of a four-cycle and the star on the remaining vertices.

`BBPSplitStar.endpoint` proves both coefficient identities, the existence of a real candidate root strictly between −100 and −86, the strict bound 86 for every complex root of the comparator, inequality of the two polynomials, and the negations of both universally quantified assertions. The real-root assertion distinguishes polynomials, as the source question does.

The counting proof checks all 4,096 vertex subsets of each graph using kernel reduction. The graph lemmas relate its finite decisions to induced-graph acyclicity. The analytic part uses the intermediate value theorem and the triangle inequality. `Checks.lean` checks the final type, small complement-edge examples, and guards the axiom output for the coefficient identities, analytic bounds and endpoint. Each depends only on `propext`, `Classical.choice` and `Quot.sound`; compiled-evaluation axioms are absent.

The proof took about six minutes with a peak near 9 GB for its largest module; allow at least 12 GB for the build. The imports order the four large counting modules so that Lake compiles them sequentially. An independent subset enumerator and a separate disjoint-set checker previously agreed on both polynomials and the four-vertex cycle example, whose polynomial is $1+4x+6x^2+4x^3$; altered inputs were rejected. Those checks are supplementary: the default Lake build proves the complete statement from the graph definitions without importing their outputs.
