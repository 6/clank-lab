# Definitions and the source conjecture

The definitions follow John Goldwasser, Xinmao Wang and Yaokun Wu,
*Minimum light numbers in the sigma-game and lit-only sigma-game on
unicyclic and grid graphs*, Electronic Journal of Combinatorics 18 (2011),
P214, [printed pages 1–5](https://doi.org/10.37236/701).

| Source definition | Lean definition | Correspondence |
| --- | --- | --- |
| Finite undirected graph, with loops permitted (pp. 1–2) | `Graph n`, `Undirected` | A Boolean adjacency matrix on `Fin n`, with symmetry required separately; diagonal entries are allowed. |
| Connected graph (Conjecture 5, p. 5) | `Connected` | Every pair of vertices is joined by a finite adjacency path, including the empty path. |
| Binary configuration and light number (p. 2) | `Configuration n`, `lightNumber` | A Boolean function on vertices, with `true` meaning ON; the number of ON vertices is a finite-set cardinality. |
| Ordinary move adds the neighborhood indicator over the binary field (pp. 2–3) | `regularMove` | Exactly the neighboring bits are toggled; the played vertex changes exactly when it has a loop. |
| Lit-only move multiplies that indicator by the played bit (p. 3) | `litOnlyMove` | The ordinary toggle at an ON vertex, and the identity otherwise. |
| Attainability by successive moves (p. 3) | `Reachable` | Reflexive transitive closure of one-step moves, allowing every finite sequence and the empty sequence. |
| Minimum attainable light numbers (p. 3) | `minimumLight`, `regularMinimum`, `litOnlyMinimum` | The natural-number infimum of attained weights; `minimumLight_attained` proves that it is attained because the start is reachable. |
| Maximum of paired differences (p. 4) | `discrepancy` | The finite maximum of lit-only minimum minus ordinary minimum, using the same starting configuration in each pair. |
| Complete multipartite graph (p. 4) | `CompleteMultipartite G m` | A surjection onto `Fin m` gives nonempty parts; adjacency holds exactly between unequal parts, excluding loops. |
| Conjecture 5 (p. 5) | `Conjecture5 G` | An undirected connected graph satisfying `n < 2 * discrepancy G` must be complete multipartite with a positive number of parts congruent to 3 modulo 4. |

The source's phase-space arcs omit moves that change nothing. The theorem
`reachable_iff_changing_steps` proves that omitting identity steps leaves
reachability unchanged. The theorem `regularMinimum_le_litOnlyMinimum`
proves that the ordinary minimum never exceeds the lit-only minimum, so
natural-number subtraction gives the source's nonnegative difference.
The strict doubled threshold is exactly $D(G)>n/2$, without rounding.
The source uses more than one part; the positive congruence condition
in `Conjecture5` forces at least three.

The definitions `rows`, `graph`, `decode` and `start` encode this paper's
witness: rows `[92,120,113,99,71,78,63]` and starting code 27, with vertex 0
as the least significant bit. Theorems `graph_is_cycle_complement` and
`start_lights` identify the graph and configuration with the paper's
description. `closedCodes` and `InCertificate` describe the ten-state
closed set; `corruptCodes` removes state 45 for the negative control.
`CounterexampleStatement` combines connectedness, symmetry, the same-start
minima 0 and 4, failure of every complete multipartition and the negation
of `Conjecture5 graph`. The proof establishes a graph-wide gap of at least
four, without asserting equality or minimality of the example.
