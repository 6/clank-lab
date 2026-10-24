# Checking the strategy certificates

The two original certificates prove that Alice wins the ordinary coloring game on
the displayed graph with five colors, and Bob wins its greedy threshold
game with the same palette. Both games start with Alice, alternate turns,
allow any uncolored vertex to be chosen, and have no passes. A third
certificate gives Alice a greedy strategy using at most six colors.
The clique and degree facts in the paper give the matching local bounds.

From the result's top-level directory, run:

```sh
python3 -I checks/verify.py
```

Python 3.10 or later and its standard library are sufficient. No package
installation, network access, graph generator, or game search is needed.
The command binds all three certificates to the exact edge list in
`data/graph.json`, checks all three with two separately written implementations,
checks their state, arc, and terminal counts, and requires the 28 original semantic
corruption rejections and 16 rejections for the six-color certificate to be rejected. It also regenerates both graph
drawings in memory and compares them with the supplied SVG and TikZ files.
It reports `PASS conclusion: chi_g(G) = 5 and Gamma_g(G) = 6` only after every
obligation succeeds. The check normally takes less than a minute.

## Certificate format

The files `data/ordinary-k5.json.gz`, `data/greedy-k5.json.gz` and
`data/greedy-k6.json.gz` contain
UTF-8 JSON compressed with gzip. Each has these fields:

| Field | Meaning |
| --- | --- |
| `version` | Format version, equal to 1. |
| `n`, `edges` | Number of vertices and a list of distinct edges `[u,v]` with `0 <= u < v < n`. |
| `k` | Palette `{1,...,k}`, equal to `{1,...,5}` or `{1,...,6}` here. |
| `game` | `ordinary` or `greedy`. |
| `first` | First player, `Alice` here. |
| `winner` | Claimed winner, `Alice` for ordinary and greedy-six, `Bob` for greedy-five. |
| `ordered` | Whether only the least-index uncolored vertex may be selected; `false` here. |
| `nodes` | A map from literal states to lists of moves `[vertex,color]`. |

A state key consists of exactly 11 comma-separated integers. Zero means
uncolored, and positive integers through the stated palette size are the colors. Thus the root key is
`0,0,0,0,0,0,0,0,0,0,0`. Every state is a proper partial coloring of the
graph. States are literal labeled colorings: no graph automorphisms, color
identifications, or other symmetry reductions are used by the checkers.

## Game rules and proof obligations

For each uncolored vertex, the checkers compute the colors absent from its
neighbors. An ordinary move can use any of these colors. A greedy move
must use the least one. Every move colors exactly one previously uncolored
vertex, and a move never changes an earlier color.

A fully colored state is an Alice win. In a five-color game, a state with
an uncolored vertex having neighbors of all five colors is a Bob win. Such a block is
irreversible, so stopping as soon as it occurs preserves the outcome of
the ordinary game. In the unrestricted greedy game, that vertex must
eventually receive color 6 or higher. Until a block occurs, the greedy
threshold game agrees with the unrestricted greedy game.

At each nonterminal state where the claimed winner moves, the certificate
lists exactly one legal move. At a state where the other player moves, it
lists every legal move exactly once. Each listed successor must appear in
the certificate. Terminal states have no moves, and their recomputed
winner must equal the claimed winner. Every supplied state must be
reachable from the all-zero root.

These local obligations imply the root outcome by induction on the number
of uncolored vertices. The terminal case has its checked outcome. At the
winner's turn, the selected move leads to a winning state by induction;
at the opponent's turn, every possible legal move does. Because every arc
reduces the number of uncolored vertices, this induction has no cycles.

Alice's ordinary strategy directly proves $\chi_g(G)\leq 5$, without any
assumption about monotonicity in the palette size. Bob's greedy strategy
forces an irreversible block, hence a color exceeding 5 in every greedy
continuation; it proves $\Gamma_g(G)>5$. These conclusions answer only the
first part of Havet and Zhu's question. They do not decide whether the gap
can be arbitrarily large, and they assert no minimality. The clique lower bound and greedy-six upper
bound strengthen the same example to the two exact values.

## Checkers and controls

`check.py` and `check_independent.py` each generate the legal moves from
the graph and state. Neither imports the other or a search implementation.
The second also checks the exact JSON field set, canonical state keys,
duplicate JSON keys, and nonstandard numeric constants. The entry command
loads all three inputs using that stricter JSON parser before applying either
checker. The accepted strategy sizes are:

| Game | Winner | States | Arcs | Terminal states |
| --- | --- | ---: | ---: | ---: |
| Ordinary | Alice | 108,669 | 216,995 | 2,800 |
| Greedy, five colors | Bob | 5,594 | 6,730 | 2,010 |
| Greedy, six colors | Alice | 2,223 | 3,339 | 208 |

These are sizes of the supplied strategy directed acyclic graphs, not of
the full game trees. `verify.py` checks all report fields and counts.

Seven corruptions are applied to each original five-color certificate in memory and submitted
directly to both checkers: omit an opponent reply; flip the claimed
winner; replace an Alice move by the illegal move `[0,0]`; add the edge
`[0,1]`; switch the first player to Bob; declare the root a terminal; and
add a move to a terminal. Thus the controls require 28 rejections. The
entry command checks both the exception class and the expected semantic
reason, so a parser failure or unrelated runtime error does not count as
a successful rejection. No file-integrity check can substitute for these
semantic controls.

The six-color strategy colors vertex 10 first and vertex 9 on Alice's
next turn if Bob has not already colored it; later Alice choices use the
smallest uncolored label. Every Bob reply is included, and all leaves are
full eleven-vertex colorings. Both checkers reject eight mutations: a
missing Bob reply, an Alice pass, a nonleast greedy color, ordered play,
Bob starting, an unfinished leaf, threshold five, and a missing successor.
The rejection class and semantic reason are checked. `exact_values.py`
also checks all ten edges of the clique on vertices 1, 4, 6, 9, 10, and the
degree bound outside vertices 9 and 10. It rejects a deleted clique edge,
a raised low-vertex degree, and a cyclic shift of the labels. The paper
explains why these facts give the matching bounds for the same games.

## Drawings and reproduction

The SVG displayed in the README and the TikZ picture in the paper have the
same vertex positions and are generated from `data/graph.json`. To
regenerate them after an intentional change to the graph or layout, run:

```sh
python3 -I checks/figure.py --write
```

Running `python3 -I checks/figure.py` compares the drawings without changing
them. This comparison is also part of the main verification command.

The full verification can be reproduced by copying this result's folder
to an otherwise empty directory and running its command there. All proof
inputs are resolved relative to that folder. The two
checkers can also inspect an individually decompressed JSON certificate:

```sh
gzip -dc data/ordinary-k5.json.gz > ordinary.json
python3 -I checks/check.py ordinary.json
python3 -I checks/check_independent.py ordinary.json
```

The compressed certificates are sufficient proof inputs. Reconstructing
the discovery search is unnecessary and is not part of verification.

## Trust boundaries

The computational argument trusts the Python interpreter and standard
library, the two checker implementations, and the correspondence of the
stated rules to the two graph games. Independent implementations and
semantic controls reduce shared implementation risk; they are not a
formal proof in a proof assistant. The short induction and the reduction
from greedy blocking to a color greater than 5 are written arguments in
the paper. The drawing comparison checks the supplied figure sources;
rendering them additionally trusts the SVG and LaTeX renderers.
