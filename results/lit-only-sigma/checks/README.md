# Certificate checks

Run from the result's directory with Python 3.10 or later:

```sh
python3 checks/check.py
```

Only Python's standard library is used. The input in
`data/certificate.json` contains the seven adjacency rows, the starting
configuration, the two regular moves and the ten-state closed set.
Bit $j$ of row $i$ records adjacency between vertices $i$ and $j$; bit $j$
of a configuration records whether vertex $j$ is lit.

`check_certificate.py` checks the graph, connectedness, the excluded
complete multipartite case, the regular path to zero and closure under all
lit-only moves. It uses integer bit operations.

`independent.py` represents configurations as sets of vertices and moves
as symmetric differences with neighbor sets. It independently checks the
graph description, its failure to be complete multipartite, the regular
path and the closed set. It also recomputes the regular and lit-only
reachable sets from the starting configuration. Both checkers accept the
certificate and reject `data/corrupt.json`, which omits state 45.

The entry point runs both checkers without optimization, checks their
answers, and confirms that the diagram and the paper's closure table
describe the same graph, start and transitions as the certificate. Every
valid transition from the ten-state set stays in it. All its states have
at least four lit vertices, and the start has exactly four; the regular
path reaches zero. Thus the checked bounds are $ML_G(27)=0$ and
$`ML_G^*(27)=4`$, giving $D(G)\geq4>7/2$.

Execution of these exact checks relies on the Python interpreter and its
execution platform.
