#!/bin/sh
# Check that G1 and G2 (data/graphs.g6) have Colin de Verdiere invariant at
# least 6 and no minor in the 78-graph Heawood family, with two independent
# sets of checkers, and that corrupted certificates are rejected. Run from the
# result's folder: sh checks/check.sh. Needs the packages in
# checks/requirements.txt. About 25 CPU-seconds and under 250 MB.
set -eu
cd "$(dirname "$0")/.."
PY=${PYTHON:-python3}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT HUP INT TERM

# The Heawood family, regenerated from K7 and K3,3,1,1.
"$PY" -I checks/family.py "$tmp/heawood.json" | tee "$tmp/family.out"
grep -q '^78 ' "$tmp/family.out"

# Minor search: planted controls must be found, then G1 and G2 must have none.
"$PY" -I checks/minor_exclusion.py data/minor-controls.g6 "$tmp/heawood.json" | tee "$tmp/controls.out"
[ "$(grep -c '"target_minors_found": \[\]' "$tmp/controls.out" || true)" = 0 ]
"$PY" -I checks/minor_exclusion.py data/graphs.g6 "$tmp/heawood.json" | tee "$tmp/minors.out"
[ "$(grep -c '"target_minors_found": \[\]' "$tmp/minors.out")" = 2 ]
# Lemma 7's census keeps graphs with at least 21 edges: 354 classes for G1, 455 for G2.
grep -q '"graph": "G1".*"minors_enumerated": 354,' "$tmp/minors.out"
grep -q '"graph": "G2".*"minors_enumerated": 455,' "$tmp/minors.out"

# The corank-6 certificates, and corruptions they must reject.
"$PY" -I checks/check_cert.py data/G1-cert.json
"$PY" -I checks/check_cert.py data/G2-cert.json
"$PY" -I checks/corruptions.py "$tmp"
"$PY" -I -c "
import json
g = dict(l.split() for l in open('data/graphs.g6'))
for k in g:
    assert json.load(open('data/%s-cert.json' % k))['graph6'] == g[k], k
print('certificates match data/graphs.g6')"

# The independent checkers.
"$PY" -I checks/checker_a.py data/G1-cert.json data/G2-cert.json
"$PY" -I checks/checker_a.py --corrupt data/G1-cert.json data/G2-cert.json > "$tmp/ca.out"
tail -1 "$tmp/ca.out"; grep -q '^CORRUPTION SUITE: PASS$' "$tmp/ca.out"
"$PY" -I checks/checker_b.py family > "$tmp/cb-family.out"
head -1 "$tmp/cb-family.out"; grep -q '^family size 78 by edges {21: 20, 22: 58}' "$tmp/cb-family.out"
"$PY" -I checks/checker_b.py minors > "$tmp/cb-minors.out"
tail -4 "$tmp/cb-minors.out"; [ "$(grep -c '^RESULT G[12]: NO Heawood-family minor$' "$tmp/cb-minors.out")" = 2 ]

# Apex structure: the non-2-apex minors, and 3-apex.
"$PY" -I checks/apex_minors.py data/graphs.g6 | tee "$tmp/apex.out"
"$PY" -I -c "
import json, sys
import networkx as nx
g6 = dict(l.split() for l in open('data/graphs.g6'))
G = {k: nx.from_graph6_bytes(v.encode()) for k, v in g6.items()}
H = G['G1'].copy(); H.remove_edge(1, 10)
f = lambda d: nx.from_graph6_bytes(d['graph6'].encode())
rows = [json.loads(l) for l in open(sys.argv[1])]
assert sorted(r['graph'] for r in rows) == ['G1', 'G2'], rows
for r in rows:
    allm, mins = r['non_2apex_minors'], r['minimal_non_2apex_minors']
    assert len(allm) == 2, r['graph']
    a, b = (f(d) for d in allm)
    assert (nx.is_isomorphic(a, G[r['graph']]) and nx.is_isomorphic(b, H)) or (nx.is_isomorphic(b, G[r['graph']]) and nx.is_isomorphic(a, H)), r['graph']
    assert len(mins) == 1 and nx.is_isomorphic(f(mins[0]), H), r['graph']
print('non-2-apex minors: G1 and G2 each have exactly two, themselves and G1 - {1,10}')
mindeg = lambda X: min(d for _, d in X.degree())
assert H.number_of_edges() == 22 and mindeg(G['G1']) == 4 and mindeg(G['G2']) == 3
for k, X in G.items():
    assert X.number_of_edges() == 23, k
    for e in X.edges():
        D = X.copy(); D.remove_edge(*e)
        assert mindeg(D) >= 2 and mindeg(nx.contracted_edge(X, e, self_loops=False)) >= 2, (k, e)
print('Lemma 8: G1 and G2 have 23 edges and minimum degrees 4 and 3, H has 22 edges, and one edge deletion or contraction leaves minimum degree at least 2')" "$tmp/apex.out"
[ "$(grep -c '"three_apex": true' "$tmp/apex.out")" = 2 ]

# Figure 1 of the paper is drawn from data/graphs.g6.
"$PY" -I checks/figure.py --check data/graphs.g6 paper/paper.tex
echo "PASS: mu(G1) >= 6 and mu(G2) >= 6, and neither has a Heawood-family minor;"
echo "each has exactly one proper non-2-apex minor up to isomorphism (H = G1 - {1,10}), so G1 or H is an excluded minor for mu <= 5 outside the family;"
echo "G1 and G2 are 3-apex, so with the cited bounds mu(G1) = mu(G2) = 6"
