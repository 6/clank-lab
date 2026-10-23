# Exact certificate and attainment checks

From the result's top directory, with Python 3.10 or later:

```sh
python3 checks/check.py
```

Only the Python standard library is used; `requirements.txt` is empty.
This entry point checks the finite certificates, their transcription into
Lean, six corrupted certificates, and the connected graph attaining four
pairwise strongly cospectral vertices. It also checks that the optional
illustration reproduces the graph. The Lean proof is checked separately
with the ordinary Lake commands in [lean/README.md](../lean/README.md).

`check_cert.py` is an independent exact checker. For every triple $(n,B,t)$
in the finite bracket problem, it builds all allowed brackets directly from
the case's own coset data, looks up the supplied weights, and evaluates the
weak-duality bound using unbounded Python integers. A sorted key finds the
weights; it does not replace the calculation for the original case. An
`EMPTY` entry is accepted only when some coset really has no allowed bracket.
Acceptance requires all 127,488 cases. The checker imports neither a search
program nor a certificate generator.

`data/d7k3.cert` contains 3,984 entries: 58 `EMPTY` entries and 3,926 weight
vectors. Its header specifies weights in units of $1/15000$ of a cost unit.
Each remaining line has the form:

```text
K n m mu1 r1 ... mu7 r7 ; EMPTY
K n m mu1 r1 ... mu7 r7 ; value:weight ...
```

The seven pairs are sorted coset means and residues; coset zero is determined
by $n$ and $m$. The single entry point compares these mathematical entries
with the committed Lean definitions. This comparison ignores comments and
source formatting. It then verifies that the independent checker rejects a
deleted entry, a false `EMPTY`, halved weights, zeroed weights, a negative
weight, and a duplicated entry. The default Lean build supplies a separate
kernel proof of the finite step and its own weight and cover controls.

`attainment.py` specializes Árnadóttir and Godsil's published construction
for odd dimension to dimension seven. It checks that the connection set has
20 elements and spans the seven-dimensional vertex group. It computes
$K=\lbrace 0,7,120,127\rbrace$ from the character criterion and independently obtains the
same strongly cospectral class from the adjacency matrix using `spectral.py`.
The latter finds every eigenvalue by exact rank computations and forms the
spectral projection polynomials with integer arithmetic. The sum of the
eigenspace dimensions must equal 128. It also rejects two incorrect class
claims, one missing a vertex and one adding a vertex.

The optional transcription program regenerates the Lean certificate modules
in a new directory without performing a search or invoking a solver:

```sh
python3 checks/transcribe.py data/d7k3.cert /tmp/cubelike-transcription
```

The optional illustration is separate from the proof checks. To check its
reproduction from the same published connection set:

```sh
python3 checks/figure.py --check
```
