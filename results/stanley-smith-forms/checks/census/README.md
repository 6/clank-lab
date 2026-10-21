# Optional census programs

These programs are optional. They are not part of the check, and the
certificates and the checkers in `checks/` do not use them. They computed
the Smith form of $X_k$ on $S^\lambda$ for every partition $\lambda$ of $n \leq 8$ and every $k$,
and compared other readings of the conjecture. They need Python 3.10 or
later with [python-flint](https://pypi.org/project/python-flint/), and
`std_check.py` and `analyze2.py` also need
[SymPy](https://pypi.org/project/sympy/):

```sh
python3 -m pip install python-flint sympy
```

Run the commands below from the folder holding `checks/` and `data/`,
writing outputs outside it. The programs write nothing into this folder.

- `specht_lattice.py N OUT.json [--sat]` builds $S^\lambda$ inside the tabloid
  module over $\mathbb{Z}$ as the span of one polytabloid under the simple
  transpositions, with Hermite normal forms (no standard basis, no
  straightening), expresses $X_k$ in that basis and computes its Smith form
  twice (FLINT and a separate pure-Python routine, which must agree). With
  `--sat` it also uses the saturated lattice, the rational span of $S^\lambda$
  intersected with the integral tabloid module. This reproduces
  `data/census-n8.json` byte for byte in about a minute:

  ```sh
  python3 checks/census/specht_lattice.py 8 /tmp/census-n8.json
  cmp /tmp/census-n8.json data/census-n8.json
  python3 checks/census/specht_lattice.py 6 /tmp/census-sat-n6.json --sat
  ```

  Each record gives `n`, `lam`, `k`, the `lattice`, `f`, the Smith form
  `snf`, Stanley's predicted list `pred`, and `ok` (whether they agree).
- `std_check.py` recomputes cases through the standard polytabloid basis,
  with an exact rational solve and SymPy's Smith normal form, and compares
  them with the census:

  ```sh
  cd checks/census
  python3 -B -c "import std_check; std_check.compare_all('../../data/census-n8.json', 6)"
  ```

- `group_ring.py N` tests the literal reading of the survey's definition:
  the Smith form of $X_k$ acting on the group ring $\mathbb{Z}[S_n]$, against the Smith
  form of the block-diagonal matrix holding $f^\lambda$ copies of each predicted
  list. That reading already fails at $n = 4$, $k = 4$:

  ```sh
  python3 checks/census/group_ring.py 5
  ```

- `analyze.py` and `analyze2.py` summarize the census: disagreements per $n$,
  the symmetry between $\lambda$ and its conjugate, rank and determinant checks,
  the weaker statement that every invariant factor is a product of
  eigenvalues, and the primes at which the disagreements occur:

  ```sh
  python3 checks/census/analyze.py data/census-n8.json
  python3 checks/census/analyze2.py data/census-n8.json
  ```

- `variants.py [NMAX] [--cache PATH]` tests corrected readings of the
  formula against the Specht lattice for every $\lambda$ with $n$ up to `NMAX` (at least 6,
  default 8):
  other indexings of the invariant factors, other definitions of the cell
  sets $S_r$, the Smith form of the diagonal of eigenvalues, products with
  zero contents dropped, other ranges of $k$ ($X_{k \pm 1}$ and
  $Y_k = \sum_{i>k} (i\,k)$), the conjugate shape, counts of partial fillings,
  and the weaker statement that every invariant factor is a product of
  eigenvalues. It builds each lattice with `specht_lattice.py`, forms every
  $X_k$ and $Y_k$ from the matrices of the simple transpositions, checks the
  Smith forms of $X_k$ against `data/census-n8.json`, and prints one table row
  per reading: the cases that match for $n \leq 7$ and $n \leq 8$, whether it gives
  Stanley's $\lambda = (5,1)$, $k = 5$ example, and the first failure. This reproduces the
  table in the paper's "Corrected readings" section in about a minute for
  $n \leq 8$. With `--cache`, the Smith forms are stored in `PATH` and reused on
  the next run; without it nothing is written.

  ```sh
  python3 checks/census/variants.py 8
  ```
