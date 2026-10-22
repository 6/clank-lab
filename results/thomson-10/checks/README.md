# Independent certificate check

Run `python3 -I checks/check.py` from the result folder with Python 3.10 or
later. The check uses only the standard library and finishes in seconds.
`python3 -I checks/check.py --list` lists its steps.

The interval $I$ is the exact height interval specified in the
[Lean guide](../lean/README.md). Its endpoints are inputs to the checker;
existence and uniqueness of a root inside it are proved by Lean.

The Python checker is an independent implementation of the arithmetic checks for the same rational three-point certificate used by Lean. It reconstructs the polynomial operators and factor-matrix products, checks all 274 residual coefficients and their total absolute error, and bounds the candidate energy over $I$. It also rejects eight deliberately corrupted certificates. It does not re-prove the global geometric classification or local uniqueness: those are Lean obligations. The detailed global and local argument is in the [Lean guide](../lean/README.md).

The separate rigorous enclosure is $32.716949460147 < E(p) < 32.716949460149$, giving $32.71694946\ldots$. [`energy_enclosure.py`](energy_enclosure.py) checks it only in Python, by rational interval arithmetic on all 45 pair distances over $I$, with outward integer-square-root bounds at precision $2^{-420}$. The existence and uniqueness of the height root are Lean facts; Python encloses the energy over the entire interval without solving that root. This enclosure is supplementary and is not part of the Lean theorem.

## Certificate sizes and finite classification

The three-point certificate has 20 nonzero matrix blocks, 42,950 factor entries and 274 residual coefficients; [`certificate.json.gz`](../data/certificate.json.gz) is 1,246,399 bytes (2,670,249 bytes expanded). The window classification checks 84 anchor records, of which 43 are eligible, and nine seven-clique witnesses, all yielding the same pattern. Its exact data occupy 14,992 bytes. These are certificate sizes and finite classification counts, not a discretization of the continuum of competitors.

The scalar, window-classification, and constrained-Hessian certificates are
exact data embedded in the corresponding Lean modules. Lake expands the
large compressed ambient certificate automatically before checking it.
