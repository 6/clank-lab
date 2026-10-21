# Certificate checkers

Run from the folder above this one, with Python 3.10 or later and no
third-party packages (see [requirements.txt](requirements.txt)):

```sh
python3 checks/check.py
```

It takes a few seconds and ends with a `PASS` line; any failure prints
`FAIL` and exits nonzero. Both checkers must accept both witnesses and the
weak-form certificate, and must reject the agreeing control, the two
weak-form controls and each corrupted certificate with the reason it was
built to trigger. A crash or a rejection for another reason fails the
check. A third checker then recomputes every case with $n \leq 5$, which shows
that the counterexample is the smallest.

## The statement checked

For a partition $\lambda$ of $n$, the integral Specht module $S^\lambda$ is the $\mathbb{Z}$-span of the
polytabloids $e_T$ in the tabloid module (row tabloids), where $T$ runs over all
$n!$ fillings of the diagram of $\lambda$. The Jucys–Murphy element is
$X_k = (1\,k) + (2\,k) + \cdots + (k{-}1\,k)$. Stanley's Conjecture 7.4 predicts the
Smith normal form of $X_k$ on $S^\lambda$: with $f = f^\lambda$ standard Young tableaux and
$S_r$ the set of cells $(i, j)$ that $k$ occupies in at least $r$ of them, the
invariant factor is

$$\alpha_{f-r+1} = \Bigl\lvert \prod_{(i,j) \in S_r} (j - i) \Bigr\rvert .$$

Both checkers recompute this list from $\lambda$ and $k$ alone.

The eigenvalues of $X_k$ on $S^\lambda$ are the contents $j - i$ of the cell
$(i, j)$ holding $k$, one for each standard Young tableau, with multiplicity.
Stanley also remarks that every invariant factor should be a product of some
of these eigenvalues. A certificate with `"weak_form": true` claims that this
weaker statement fails too: some invariant factor is not, up to sign, the
product of any sub-multiset of the eigenvalues (the empty product being $1$).

## The certificate format

Each file in `data/` is one JSON object:

- `n`, `lambda`, `k`: the case;
- `basis`: the standard Young tableaux of shape $\lambda$, each a list of rows, in
  the order used for the basis $e_T$;
- `A`: the $f \times f$ integer matrix of $X_k$ in that basis, column $j$ holding the
  coordinates of $X_k e_{T_j}$;
- `U`, `V`: $f \times f$ integer matrices with determinant $\pm 1$ such that
  $UAV$ is the diagonal matrix with entries `snf`;
- `snf`: the Smith normal form, a nonnegative divisibility chain with zeros
  last;
- `predicted`: Stanley's list for this case;
- `weak_form` (optional): `true` when the certificate also claims that the
  weaker statement fails;
- `claim`, `convention`, `positions_of_k`: descriptive fields, not read by
  the checkers (`positions_of_k` counts the standard tableaux in which $k$
  occupies each cell).

The witnesses are `witness-311-k3.json` ($\lambda = (3,1,1)$, $k = 3$, the smallest
counterexample: Smith form $(1,1,1,1,2,2)$ against the prediction
$(1,1,1,1,1,4)$) and `witness-52-k7.json` ($\lambda = (5,2)$, $k = 7$: Smith form
$(1,1,1,1,2,4,4,4,4,0,0,0,0,0)$ against $(1,1,1,1,1,4,4,4,4,0,0,0,0,0)$).

`weak-52-k7.json` holds the same data as `witness-52-k7.json`, with
`"weak_form": true` and its own `claim`. For $\lambda = (5,2)$, $k = 7$ the
entry $7$ sits in cell $(1,5)$ or $(2,2)$, so the eigenvalues are $4$, with
multiplicity $9$, and $0$, with multiplicity $5$. Every product of some of
them is $1$, $0$ or a power of $4$, while the Smith form contains a $2$.

## Checker A: `check_snf.py`

Works from the definitions, with exact rational arithmetic:

1. enumerates the standard Young tableaux from all $n!$ fillings and checks
   that `basis` is exactly that set;
2. checks that the standard polytabloids are linearly independent and that
   every one of the $n!$ polytabloids is an integer combination of them, so
   they form a $\mathbb{Z}$-basis of $S^\lambda$;
3. recomputes $X_k e_T$ for each basis tableau and checks it equals column $j$
   of `A`;
4. checks that `A`, `U` and `V` are $f \times f$ integer matrices, that
   $UAV$ is the diagonal matrix with entries `snf`, that $\det U$ and $\det V$ are $\pm 1$, and that `snf` is a
   divisibility chain, so `snf` is the Smith normal form of $X_k$ on $S^\lambda$;
5. recomputes Stanley's list, checks it equals `predicted`, and requires it
   to differ from `snf`.

For a certificate with `"weak_form": true` it also, before checking the
columns of `A`:

6. takes the contents of the cells holding $k$ in the standard tableaux as
   the eigenvalue list and checks, with exact integer matrix products, that
   $\prod_c (A - cI) = 0$ over the distinct contents $c$, so $A$ is
   diagonalizable with every eigenvalue among them, and that
   $\operatorname{tr}(A^j)$ equals the $j$-th power sum of the list for
   $1 \leq j < d$, where $d$ is the number of distinct contents. These $d$
   power sums (with $j = 0$ giving $f$) determine the multiplicities, since
   the Vandermonde matrix of distinct values is invertible;

and, after checking the Smith form,

7. builds every product of a sub-multiset of the eigenvalues and requires
   some entry of `snf` to be none of them in absolute value.

## Checker B: `check_mod2.py`

Written separately, with different enumeration and arithmetic:

1. enumerates the standard Young tableaux by Yamanouchi (lattice) words;
2. shows that the span over $\mathbb{F}_2$ of all $n!$ polytabloids, inside the tabloid
   module over $\mathbb{F}_2$, has dimension $f$. Since $S^\lambda$ is free of rank $f$ (the
   standard basis theorem, which checker A confirms for these inputs),
   $S^\lambda / 2S^\lambda$ embeds in the tabloid module over $\mathbb{F}_2$;
3. computes the rank of $X_k$ on that span, which needs no choice of basis.
   It equals the number of odd invariant factors of $X_k$ on $S^\lambda$;
4. compares that rank with the number of odd entries of Stanley's list,
   recomputed from the Yamanouchi words, and requires them to differ;
5. checks `basis`, `A`, `U`, `V` and `snf` with its own code: $X_k e_T$
   equals the combination given by `A` exactly over $\mathbb{Z}$, $UAV$ is the diagonal matrix with entries `snf`,
   determinants are $\pm 1$ by Bareiss elimination, a divisibility chain, and as many
   odd entries in `snf` as the rank found in step 3.
6. for a certificate with `"weak_form": true`, reads the contents from the
   Yamanouchi words, applies the factors $A - cI$ for the distinct contents
   $c$ in turn to every unit vector and requires $0$, and compares the
   traces of $A, A^2, \ldots, A^{d-1}$, computed one column at a time, with
   the power sums of the contents; then it runs over all exponent vectors
   $0 \leq e_c \leq m_c$, with $m_c$ the multiplicity of $c$, and requires
   some entry of `snf` to differ from every $\lvert \prod_c c^{e_c} \rvert$.

For $\lambda = (3,1,1)$, $k = 3$, $X_3$ has rank $4$ over $\mathbb{F}_2$, while the predicted list
$(1,1,1,1,1,4)$ has five odd entries. This part alone already refutes the
conjecture for the integral Specht module.

## Checker C: `check_small.py`

Written separately from checkers A and B, importing neither, and reading no
file from `data/`. It shows that $\lambda = (3,1,1)$, $k = 3$ is a smallest
counterexample. For every partition $\lambda$ of $n \leq 5$ and every $1 \leq k \leq n$ it:

1. builds the polytabloids of all $n!$ fillings in the row-tabloid module;
2. proves that the standard polytabloids form a $\mathbb{Z}$-basis of their span: the
   square matrix of the coefficients of the tabloids $\lbrace T \rbrace$, for $T$ standard,
   in the standard polytabloids has determinant $\pm 1$, and every one of the $n!$
   polytabloids is rebuilt exactly from the integer coordinates that matrix
   gives;
3. forms the matrix of $X_k$ in that basis;
4. computes its Smith form from determinantal divisors: $d_j$ is the gcd of
   all $j \times j$ minors, computed as exact integer determinants, and the $j$-th
   invariant factor is $d_j / d_{j-1}$;
5. recomputes Stanley's list, with the empty product equal to $1$.

It requires that all 34 cases with $n \leq 4$ agree with the conjecture, and
that exactly 2 of the 35 cases with $n = 5$ disagree, both for $\lambda = (3,1,1)$:
$k = 3$, with Smith form $(1,1,1,1,2,2)$ against $(1,1,1,1,1,4)$, and $k = 5$, with
$(1,1,2,2,4,4)$ against $(1,1,1,4,4,4)$. It also requires that Stanley's worked
example $\lambda = (5,1)$, $k = 5$ gives $(1,1,3,3,12)$, as predicted. It runs in under a
second, and its checks don't depend on Python's assertions, so `-O` doesn't
skip them.

## Control and corruptions

`data/control-51-k5.json` is Stanley's own worked example, $\lambda = (5,1)$, $k = 5$,
where the Smith form $(1,1,3,3,12)$ agrees with the prediction. It is a valid
certificate, and both checkers reject it as showing no discrepancy, so they
do not accept a case merely because its certificate is well formed.

Two weak-form controls in `data/corrupt/` are valid certificates of true
statements marked with `"weak_form": true`, and both checkers must reject
the weak-form claim:

- `weak-control.json` is the $(5,1)$, $k = 5$ control. The eigenvalues are
  $4$, $3$ and $-1$, and $(1,1,3,3,12)$ consists of products of them
  ($12 = 4 \cdot 3$);
- `weak-control-311-k3.json` is the smallest witness. It does refute the
  conjecture, but its entry $2$ is a product of eigenvalues ($2 = 2 \cdot 1$),
  so it does not refute the weaker statement.

The other files in `data/corrupt/` each change one thing in a witness:

| File | Change | Rejected because |
|---|---|---|
| `A-entry.json` | one entry of $A$ changed | a column of $A$ is not $X_k e_T$ |
| `snf-claims-prediction.json` | `snf` replaced by the prediction | $UAV$ is not the diagonal matrix of `snf` |
| `U-not-unimodular.json` | $U$ made non-unimodular, `snf` adjusted to match | $\det U \neq \pm 1$ |
| `U-rational.json` | one row of $U$ doubled and another halved, `snf` adjusted | $U$ is not an integer matrix |
| `snf-extra-zero.json` | an extra factor $0$ appended | `snf` does not have $f$ entries |
| `basis-nonstandard.json` | a non-standard tableau in the basis | the basis is not the standard tableaux |
| `prediction-altered.json` | the recorded prediction changed | it differs from the recomputed one |
| `weak-eigen-wrong.json` | in the weak-form certificate, row 1 of $A$ replaced by row 1 plus row 3 and $U$ adjusted, so $UAV$ still equals the diagonal matrix of `snf` | $A(A - 4I) \neq 0$, so $A$ has an eigenvalue that is not a content |

`check.py` lists the exact rejection message it expects from each checker.

## What the checks do not cover

The checkers establish the Smith form on the integral Specht module with
its standard polytabloid basis, the lattice Grinberg specified. That the
same Smith form holds on every lattice stable under the permutations of
$1, 2, 3$, and that the conjecture fails at $k = 3$ for every shape with at
least three rows and three columns, are written arguments in the paper,
not checked by these programs. The Lean project in `../lean/` checks the
computation on the $6 \times 6$ matrix of the smallest witness and some steps of
those written arguments; [its documentation](../lean/README.md) says which.

## Optional census programs

[`census/`](census/README.md) holds the programs that computed the Smith
forms for every $\lambda$ with $n \leq 8$ and every $k$ (`data/census-n8.json`) and
compared other readings of the conjecture. They need third-party packages,
are not part of the check, and the certificates do not depend on them.
