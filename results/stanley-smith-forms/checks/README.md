# Certificate checkers

Run from the folder above this one, with Python 3.10 or later and no
third-party packages (see [requirements.txt](requirements.txt)):

```sh
python3 checks/check.py
```

It takes a few seconds and ends with a `PASS` line; any failure prints
`FAIL` and exits nonzero. Both checkers must accept both witnesses, and must
reject the agreeing control and each corrupted certificate with the reason
it was built to trigger. A crash or a rejection for another reason fails the
check. A third checker then recomputes every case with n ≤ 5, which shows
that the counterexample is the smallest.

## The statement checked

For a partition λ of n, the integral Specht module S^λ is the Z-span of the
polytabloids e_T in the tabloid module (row tabloids), where T runs over all
n! fillings of the diagram of λ. The Jucys–Murphy element is
X_k = (1 k) + (2 k) + … + (k−1 k). Stanley's Conjecture 7.4 predicts the
Smith normal form of X_k on S^λ: with f = f^λ standard Young tableaux and
S_r the set of cells (i, j) that k occupies in at least r of them, the
invariant factor α_{f−r+1} is |∏_{(i,j)∈S_r} (j − i)|. Both checkers
recompute this list from λ and k alone.

## The certificate format

Each file in `data/` is one JSON object:

- `n`, `lambda`, `k`: the case;
- `basis`: the standard Young tableaux of shape λ, each a list of rows, in
  the order used for the basis e_T;
- `A`: the f × f integer matrix of X_k in that basis, column j holding the
  coordinates of X_k e_{T_j};
- `U`, `V`: f × f integer matrices with determinant ±1 and
  U·A·V = diag(`snf`);
- `snf`: the Smith normal form, a nonnegative divisibility chain with zeros
  last;
- `predicted`: Stanley's list for this case;
- `claim`, `convention`, `positions_of_k`: descriptive fields, not read by
  the checkers (`positions_of_k` counts the standard tableaux in which k
  occupies each cell).

The witnesses are `witness-311-k3.json` (λ = (3,1,1), k = 3, the smallest
counterexample: Smith form (1,1,1,1,2,2) against the prediction
(1,1,1,1,1,4)) and `witness-52-k7.json` (λ = (5,2), k = 7: Smith form
(1,1,1,1,2,4,4,4,4,0,0,0,0,0) against (1,1,1,1,1,4,4,4,4,0,0,0,0,0)).

## Checker A: `check_snf.py`

Works from the definitions, with exact rational arithmetic:

1. enumerates the standard Young tableaux from all n! fillings and checks
   that `basis` is exactly that set;
2. checks that the standard polytabloids are linearly independent and that
   every one of the n! polytabloids is an integer combination of them, so
   they form a Z-basis of S^λ;
3. recomputes X_k e_T for each basis tableau and checks it equals column j
   of `A`;
4. checks that `A`, `U` and `V` are f × f integer matrices, that
   U·A·V = diag(`snf`), that det U and det V are ±1, and that `snf` is a
   divisibility chain, so `snf` is the Smith normal form of X_k on S^λ;
5. recomputes Stanley's list, checks it equals `predicted`, and requires it
   to differ from `snf`.

## Checker B: `check_mod2.py`

Written separately, with different enumeration and arithmetic:

1. enumerates the standard Young tableaux by Yamanouchi (lattice) words;
2. shows that the span over F₂ of all n! polytabloids, inside the tabloid
   module over F₂, has dimension f. Since S^λ is free of rank f (the
   standard basis theorem, which checker A confirms for these inputs),
   S^λ/2S^λ embeds in the tabloid module over F₂;
3. computes the rank of X_k on that span, which needs no choice of basis.
   It equals the number of odd invariant factors of X_k on S^λ;
4. compares that rank with the number of odd entries of Stanley's list,
   recomputed from the Yamanouchi words, and requires them to differ;
5. checks `basis`, `A`, `U`, `V` and `snf` with its own code: X_k e_T
   equals the combination given by `A` exactly over Z, U·A·V = diag(`snf`),
   determinants ±1 by Bareiss elimination, a divisibility chain, and as many
   odd entries in `snf` as the rank found in step 3.

For λ = (3,1,1), k = 3, X_3 has rank 4 over F₂, while the predicted list
(1,1,1,1,1,4) has five odd entries. This part alone already refutes the
conjecture for the integral Specht module.

## Checker C: `check_small.py`

Written separately from checkers A and B, importing neither, and reading no
file from `data/`. It shows that λ = (3,1,1), k = 3 is a smallest
counterexample. For every partition λ of n ≤ 5 and every 1 ≤ k ≤ n it:

1. builds the polytabloids of all n! fillings in the row-tabloid module;
2. proves that the standard polytabloids form a Z-basis of their span: the
   square matrix of the coefficients of the tabloids {T}, for T standard,
   in the standard polytabloids has determinant ±1, and every one of the n!
   polytabloids is rebuilt exactly from the integer coordinates that matrix
   gives;
3. forms the matrix of X_k in that basis;
4. computes its Smith form from determinantal divisors: d_j is the gcd of
   all j × j minors, computed as exact integer determinants, and the j-th
   invariant factor is d_j / d_{j−1};
5. recomputes Stanley's list, with the empty product equal to 1.

It requires that all 34 cases with n ≤ 4 agree with the conjecture, and
that exactly 2 of the 35 cases with n = 5 disagree, both for λ = (3,1,1):
k = 3, with Smith form (1,1,1,1,2,2) against (1,1,1,1,1,4), and k = 5, with
(1,1,2,2,4,4) against (1,1,1,4,4,4). It also requires that Stanley's worked
example λ = (5,1), k = 5 gives (1,1,3,3,12), as predicted. It runs in under a
second, and its checks don't depend on Python's assertions, so `-O` doesn't
skip them.

## Control and corruptions

`data/control-51-k5.json` is Stanley's own worked example, λ = (5,1), k = 5,
where the Smith form (1,1,3,3,12) agrees with the prediction. It is a valid
certificate, and both checkers reject it as showing no discrepancy, so they
do not accept a case merely because its certificate is well formed.

Each file in `data/corrupt/` changes one thing in a witness:

| File | Change | Rejected because |
|---|---|---|
| `A-entry.json` | one entry of A changed | a column of A is not X_k e_T |
| `snf-claims-prediction.json` | snf replaced by the prediction | U·A·V ≠ diag(snf) |
| `U-not-unimodular.json` | U made non-unimodular, snf adjusted to match | det U ≠ ±1 |
| `U-rational.json` | one row of U doubled and another halved, snf adjusted | U is not an integer matrix |
| `snf-extra-zero.json` | an extra factor 0 appended | snf does not have f entries |
| `basis-nonstandard.json` | a non-standard tableau in the basis | the basis is not the standard tableaux |
| `prediction-altered.json` | the recorded prediction changed | it differs from the recomputed one |

`check.py` lists the exact rejection message it expects from each checker.

## What the checks do not cover

The checkers establish the Smith form on the integral Specht module with
its standard polytabloid basis, the lattice Grinberg specified. That the
same Smith form holds on every lattice stable under the permutations of
1, 2, 3, and that the conjecture fails at k = 3 for every shape with at
least three rows and three columns, are written arguments in the paper,
not checked by these programs. The Lean project in `../lean/` checks the
computation on the 6 × 6 matrix of the smallest witness.

## Optional census programs

[`census/`](census/README.md) holds the programs that computed the Smith
forms for every λ with n ≤ 8 and every k (`data/census-n8.json`) and
compared other readings of the conjecture. They need third-party packages,
are not part of the check, and the certificates do not depend on them.
