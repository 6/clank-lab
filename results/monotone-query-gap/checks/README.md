# Exact certificate checks

From the result's top directory, run:

```sh
python3 -I checks/check.py
```

Python 3.10 or newer is required. There are no third-party Python packages;
`requirements.txt` records this. Both checkers use exact integers and
rationals, without an optimizer or floating-point arithmetic. The entry
point runs two separately implemented checkers on
[`data/certificate.json`](../data/certificate.json), then requires both to
reject eleven deliberate corruptions. A rejection must be exit code 1
with a `REJECT` message and no error on standard error, so a crashed checker
does not count as a successful control.

Both implementations verify the formula
$f(x)=x_1x_2x_3\lor x_0x_4(x_1\lor x_2\lor x_3)$, its monotonicity, a
query lower bound for all 243 restrictions, a decision tree of expected
cost $13/4$, an eleven-cell monochromatic partition of expected
codimension $51/16$, and the matching linear-programming dual lower bound.
The second checker also recomputes the adaptive optimum independently.
The first represents restrictions as strings, while the second uses masks
and submasks and a disjunction of the four minimal true sets for the
function. Neither imports a search program or the other checker.

## Certificate meaning

A point is an integer $x$ from 0 through 31, with $x_i$ its bit $i$.
A subcube string has five characters from `0`, `1`, `*`, in coordinate order
0 through 4. A star denotes a free bit. The proof fields are:

- `truth_table`: the 32 values of $f$, in integer point order.
- `lower_bound_table`: a rational $L(r)$ for each of the 243 restrictions.
  Constant restrictions satisfy $L(r)\le0$. Every free coordinate $i$ of a
  nonconstant restriction satisfies
  $L(r)\le1+(L(r_{i=0})+L(r_{i=1}))/2$.
  Induction over a decision tree gives the query lower bound from
  $L(\texttt{*****})=13/4$. Repeated queries cannot help.
- `optimal_tree`: nodes `{"q": i, "0": T0, "1": T1}` and leaves
  `{"leaf": v}`. Both checkers follow every input to a correctly labeled
  leaf where $f$ is determined and verify the total depth 104. This tree
  gives the required query upper bound, even if counting all the way to a
  leaf could in general count queries made after the value is determined.
- `partition`: eleven subcube strings, covering every point exactly once,
  each monochromatic, with total codimension 102 over the 32 points.
- `sc_dual`: 32 rational weights $y_x$. For every monochromatic subcube $C$,
  the checkers verify
  $\sum_{x\in C}y_x\le\mathrm{codim}(C)|C|$, and they verify
  $\sum_x y_x=102$.

Summing the last inequality over any monochromatic partition proves
$sc(f,\pi_{1/2})\ge102/32=51/16$, matching the explicit partition.
The remaining certificate fields are descriptive metadata; the independent
checker additionally checks `n`, `p`, `a_value`, and `sc_value` when present.

The controls alter the truth table, lower-bound table, partition, dual or
tree. One changes two dual entries while keeping their sum fixed, so its
rejection checks the subcube inequalities rather than just the objective.
The original mathematical result is also checked by
[the Lean proof](../lean/README.md), except for the dual lower bound, which
is established by these two certificate checkers.
