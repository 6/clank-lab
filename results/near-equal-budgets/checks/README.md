# Checkers

`sh checks/check.sh`, run from the result's folder, runs six checks with Python's standard library alone and prints `PASS: 6 of 6 checks`. `sh checks/check.sh --part K/N` runs checks K, K+N, K+2N, … (the public workflow runs eight parts). Each check prints its program's output and then whether it passed; a check passes only if its program exits as expected and prints the expected figures.

| Check | Program | Expected result | Time |
|---|---|---|---|
| 1 | `check_instance.py data/instance.json data/certificate.json` | the hypotheses hold | under a second |
| 2 | `check_cert.py data/certificate.json` | all 243 allocations certified, radius `r=1/17` | under a second |
| 3 | `check_ray.py data/instance.json` | `R=1/17` | about four minutes |
| 4 | `check_cert.py` on corruption 1 | rejected | under a second |
| 5 | `check_cert.py` on corruption 2 | rejected | under a second |
| 6 | `check_ray.py` on corruption 3 | rejected | about two minutes |

Times are on one core of a current laptop or server; memory stays under 100 MB.

## The market

`data/instance.json` holds the values (one row per agent, goods in the order $v, w, x, y, z$) and the direction $d = (-3, 2, 1)$:

| agent | $v$ | $w$ | $x$ | $y$ | $z$ |
|---|---|---|---|---|---|
| 1 | 6 | 12 | 11 | 9 | 13 |
| 2 | 14 | 4 | 1 | 8 | 20 |
| 3 | 8 | 6 | 9 | 16 | 12 |

The theorem concerns the budgets $e + \delta d = (1-3\delta, 1+2\delta, 1+\delta)$. In the programs agents and goods are numbered from 0, so agent 1 of the paper is agent 0 there.

`check_instance.py` checks that the market inside the certificate file is this one, that every value is a positive integer (so each valuation is strictly increasing), that each agent's 32 bundle values are pairwise distinct (strict preferences), and that the entries of $d$ sum to 0.

## The certificates

`data/certificate.json` repeats the market under `instance` and lists, under `certificates`, one entry for each of the $3^5 = 243$ allocations:

- `owner`: the agent receiving each good, in the order $v, w, x, y, z$;
- `type`: `A` (the weight $w$ has $w \cdot e < 0$) or `B` ($w \cdot e = 0$ and $w \cdot d < 0$);
- `alpha`: the multipliers $\alpha_i \ge 0$, one per agent, as rational strings such as `"2/7"`;
- `lambda`: triples `[i, Y, value]`, the multiplier $\lambda_{i,Y} \ge 0$ for a bundle $Y$ that agent $i$ strictly prefers to its own, with $Y$ a bit mask over the goods (bit 0 for $v$).

`check_cert.py` checks, in exact rationals, that every allocation has exactly one certificate; that each $\lambda_{i,Y}$ belongs to a bundle agent $i$ strictly prefers to its own; that the multipliers are nonnegative and that, for every good, the $\alpha_i$ of its owner is at least the sum of the $\lambda_{i,Y}$ over bundles $Y$ containing it; and that the weight $w_i = \alpha_i - \sum_Y \lambda_{i,Y}$ is of type A or B. It ignores the `type` field and recomputes the type from the weight. It prints the least $r_X$ over the type-A allocations, where $r_X = -w \cdot e / w \cdot d$ when $w \cdot d > 0$; this is the radius $r = 1/17$. Lemma 2.1 of the paper shows why such multipliers exclude every equilibrium with that allocation at budgets $t$ with $w \cdot t < 0$.

## The independent computation

`check_ray.py` reads only the market. For each allocation it solves, with its own exact two-phase simplex method (Bland's rule, Python fractions), the linear program in prices $p \ge 0$ and $\delta \ge 0$ with $p(X_i) \le 1 + \delta d_i$ for each agent and $p(Y) \ge 1 + \delta d_i$ for every bundle $Y$ that agent $i$ strictly prefers to $X_i$. It finds the least feasible $\delta$, and the greatest when the least is 0. It passes when every allocation is infeasible, feasible only at $\delta = 0$, or feasible only from some positive $\delta$ on, and prints the least such $\delta$, $R = 1/17$. Its counts are 214 infeasible allocations, 17 feasible only at $\delta = 0$ (the 17 of type B) and 12 feasible from some $\delta \ge 1/17$ on.

## Corrupted inputs

`corrupt.py` writes three corrupted inputs into a temporary folder, and each must be rejected:

1. the certificate with the first $\lambda$ multiplier of the first type-B certificate doubled: `check_cert.py` reports that the condition on the goods fails;
2. the certificate checked against the market with agent 1's value for $v$ lowered from 6 to 1: `check_cert.py` reports a bundle that agent 1 no longer prefers;
3. that changed market alone: `check_ray.py` reports the allocation (agent 2, agent 1, agent 3, agent 2, agent 3) of $v, w, x, y, z$ as feasible for $\delta$ in $[0, 2/11]$.

## How the example was found

A randomized search over small integer valuations and directions, with floating-point linear programs, found budgets near equal at which no allocation had equilibrium prices; the example was then reduced to small integers and its certificates were computed by an exact simplex method. Neither the search nor the certificate builder is part of the proof, and neither is included.

## Further credits

- M. Babaioff, N. Nisan and I. Talgam-Cohen, *Competitive equilibrium with indivisible goods and generic budgets*, Mathematics of Operations Research 46 (2021), 382–403, [doi:10.1287/moor.2020.1062](https://doi.org/10.1287/moor.2020.1062); [arXiv:1703.08150v2](https://arxiv.org/abs/1703.08150v2), Theorems 1.1 and 7.1, Open Problem 1, Definition 2.1, and Section 9.2 and Appendix B.2 (the authors' computer search, which found a CE in every Spliddit instance with more than two agents after an almost-equal perturbation of the budgets).
- M. Babaioff, N. Nisan and I. Talgam-Cohen, *Competitive equilibria with indivisible goods and generic budgets*, [arXiv:1703.08150v1](https://arxiv.org/abs/1703.08150v1) (March 23, 2017), Section 1.4: the earlier question on generic budgets for any number of players.
- M. Babaioff, N. Nisan and I. Talgam-Cohen, *Competitive equilibrium with generic budgets: beyond additive*, [arXiv:1911.09992v1](https://arxiv.org/abs/1911.09992v1), Theorem 3.5 (two agents, five goods, non-additive preferences).
- M. Babaioff, N. Nisan and I. Talgam-Cohen, *Fair allocation through competitive equilibrium from generic incomes*, Proceedings of the Conference on Fairness, Accountability, and Transparency (2019), [doi:10.1145/3287560.3287582](https://doi.org/10.1145/3287560.3287582).
- E. Segal-Halevi, *Competitive equilibrium for almost all incomes: existence and fairness*, Autonomous Agents and Multi-Agent Systems 34 (2020), article 26, [doi:10.1007/s10458-020-09444-z](https://doi.org/10.1007/s10458-020-09444-z); [arXiv:1705.04212v6](https://arxiv.org/abs/1705.04212v6), Definitions 1–3, Lemma 5, Theorems 4–6 and Section 10.1.
- Prove2Me, a platform for contributors working with AI agents: Lean statements of Babaioff, Nisan and Talgam-Cohen's results by a contributor (@mikedeng1), created October 8, 2026, among them Theorem 7.1 (`envs/0df444a/Theorems/Thm_GenericBudgets_AlmostEqual_theorem_7_1.lean` in the daily export [prove2me/formalpedia](https://github.com/prove2me/formalpedia)), read November 5, 2026. The proof here does not use them.
- E. Budish, *The combinatorial assignment problem: approximate competitive equilibrium from equal incomes*, Journal of Political Economy 119 (2011), 1061–1103, [doi:10.1086/664613](https://doi.org/10.1086/664613).
- D. K. Foley, *Resource allocation and the public sector*, Yale Economic Essays 7 (1967), 45–98.
- H. R. Varian, *Equity, envy, and efficiency*, Journal of Economic Theory 9 (1974), 63–91, [doi:10.1016/0022-0531(74)90075-1](https://doi.org/10.1016/0022-0531(74)90075-1).
- A. Schrijver, *Theory of Linear and Integer Programming*, Wiley, 1986 (Farkas' lemma).
- Wikipedia, *List of unsolved problems in fair division*, section [Competitive equilibrium for almost all incomes](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_fair_division#Competitive_equilibrium_for_almost_all_incomes), revision 1360704274, read November 5, 2026: the open conjecture that with three agents, even with additive valuations, CE for almost all incomes might not exist.
