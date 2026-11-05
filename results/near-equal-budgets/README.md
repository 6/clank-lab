# Competitive equilibrium can fail near equal budgets for three additive agents

[![Checks](https://github.com/6/clank-lab/actions/workflows/near-equal-budgets.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/near-equal-budgets.yml)

In a [Fisher market](https://en.wikipedia.org/wiki/Fisher_market) each agent spends a budget of artificial money on goods, and a [competitive equilibrium](https://en.wikipedia.org/wiki/Competitive_equilibrium) is an allocation of all the goods with prices at which every agent gets a most preferred bundle it can afford. With equal budgets this is the classical competitive equilibrium from equal incomes, a rule for [fair division](https://en.wikipedia.org/wiki/Fair_item_allocation). With indivisible goods it can fail even for one good and two agents. Moshe Babaioff, Noam Nisan and Inbal Talgam-Cohen proved that two agents with additive preferences over any number of indivisible goods do have an equilibrium whenever their budgets are sufficiently close to equal but not equal, and asked whether this holds for more than two agents ([Open Problem 1, arXiv version of September 25, 2018](https://arxiv.org/abs/1703.08150v2)). We show that it does not. Three agents with strict additive values for five goods have no equilibrium at the budgets $(1-3\delta, 1+2\delta, 1+\delta)$ for any $0<\delta<1/17$, nor at any budgets close to these, so every neighborhood of equal budgets contains a set of positive measure with no equilibrium. Adding goods of small value, as in Erel Segal-Halevi's Lemma 5, gives the same for every number of goods $m \ge 5$. This settles the case of three additive agents and $m \ge 5$ goods that Segal-Halevi left open in the study of [competitive equilibrium for almost all incomes](https://arxiv.org/abs/1705.04212v6): the budgets with no equilibrium can have positive measure, as the open conjecture in Wikipedia's [list of unsolved problems in fair division](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_fair_division#Competitive_equilibrium_for_almost_all_incomes) expects.

Computer-assisted; not yet reviewed by experts.

The proofs, the computer checks and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

## Check it

For each of the 243 ways to allocate the five goods, the file `data/certificate.json` gives nonnegative multipliers that combine the equilibrium conditions into an inequality on the budgets alone, which the budgets of the theorem violate. One program checks these certificates in exact rational arithmetic; a second, which does not read them, solves the 243 linear programs exactly along the line of budgets and finds the same bound $1/17$. With Python 3.12 or later and no other packages, from this folder:

```sh
sh checks/check.sh
```

It takes about six minutes on one core, with under 100 MB of memory, and ends with `PASS: 6 of 6 checks`. `sh checks/check.sh --part K/N` runs every N-th check. The [checker documentation](checks/README.md) describes each program, the certificate format and the three corrupted inputs it must reject.

## Credits

Moshe Babaioff, Noam Nisan and Inbal Talgam-Cohen posed the question in *Competitive equilibrium with indivisible goods and generic budgets* (Mathematics of Operations Research, 2021), where they proved existence near equal budgets for two additive agents; the model and the equilibrium notion are theirs. Erel Segal-Halevi's *Competitive equilibrium for almost all incomes: existence and fairness* (Autonomous Agents and Multi-Agent Systems, 2020) asked the almost-all-incomes question for three additive agents, proved existence with four goods, gave additive counterexamples for four or more agents, and supplied the low-value-good argument that extends the result to more goods.

Lean statements of Babaioff, Nisan and Talgam-Cohen's two-agent results, among them their Theorem 7.1, were posted on [Prove2Me](https://github.com/prove2me/formalpedia), a platform for contributors working with AI agents, by a contributor (@mikedeng1) on October 8, 2026; this result does not use them. The proof rests on Farkas' lemma, and the checkers are plain Python with exact rational arithmetic. [Further credits](checks/README.md#further-credits) give the exact references.

Apache-2.0 (see the repository's LICENSE).

## Cite

```bibtex
@misc{GrahamNearEqualBudgets2026,
  author = {Graham, P.},
  title = {{Competitive equilibrium can fail near equal budgets for three additive agents}},
  year = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/near-equal-budgets-v1/results/near-equal-budgets}}
}
```
