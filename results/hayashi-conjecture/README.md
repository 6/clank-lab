# Connected quandles that refute Hayashi's conjecture

[![Checks](https://github.com/6/clank-lab/actions/workflows/hayashi-conjecture.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/hayashi-conjecture.yml)

A [quandle](https://en.wikipedia.org/wiki/Racks_and_quandles) is a set with a binary operation modeled on conjugation in a group, and quandles give invariants of knots. In a finite connected quandle every right translation $`x \mapsto x * y`$ is a permutation with the same cycle type, called the profile. Chuichiro Hayashi conjectured in [Conjecture 1.1 of a 2013 paper](https://doi.org/10.1080/00927872.2012.685532) that the longest cycle length in the profile is a multiple of every other cycle length. António Lages and Pedro Lopes [proved this for profiles with at most five cycles](https://doi.org/10.26493/1855-3974.3529.4e5), Taisuke Watanabe for all orders up to 47, and T. Kajiwara and C. Nakayama for affine quandles. We give connected quandles of orders 1890 and 5670 whose profiles contain cycles of lengths 60, 84, 140 and 210. Since 60, 84 and 140 do not divide 210, the conjecture is false.

Each quandle is a conjugacy class in a group of affine maps of a sum of vector spaces over the fields with 2, 3, 5 and 7 elements. Filip Filipi [showed](https://arxiv.org/abs/2503.22377v1) that for such conjugation quandles the conjecture is equivalent to a centrality condition on conjugacy classes, stated as Conjecture 4.1 of that paper, so that conjecture is false too. The same construction gives an infinite family of counterexamples, including latin ones, the smallest of order 10395. No counterexample from the construction is smaller than 1890; whether a smaller connected quandle refutes the conjecture remains open.

All of these statements have written proofs in the paper. Computer programs independently recheck the two quandles of orders 1890 and 5670 and Filipi's condition for them; the family and the minimality within the construction are proved by hand only.

Computer-assisted; not yet reviewed by experts.

The proofs, the checking programs and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23990073](https://doi.org/10.5281/zenodo.23990073)

## Check it

The checks need Python 3.12 or newer, numpy and a C compiler. From this directory, run:

```sh
python3 -m pip install --require-hashes -r checks/requirements.txt
python3 -I checks/check.py
```

This takes about three minutes on an ordinary computer. For each quandle it rebuilds the conjugacy class and its full operation table, checks every quandle axiom, connectedness, the profile and faithfulness, checks Filipi's condition two ways, and confirms that every checker rejects deliberately corrupted inputs. Right self-distributivity is checked over all triples for order 1890 and over a sample for order 5670; `python3 -I checks/check.py --full` checks all triples for order 5670 as well, which takes about ten minutes in all. The [checking notes](checks/README.md) describe the four programs.

## Credits

Chuichiro Hayashi posed the conjecture. The work this result builds on most is Filip Filipi's study of conjugation quandles, whose Theorem 4.1 and Conjecture 4.1 recast the conjecture as a centrality condition, completing ideas of S. Kayacan, and the paper of António Lages and Pedro Lopes, whose statement of the conjecture (Conjecture 1.6), Theorem 1.7 for at most five cycles and Corollary 2.6 frame the result. Taisuke Watanabe proved the conjecture for orders up to 47. T. Kajiwara and C. Nakayama proved it for affine quandles in 2016, as did Naqeeb ur Rehman in a 2016 thesis and a 2019 paper; the affine case rests on Horoševskiĭ's theorem, reproved by Alexander Bors, that every automorphism of a finite nilpotent group has a cycle whose length is its order.

Dilpreet Kaur, Uday Bhaskar Sharma and Pushpendra Singh proved the conjecture for conjugation quandles of finite irreducible Coxeter groups. Filippo Spaggiari's thesis, in a chapter based on a joint project with Marco Bonatto, reduces the conjecture to faithful quandles; our examples are faithful. The proofs are written by hand. Two independent programs recompute both quandles, one of them checking every quandle axiom on the full operation table, and two more check Filipi's condition. [Further credits](checks/README.md#further-credits) list the other work on the conjecture.

Apache-2.0 (see the repository's LICENSE).

## Cite

```bibtex
@misc{GrahamHayashiConjecture2026,
  author = {Graham, P.},
  title = {{Connected quandles that refute Hayashi's conjecture}},
  year = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/hayashi-conjecture-v1/results/hayashi-conjecture}},
  doi          = {10.5281/zenodo.23990073}
}
```
