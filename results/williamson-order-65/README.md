# Nonexistence of Williamson matrices of order 65

[![Checks](https://github.com/6/clank-lab/actions/workflows/williamson-order-65.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/williamson-order-65.yml)

[Williamson matrices](https://en.wikipedia.org/wiki/Williamson_conjecture) are four symmetric matrices of signs, each formed by cyclically shifting a row, whose squares sum to a multiple of the identity. Introduced by Williamson in 1944 to construct Hadamard matrices, they prompted the question of existence at every order. Earlier searches disproved this at orders 35, 47, 53 and 59; [Bright in 2019](https://cs.curtisbright.com/extended-research-statement.pdf) called 65 “currently the smallest order for which it is unknown” whether Williamson matrices exist. Order 67 remains open. This work gives a computer-assisted nonexistence result: no four symmetric circulant sign matrices $A,B,C,D$ of order $65$ satisfy $A^2+B^2+C^2+D^2=260I_{65}$. Kharaghani, Mohammadian, Tayfeh-Rezaie and Zaitsev's [near-Williamson construction, v2 (September 6, 2026)](https://arxiv.org/html/2605.08661v2) supplies an order-65 example in a broader family where one block need not be symmetric; the work was first posted as a three-author v1 in May 2026. The present result concerns the symmetric family. Two earlier GPU searches by the same team share the specification and are reported but not distributed here; not all original raw execution records were rechecked. The conclusion depends on correct execution of the search programs. The records are not a short proof certificate or a formal verification of the search.

Exhaustive computer search with a replayable CPU implementation, receipts and two independent coverage and accounting checkers.

Computer-assisted; not yet reviewed by experts.

The proofs, the search code, the certificate checkers and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

## Check it

Use Python 3.10 or newer, GCC and G++ with OpenMP, and the OpenSSL development headers and library. From this folder:

```sh
python3 -m pip install -r checks/requirements.txt
python3 checks/check.py
```

This checks both independent coverage and receipt checkers, their corruption controls, published counts at odd orders through 33, and known-case controls at 39, 45 and 55. It takes tens of minutes, with about 8 GB of memory and 8 GB of free disk space for regenerated data. It does not repeat the full order-65 pair search. For the unfiltered small-order baseline and discovery at order 55, use `python3 checks/check.py --full-controls`; for the complete order-65 search, use `python3 checks/check.py --full-search`. The latter is a substantial computation. See [the checker guide](checks/README.md) for the scope of each mode, resource needs, and the full data specification. The default check runs from this folder alone; large row data can be regenerated and do not require a dataset deposit. No separate dataset deposit exists and no dataset DOI has been assigned.

## Credits

John Williamson introduced the construction and its product identity. Richard Turyn developed the infinite family. Leonard Baumert, Solomon Golomb and Marshall Hall pioneered computer searches; Baumert and Hall, K. Sawade, Christos Koukouvinos and S. Kounias, Dragomir Đoković, W. H. Holzmann, Hadi Kharaghani and Behruz Tayfeh-Rezaie developed the odd-order searches and classifications. Dragomir Đoković and Ilias Kotsireas developed compression of complementary sequences; Curtis Bright, Ilias Kotsireas and Vijay Ganesh combined algebraic and spectral restrictions with SAT enumeration in MathCheck. The [classification through odd order 59](https://doi.org/10.1007/s10623-007-9163-5) has a 2007 manuscript and was published in 2008. The [MathCheck SAT and computer-algebra enumeration](https://arxiv.org/abs/1804.01172) was first posted in 2018. Their methods and recorded small-order counts provide the mathematical and computational background here. Aidan Bennett, Curtis Bright, Paul Colinot and Ashwin Nayak's [quaternionic perfect-sequence work](https://arxiv.org/abs/2601.22337), first posted January 29, 2026, enumerates the broader circulant Williamson-type family through order 21, allowing nonsymmetric blocks. It is relevant recent enumeration work; its code and quaternionic correspondence are not used in this search. Version 2 of the near-Williamson work by Hadi Kharaghani, Ali Mohammadian, Behruz Tayfeh-Rezaie and Vlad Zaitsev is credited above and distinguished in the paper. Ronan Egan, Ilias Kotsireas, Stephen London and Pádraig Ó Catháin's [recent survey](https://arxiv.org/abs/2610.27175), first posted on October 19, 2026, covers the wider Hadamard construction problem. Wolfgang Lang and Ekkehard Schneider's Turyn-type searches include order 61. S. Y. Zhang's [April 2, 2026 report](https://doi.org/10.5281/zenodo.19392279) describes an earlier attempt on the exact order-65 problem that left it unsolved; no code or reductions from that attempt are used here. The paper gives the references. The checkers use NumPy, mpmath, OpenMP and OpenSSL.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamWilliamsonOrder652026,
  author       = {Graham, P.},
  title        = {{Nonexistence of Williamson matrices of order 65}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/williamson-order-65-v1/results/williamson-order-65}}
}
```
