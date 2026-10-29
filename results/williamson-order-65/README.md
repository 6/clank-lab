# Nonexistence of Williamson matrices of order 65

[![Checks](https://github.com/6/clank-lab/actions/workflows/williamson-order-65.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/williamson-order-65.yml)

[Williamson matrices](https://en.wikipedia.org/wiki/Williamson_conjecture) are four symmetric matrices of signs, each formed by cyclically shifting a row, whose squares sum to a multiple of the identity. [Bright's March 20, 2019 statement, Section 4.2](https://cs.curtisbright.com/extended-research-statement.pdf), calls 65 “currently the smallest order for which it is unknown” whether they exist. This work gives a computer-assisted nonexistence result: no four symmetric circulant sign matrices $A,B,C,D$ of order $65$ satisfy $A^2+B^2+C^2+D^2=260I_{65}$. Order 67 remains open. For the neighboring family, see Kharaghani, Mohammadian, Tayfeh-Rezaie and Zaitsev's [arXiv version 2, Definition 1.1 and Table 6](https://arxiv.org/html/2605.08661v2). The CPU exhaustion is replayable. Two checkers verify coverage and accounting: one reuses the CPU row generator, while the other regenerates rows with separately written code. They share the compression model, ordering conventions and receipt files; correct execution of the exhaustive joins remains necessary. The receipts are not a short proof certificate or formal verification of the search. Two historical GPU searches by the same team share the specification and are reported but not distributed here; not all original raw execution records were rechecked.

Computer-assisted; not yet reviewed by experts.

The proofs, the search code, the enumeration checkers, the witness checkers and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23753091](https://doi.org/10.5281/zenodo.23753091)


## Check it

Use Python 3.10 or newer, GCC and G++ with OpenMP, and the OpenSSL development headers and library. From this folder:

```sh
python3 -m pip install -r checks/requirements.txt
python3 checks/check.py
```

This runs both coverage and receipt checkers described above, their corruption controls, published counts at odd orders through 33, and known-case controls at 39, 45 and 55. It takes tens of minutes, with about 8 GB of memory and 8 GB of free disk space for regenerated data. It does not repeat the full order-65 pair search. For the unfiltered small-order baseline and discovery at order 55, use `python3 checks/check.py --full-controls`; for the complete order-65 search, use `python3 checks/check.py --full-search`. The latter is a substantial computation. See [the checker guide](checks/README.md) for the scope of each mode, resource needs, and the full data specification. The default check runs from this folder alone; large row data can be regenerated and do not require a dataset deposit. No separate dataset deposit exists and no dataset DOI has been assigned.

## Credits

John Williamson introduced the construction and its product identity. Richard Turyn developed the infinite family. Leonard Baumert, Solomon Golomb and Marshall Hall pioneered computer searches; Baumert and Hall, K. Sawade, Christos Koukouvinos and S. Kounias, Dragomir Đoković, W. H. Holzmann, Hadi Kharaghani and Behruz Tayfeh-Rezaie developed the odd-order searches and classifications. Dragomir Đoković and Ilias Kotsireas developed compression of complementary sequences; Curtis Bright, Ilias Kotsireas and Vijay Ganesh combined algebraic and spectral restrictions with SAT enumeration in MathCheck. The [classification through odd order 59](https://doi.org/10.1007/s10623-007-9163-5) has a 2007 manuscript and was published in 2008. The [MathCheck SAT and computer-algebra enumeration](https://arxiv.org/abs/1804.01172) was first posted in 2018. Their methods and recorded small-order counts provide the mathematical and computational background here. Aidan Bennett, Curtis Bright, Paul Colinot and Ashwin Nayak's [quaternionic perfect-sequence work](https://arxiv.org/abs/2601.22337), first posted January 29, 2026, enumerates the broader circulant Williamson-type family through order 21, allowing nonsymmetric blocks. It is relevant recent enumeration work; its code and quaternionic correspondence are not used in this search. Version 2 of the near-Williamson work by Hadi Kharaghani, Ali Mohammadian, Behruz Tayfeh-Rezaie and Vlad Zaitsev is credited above and distinguished in the paper. Ronan Egan, Ilias Kotsireas, Stephen London and Pádraig Ó Catháin's [recent survey](https://arxiv.org/abs/2610.27175), first posted on October 19, 2026, covers the wider Hadamard construction problem. Wolfgang Lang and Ekkehard Schneider's Turyn-type searches include order 61. S. Y. Zhang's [April 2, 2026 report, §§7.4–7.5](https://doi.org/10.5281/zenodo.19392279) records an AI research system's prediction that order 65 is “very likely non-existent”, based on reported computational and structural evidence, while explicitly distinguishing that assessment from a formal proof. The exhaustive computation here confirms that prediction; no code or reductions from Zhang's account are used. The [computation companion](checks/computation.md) retains the detailed history, references, controls, and historical CPU and GPU evidence. The checkers use [NumPy](https://github.com/numpy/numpy), [mpmath](https://github.com/mpmath/mpmath), [OpenMP](https://github.com/OpenMP/sources) and [OpenSSL](https://github.com/openssl/openssl).

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamWilliamsonOrder652026,
  author       = {Graham, P.},
  title        = {{Nonexistence of Williamson matrices of order 65}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/williamson-order-65-v4/results/williamson-order-65}},
  doi          = {10.5281/zenodo.23753091}
}
```
