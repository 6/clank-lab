# The US supercentenarian birth-registration statistic is typical after shuffling birth years

[![Checks](https://github.com/6/clank-lab/actions/workflows/supercentenarian-birth-years.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/supercentenarian-birth-years.yml)

Among US-born people listed as reaching 110, [Newman (2019)](https://doi.org/10.1101/704080) counted 82.6% as born before statewide birth registration and took that as a sign of age errors. His cutoffs varied by a few years from state to state. We show that share is typical for when and where they were born, so on its own it is no such sign.

Computer-assisted; not yet reviewed by experts.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.24459608](https://doi.org/10.5281/zenodo.24459608)

## Abstract

Saul Justin Newman reported that 82% of US entries in a historical roster of people aged 110 or older were early births. His R supplement prints 82.6% and uses cutoffs ranging from three years before statewide birth registration to one year after. Newman took the decline in recorded cases after registration as evidence that better documentation exposed errors in extreme-age records. We ask how often the same early share arises simply from the years and birthplaces represented in the roster. We randomly reassigned its 697 US birth years, keeping each state's number of entries. Newman's published R script counts 646 entries. It gives 534 early births (82.66%) on our reconstruction. Across 10,000 shuffles the middle 95% of shares ran from 81.73% to 83.90%. The roster's birth years and state mix alone typically produce an early share like Newman's. A common 60-year window on either side of registration, including New York, counts 552 of 686 entries as early (80.47%), within its shuffled range of 78.75% to 81.14%. These comparisons tell us about the roster's composition. They cannot tell us which ages were correct.

This work has not yet been reviewed by experts. The computations, code and text were produced by AI models from OpenAI and Anthropic, working under the author's direction.

## Check it

Check the counts and shuffle ranges in under a second with Python 3.10 or later.

```sh
python3 checks/check.py
```

To reproduce them from the three source files, install R, curl and Poppler's pdftotext. After download, this takes a few seconds.

```sh
python3 checks/reproduce.py
```

With NetworkX 3.2.1, add `--bounds` to check the limits over all possible shuffles.

## Credits

Saul Justin Newman published the comparison and its code. Louis Epstein, Robert Young and their colleagues at the Gerontology Research Group compiled and validated the January 2015 list. The Internet Archive preserved it. The National Center for Health Statistics supplied the statewide registration dates.

In August 2019, Young pointed out delays in validating and releasing cases. Newman replied with checks using birth and death cutoffs and census figures. [Further credits](checks/README.md#further-credits). Apache-2.0 (see the repository's LICENSE).

## Cite

```bibtex
@misc{GrahamSupercentenarianBirthYears2026,
  author = {Graham, Peter},
  title = {{The US supercentenarian birth-registration statistic is typical after shuffling birth years}},
  year = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/supercentenarian-birth-years-v2/results/supercentenarian-birth-years}},
  doi          = {10.5281/zenodo.24459608}
}
```
