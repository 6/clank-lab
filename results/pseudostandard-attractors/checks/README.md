# The checkers

Run everything from the result's folder with `python3 checks/check.py`.
Positions are counted from 0, as in Dvořáková and Hendrychová's paper.

The two checkers were written separately and import nothing from each other.

`check_exhaustive.py data/witnesses.json` reads the two examples (directive
prefixes, the lengths of the closures, the word and a five-position
attractor). It

- rebuilds each closure as the shortest word fixed by $R$ (reversal) or $E$
  (reversal with 0 and 1 exchanged) that starts with the given word, trying
  lengths in increasing order;
- checks that the five positions attract every factor;
- tries every set of four positions (58,905 for the 36-letter word, 123,410
  for the 43-letter word) and finds none that is an attractor. A smaller
  attractor would be contained in a four-position one, so this rules out every
  size below five;
- reproduces, as controls, Example 2 (six closures) and Example 4 (the
  Thue–Morse prefixes) of the paper, and its attractor $\lbrace 1, 3\rbrace$ of
  `010010`.

`check_proof.py data/witnesses.json data/obstruction.json data/upper-bound.json`

- rebuilds each closure by the paper's formula $v x \vartheta(v)$, with $x$ the
  longest fixed suffix, and confirms by trying every shorter extension that
  no shorter fixed word starts with the seed;
- checks the seven-factor obstruction in `data/obstruction.json`: each
  factor's complete list of occurrences, that no position lies in all three
  position sets of the left group or of the right group, and that the three
  regions are disjoint, giving the bound $2 + 1 + 2 = 5$;
- checks `data/upper-bound.json`: it lists exactly the 48 distinct factors
  that fit in a gap between consecutive attractor positions, each with an
  occurrence that contains an attractor position;
- computes the smallest attractor size of both words by a branch-and-bound
  search for a smallest set of positions meeting every factor's occurrences.

`check.py` runs both, then runs them on the inputs in `data/rejected/`, each
of which must be rejected: a flipped letter, one closure changed from $E$ to
$R$, five positions that are not an attractor, an attractor of four positions,
a Thue–Morse prefix (which has an attractor of size four), and, for
`check_proof.py`, an occurrence or factor missing from the obstruction or the
table. Last, it confirms that the figure `data/word.svg` matches the data;
`draw_word.py` draws it and is not part of the proof.

## Sources used during development

This DOI archives v2; v3 is prepared and not yet published.

## Further credits

- Ľubomíra Dvořáková and Veronika Hendrychová, [String attractors of Rote sequences](https://doi.org/10.46298/dmtcs.12385) — supplies the conjecture, definitions and control examples.
- Dominik Kempa and Nicola Prezza, [At the roots of dictionary compression: string attractors](https://doi.org/10.1145/3188745.3188814) — introduces string attractors.
- Aldo de Luca and Alessandro De Luca, [Pseudopalindrome closure operators in free monoids](https://www.sciencedirect.com/science/article/pii/S0304397506004245) — introduces generalized pseudostandard sequences.
- Alexandre Blondin Massé, Geneviève Paquin, Hugo Tremblay and Laurent Vuillon, [On generalized pseudostandard words over binary alphabets](https://cs.uwaterloo.ca/journals/JIS/VOL16/Blondin/blondin.pdf) — supplies the description of Rote sequences used here.
- Günter Rote, [Sequences with subword complexity 2n](https://doi.org/10.1006/jnth.1994.1012) — supplies the count of factors of Rote sequences.
- Josef Florian and Ľubomíra Dvořáková, [On periodicity of generalized pseudostandard words](https://doi.org/10.37236/4771) — supplies the periodicity criterion.
- Ľubomíra Dvořáková, [String attractors of episturmian sequences](https://doi.org/10.1016/j.tcs.2023.114341) — supplies minimal attractors of standard Sturmian prefixes.
- Kanaru Kutsukake, Takuya Matsumoto, Yuto Nakashima, Shunsuke Inenaga, Hideo Bannai and Masayuki Takeda, [On repetitiveness measures of Thue–Morse words](https://arxiv.org/abs/2005.09524) — supplies the Thue–Morse attractors used here.
- Simone Faro, Francesco Pio Marino and Arianna Pavone, [Smallest string attractors and minimal coverage certificates of Thue–Morse words](https://arxiv.org/abs/2610.10950) — describes smallest attractors and the same kind of lower-bound certificate.
- Mutsunori Banbara, Hideo Bannai, Peaker Guo, Dominik Köppl, Takuya Mieno and Yoshio Okamoto, [The smallest string attractors of Fibonacci, period-doubling, and Thue–Morse words](https://arxiv.org/abs/2602.16152) — also describes smallest Thue–Morse attractors.
