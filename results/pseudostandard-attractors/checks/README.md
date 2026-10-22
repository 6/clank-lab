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
