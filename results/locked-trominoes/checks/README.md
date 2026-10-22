# Checkers

```sh
python3 checks/check.py
```

Python 3.10 or later, standard library only (`requirements.txt` lists
nothing to install). It prints one `PASS` line per step and stops at the
first failure.

## The data

`data/` holds the tilings of the paper's Proposition 9, one JSON file per
family:

- `data/witnesses/width-N.json` for each width $N$ from 4 to 55: blocks
  `h6wN` and `h9wN` of heights 6 and 9 (at width 5, `h9w5` and `h12w5`);
- `data/witnesses/direct-6x5.json` and `direct-15x5.json`: one block each,
  named `A`, tiling the $6 \times 5$ and $15 \times 5$ rectangles;
- `data/palette.json`: the four blocks `h6w8`, `h6w9`, `h9w8` and `h9w9` for
  widths of 56 and more.

Each file has three keys. `blocks` maps a block name to its `height`, its
`width` and its `tiles`, each tile a list of three cells `[row, column]`,
with rows counted from 0 at the top. `vertical` lists ordered pairs
`[X, Y]` meaning that block `X` sits directly above block `Y`, and
`horizontal` lists pairs `[X, Y]` meaning `X` sits directly left of `Y`.
These are the seams to be checked.

## What each program proves

`locked.py` and `independent.py` were written separately and share no code.
Each takes a file and accepts it only if every block is a partition of its
rectangle into connected sets of three cells, every pair of tiles in a block
is rigid (the union of the two tiles has exactly one partition into two
connected sets of three cells, the original one), and for every listed seam
every pair made of a tile of the first block and a tile of the second,
placed next to each other, is rigid. Both list every partition of each
six-cell union directly; neither uses tile templates or the search. Both
can also be run on one file:

```sh
python3 checks/locked.py data/palette.json
python3 checks/independent.py data/palette.json
```

`check.py` runs the whole check:

1. Coverage: the files hold exactly the blocks and the ordered seams the
   proof uses, including both orders of two different blocks and each block
   next to a copy of itself; a missing block or seam fails.
2. Both checkers accept all 110 blocks and 224 seams.
3. Controls: `enumerate_controls.py` lists every tiling of the
   $6 \times 4$ and $6 \times 6$ rectangles all of whose pairs are rigid,
   with no symmetry reduction, and finds 26 (7 up to symmetry, as
   Tucker-Foltz reports) and 50 (as he reports). Both checkers accept one
   tiling from each symmetry class.
4. Corruptions: both checkers reject a repeated cell, a cell outside its
   block, a non-integer coordinate, two straight trominoes that recombine,
   and a locked $6 \times 5$ block placed on a copy of itself, whose seam
   recombines; the coverage step rejects a missing block and a missing seam
   in each direction.
5. Lean inputs: `render_lean.py` renders `data/` as Lean, and the result
   must equal `lean/Generated/` file for file. Lean checks those
   coordinates, so the programs and Lean check the same blocks. The
   rendering is not trusted: everything it writes is checked by Lean.
6. Figures: `figures.py` draws the tilings in the paper's figures and the
   README image `data/tiling.svg` from `data/`, and checks that
   `paper/paper.tex` and the image contain exactly those drawings; each
   drawn rectangle, as a whole, must pass both checkers.

## Optional: finding the blocks

The blocks were found by `search/search.py`, a SAT encoding solved with
[python-sat](https://github.com/pysathq/pysat) (`pip install python-sat`).
It is not part of the proof or the check, and a run may find different
blocks, which would serve equally well. For example:

```sh
python3 checks/search/search.py stack 4 6 9 --out /tmp/width-4.json
python3 checks/search/search.py stack 5 9 12 --out /tmp/width-5.json
python3 checks/search/search.py direct 6 5 --out /tmp/direct-6x5.json
python3 checks/search/search.py palette 8 9 --out /tmp/palette.json
```
