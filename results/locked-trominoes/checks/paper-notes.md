# Paper checking notes

The paper's existence theorem uses Lean's kernel and the definitions in
`lean/Core.lean`. The classification additionally uses Tucker-Foltz's
Theorem 3.1 and the written deduction in the paper. No new mathematical
check, search or replay was performed for this presentation edition.

The published formal theorem depends only on propositional extensionality,
the axiom of choice and the soundness of quotients (`propext`,
`Classical.choice`, `Quot.sound`), checked by `lean/Check.lean`.
The files use Lean 4.34.0 and its standard library, without Mathlib,
`sorry`, added axioms or compiled evaluation. The existing
[Lean notes](../lean/README.md) give the exact definitions and dependency map.

The published resource estimate is about 15 minutes of processor time and
up to about 3 GB per parallel module. The existing
[checking documentation](README.md) and [result README](../README.md)
give the Python and Lean reproduction commands. These are historical
estimates, not new measurements in this edition.

Tucker-Foltz reports 7 symmetry classes of locked 6 by 4 tilings and 50
locked 6 by 6 tilings in Section 1, Figure 2; the 6 by 4 count is in
Section 3. The enumeration accompanying this paper
finds 26 locked 6 by 4 tilings; the count 26 is ours. Its 7 symmetry classes
and the 50 locked 6 by 6 tilings reproduce his counts. His construction
from copies of a locked 6 by 6 tiling handles sides divisible by six;
his strips of lengths 22, 19 and 8 give widths at least 100. The present
blocks complete the remaining cases using the same gluing method.

The paper's figures and their generated drawing commands are retained
unchanged from the published bundle, with their original coordinate data
and checking code. They have only been relocated. The published check
confirms that each drawing agrees with the data and is a tiling with only
rigid pairs.

## Finite checking details

The search that found the blocks is not part of the proof. The formal
proof follows the paper's definitions, gluing and block-construction
sections: the no-adjacent-cells lemma, the arbitrary row-and-column gluing
lemma, the assembly corollary, the arithmetic lemma, the two straight
tilings and the finite block proposition are all checked in Lean.

The blocks occur in `lean/Generated/` as explicit cell lists, one file per
width. Each finite fact is proved by kernel evaluation (`decide`), without
trusting compiled code. Proved checking procedures use a table assigning
each cell its tile to establish the partition. For each tile, a complete
list of tiles containing a neighbor of one of its cells reduces rigidity
to those pairs; the nonadjacent pairs are covered by the lemma. Touching
pairs fall into 162 shapes up to translation and order, checked once and
reused by proved translation invariance. An incorrect cell, tile assignment,
neighbor list or shape is rejected.

`checks/locked.py` and `checks/independent.py` were separately written,
share no code and enumerate all partitions of each six-cell union into two
trominoes. `checks/check.py` runs both, verifies that `data/` contains
exactly the required blocks and seams, checks that `lean/Generated/` is
exactly the rendering of `data/`, and confirms rejection of deliberately
incorrect data by both programs. It also enumerates the small rectangles
whose counts are compared in the paper. `checks/figures.py` draws the paper's
figures from `data/` and checks that each complete drawn rectangle is a
tiling with every pair rigid.
