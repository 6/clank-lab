# Lean proof

From this directory, with [elan](https://github.com/leanprover/elan) installed:

```sh
lake build
```

`lean-toolchain` pins Lean 4.34.0, which elan installs. The project uses
only Lean's bundled standard library: there is no Mathlib and no other
dependency, so there is no cache to fetch, and Lake builds every file from
source. Warnings are errors (`warningAsError` in `lakefile.toml`).

The build takes about 15 minutes of processor time, mostly in the files of
`Generated/`, which check the blocks by evaluation in Lean's kernel. The
largest of them use up to about 3 GB of memory each, and Lake builds as
many in parallel as the machine has cores. On a machine with less than
about 4 GB of memory per core, limit the number of parallel workers, for
example

```sh
LEAN_NUM_THREADS=2 lake build
```

## What is stated

[Core.lean](Core.lean) defines the objects in a few lines, with no axioms
about tiles. A cell is a pair of integers (row, column); `Adj` is adjacency
(equal in one coordinate, differing by one in the other); a `Tile` is a set
of exactly three distinct cells, connected by walks of adjacent cells inside
it; `Rectangle m n` is the set of cells with $0 \le$ row $< m$ and
$0 \le$ column $< n$:

```lean
def Rectangle (h w : Nat) : Region :=
  fun x => 0 ≤ x.1 ∧ x.1 < h ∧ 0 ≤ x.2 ∧ x.2 < w

/-- A tiling is literally a partition into connected three-element subsets. -/
def Tiling (R : Region) (T : Region → Prop) : Prop :=
  (∀ A, T A → Tile A) ∧
  (∀ x, R x ↔ ∃ A, T A ∧ A x) ∧
  (∀ A B, T A → T B → A ≠ B → Disjoint A B)

def Split (A B C D : Region) : Prop :=
  Tile C ∧ Tile D ∧ Disjoint C D ∧ Union C D = Union A B

def Rigid (A B : Region) : Prop :=
  ∀ C D, Split A B C D → (C = A ∧ D = B) ∨ (C = B ∧ D = A)

def PairwiseRigid (T : Region → Prop) : Prop :=
  ∀ A B, T A → T B → A ≠ B → Rigid A B

/-- The extra vertex of the metagraph is part of the definition. -/
def Locked (R : Region) (T : Region → Prop) : Prop :=
  Tiling R T ∧ PairwiseRigid T ∧ ∃ U, Tiling R U ∧ U ≠ T
```

`Rigid A B` says that no recombination move exists for the pair: every
partition of the union of two tiles into two tiles is the original pair.
`Locked` adds that the rectangle has another tiling, as in Tucker-Foltz's
definition (an isolated vertex of the metagraph that is not its only
vertex).

The main theorem is in [Generated/Universal.lean](Generated/Universal.lean):

```lean
theorem locked_tromino_rectangles (m n : Nat) (hm : 6 ≤ m) (hd : 3 ∣ m) (hn : 4 ≤ n) :
    ∃ T, Locked (Rectangle m n) T
```

It has no hypotheses beyond the three conditions of the conjecture: every
block is built and checked inside the proof. [Check.lean](Check.lean)
restates its type from the definitions, so the build fails if the theorem
says anything else, and checks with `#guard_msgs` that it depends only on
`propext`, `Classical.choice` and `Quot.sound`. It also checks a few
instances of `Adj` and `Rectangle`.

## Where the proof is

The files follow the paper (section numbers refer to it).

- [Core.lean](Core.lean): the definitions, and `noEdges_rigid`: two tiles
  with no adjacent cells are rigid (Lemma 4).
- [Nonunique.lean](Nonunique.lean): the two straight tilings, so a tiling
  with only rigid pairs is locked (`locked_of_rigid`, Lemma 5).
- [Geometry.lean](Geometry.lean) and [Assembly.lean](Assembly.lean): blocks
  cut along full rows and columns; adjacent cells lie in one block or in two
  side neighbors (`edge_boxes`), and the gluing lemma
  (`grid_pairwiseRigid`, `rectangular_assembly`, Lemma 7).
- [Translation.lean](Translation.lean), [Palette.lean](Palette.lean) and
  [Strips.lean](Strips.lean): translation invariance, and assembly from
  blocks that stack and fit side by side (`palette_assembly`,
  `strip_assembly`, Corollary 8); `ProposedCertificate` lists the blocks
  the proof needs, and `universal_of_proposed_certificate` derives the
  theorem from them.
- [Arithmetic.lean](Arithmetic.lean): heights as sums of 6 and 9 (or 9
  and 12), widths from 56 as sums of 8 and 9 (Lemma 10).
- [Finite.lean](Finite.lean), [Certificate.lean](Certificate.lean),
  [SubsetCertificate.lean](SubsetCertificate.lean),
  [FastCertificate.lean](FastCertificate.lean),
  [LocalCertificate.lean](LocalCertificate.lean) and
  [CatalogCertificate.lean](CatalogCertificate.lean): checking procedures
  on explicit lists of cells, each proved sound for the definitions above.
  A table of the tile owning each cell proves the partition; a list of
  neighboring tiles, proved complete, reduces rigidity to touching pairs;
  and each touching pair is matched, by an exact translation, to one of the
  162 pair shapes checked once in `Generated/Catalog.lean`.
- `Generated/`: the blocks, as explicit lists of cells, and their checks by
  kernel evaluation (`decide +kernel`): `Width4.lean` to `Width55.lean`,
  `Direct6.lean` and `Direct15.lean` (the $6 \times 5$ and $15 \times 5$
  tilings), `Tail.lean` (the four blocks of widths 8 and 9),
  `Catalog.lean`, and `Universal.lean`, which assembles them into the main
  theorem. These files are written by `checks/render_lean.py` from `data/`,
  and `checks/check.py` confirms that they match; the rendering is not
  trusted, since Lean checks every fact in them.
- [LocalControls.lean](LocalControls.lean) and
  [ActualControls.lean](ActualControls.lean): the checking procedures
  reject wrong data (two tiles given the same owner, a missing neighbor
  link, a wrong translation, a pair of straight trominoes that recombine,
  and an actual block with its links removed).
- [Audit.lean](Audit.lean): prints the axioms of the main intermediate
  theorems.

No `sorry`, no added axiom and no compiled evaluation (`native_decide`) is
used.
