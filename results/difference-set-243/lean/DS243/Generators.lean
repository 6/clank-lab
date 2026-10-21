import DS243.Basic

/-!
# Generators of the normalization maps

Eleven explicit legal maps of `G` (four translations by elements of `H` and seven additive
automorphisms) and words in them. Every normalization used in the reduction is such a word,
so every finite check evaluates these maps directly; no table of maps is trusted.

* `transX, transY, transZ`: translation by `(1,0,0)`, `(0,3,0)`, `(0,0,3)`.
* `negX`: `(x,y,z) ↦ (-x,y,z)`; `swapYZ`: `(x,z,y)`; `addYZ`: `(x,y+z,z)`; `dblY`: `(x,2y,z)`.
* `shearY`, `shearZ`: add `3x` to `y`, resp. `z` (`up3 x = 3·x` as an element of `ZMod 9`).
* `bX`, `cX`: add `y mod 3`, resp. `z mod 3`, to `x`.
-/

namespace DS243

open Finset

/-- `x ↦ 3x`, from `ZMod 3` to `ZMod 9`. -/
def up3 (x : ZMod 3) : ZMod 9 := 3 * (x.val : ZMod 9)

lemma up3_add (a b : ZMod 3) : up3 (a + b) = up3 a + up3 b := by
  revert a b; decide

lemma red_add (a b : ZMod 9) : red (a + b) = red a + red b := map_add _ a b

/-- The general additive map `(x,y,z) ↦ (ax + b ȳ + c z̄, 3dx + ey + fz, 3gx + hy + iz)`. -/
def linMap (a b c d g : ZMod 3) (e f h i : ZMod 9) : G →+ G :=
  AddMonoidHom.mk' (fun p => (a * p.1 + b * red p.2.1 + c * red p.2.2,
      up3 (d * p.1) + e * p.2.1 + f * p.2.2, up3 (g * p.1) + h * p.2.1 + i * p.2.2)) (by
    intro p q
    simp only [Prod.fst_add, Prod.snd_add, mul_add, red_add, up3_add]
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring)

/-- The eleven generators. -/
inductive Gen
  | transX | transY | transZ | negX | swapYZ | addYZ | dblY | shearY | shearZ | bX | cX
  deriving DecidableEq, Repr

/-- The translation part of a generator. -/
def Gen.tau : Gen → G
  | .transX => (1, 0, 0)
  | .transY => (0, 3, 0)
  | .transZ => (0, 0, 3)
  | _ => 0

/-- The linear part of a generator. -/
def Gen.lin : Gen → (G →+ G)
  | .transX | .transY | .transZ => linMap 1 0 0 0 0 1 0 0 1
  | .negX => linMap 2 0 0 0 0 1 0 0 1
  | .swapYZ => linMap 1 0 0 0 0 0 1 1 0
  | .addYZ => linMap 1 0 0 0 0 1 1 0 1
  | .dblY => linMap 1 0 0 0 0 2 0 0 1
  | .shearY => linMap 1 0 0 1 0 1 0 0 1
  | .shearZ => linMap 1 0 0 0 1 1 0 0 1
  | .bX => linMap 1 1 0 0 0 1 0 0 1
  | .cX => linMap 1 0 1 0 0 1 0 0 1

set_option maxRecDepth 100000 in
lemma Gen.lin_ker (s : Gen) : ∀ x : G, s.lin x = 0 → x = 0 := by
  cases s <;> decide +kernel

lemma Gen.bij (s : Gen) : Function.Bijective s.lin := by
  have hinj : Function.Injective s.lin :=
    (injective_iff_map_eq_zero s.lin).2 (s.lin_ker)
  exact ⟨hinj, Finite.surjective_of_injective hinj⟩

lemma Gen.htau (s : Gen) : 3 • s.tau = 0 := by
  cases s <;> decide

/-- A generator as a legal map. -/
def Gen.legal (s : Gen) : Legal := ⟨s.lin, s.tau, s.bij, s.htau⟩

/-- Words in the generators; `[s₁, …, sₙ]` acts as `s₁ ∘ ⋯ ∘ sₙ`. -/
abbrev Word := List Gen

/-- The legal map of a word. -/
def Word.legal : Word → Legal
  | [] => Legal.id
  | s :: w => s.legal.comp (Word.legal w)

/-- Evaluation of a word, computed generator by generator. -/
def Word.eval : Word → G → G
  | [], x => x
  | s :: w, x => s.legal.toFun (Word.eval w x)

lemma Word.legal_toFun (w : Word) (x : G) : w.legal.toFun x = w.eval x := by
  induction w with
  | nil => simp [Word.legal, Word.eval, Legal.id_toFun]
  | cons s w ih => simp [Word.legal, Word.eval, Legal.comp_toFun, ih]

/-! ## Legal maps act on the cells of `Q = G / 3G` -/

lemma cell_sub (x y : G) : cell (x - y) = cell x - cell y := by
  simp [cell, red, map_sub]

set_option maxRecDepth 100000 in
/-- An element whose cell is zero is a multiple of three. -/
lemma exists_three_of_cell_eq_zero : ∀ z : G, cell z = 0 → ∃ y : G, z = 3 • y := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma cell_three_smul : ∀ y : G, cell (3 • y) = 0 := by decide +kernel

/-- Legal maps respect cells: equal cells have equal images. -/
lemma Legal.cell_congr (L : Legal) {x x' : G} (h : cell x = cell x') :
    cell (L.toFun x) = cell (L.toFun x') := by
  have hz : cell (x - x') = 0 := by rw [cell_sub, h, sub_self]
  obtain ⟨y, hy⟩ := exists_three_of_cell_eq_zero _ hz
  have : L.toFun x - L.toFun x' = 3 • L.lin y := by rw [Legal.toFun_sub, hy, map_nsmul]
  have h2 := congrArg cell this
  rw [cell_sub, cell_three_smul] at h2
  exact sub_eq_zero.1 h2

end DS243
