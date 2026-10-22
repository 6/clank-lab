import Mathlib

/-! # The toroidal map `{4,4}_(s,0)`, defined geometrically (ARP §1D)

The square tessellation `{4,4}` of the plane has vertices `ℤ²`, the unit edges
and the unit squares. `{4,4}_(s,0)` is its quotient by the translations by
`sℤ²` (the lattice spanned by `(s,0)` and `(0,s)`). Its vertices are
`(ℤ/s)²`, and for `s ≥ 3` each face is determined by its vertex set, so the
faces are recorded here as subsets of `(ℤ/s)²`, ordered by inclusion: the empty
face, the `s²` vertices, the `2s²` edges `{v, v + (1,0)}` and `{v, v + (0,1)}`,
the `s²` squares, and the whole map. No group appears in the definition. -/

namespace P16c

/-- The faces of the square tessellation `{4,4}` of the plane as vertex sets in
`ℤ²`: the empty face, the vertices, the unit edges, the unit squares, and the
whole plane. -/
def planeFaces : Set (Set (ℤ × ℤ)) :=
  {∅, Set.univ} ∪ (Set.range fun v => {v}) ∪ (Set.range fun v => {v, v + (1, 0)}) ∪
    (Set.range fun v => {v, v + (0, 1)}) ∪
    (Set.range fun v => {v, v + (1, 0), v + (0, 1), v + (1, 1)})

/-- The vertices `(ℤ/s)²` of `{4,4}_(s,0)`. -/
abbrev TorusVertex (s : ℕ) := ZMod s × ZMod s

/-- The faces of `{4,4}_(s,0)` as vertex sets: the empty face, the vertices, the
horizontal and vertical edges, the squares, and the whole map. -/
def torusFaces (s : ℕ) : Set (Set (TorusVertex s)) :=
  {∅, Set.univ} ∪ (Set.range fun v => {v}) ∪ (Set.range fun v => {v, v + (1, 0)}) ∪
    (Set.range fun v => {v, v + (0, 1)}) ∪
    (Set.range fun v => {v, v + (1, 0), v + (0, 1), v + (1, 1)})

/-- The quotient map `ℤ² → ℤ²/sℤ² = (ℤ/s)²`. -/
def torusProj (s : ℕ) (v : ℤ × ℤ) : TorusVertex s := ((v.1 : ZMod s), (v.2 : ZMod s))

/-- The toroidal map `{4,4}_(s,0)`: its faces, ordered by inclusion. -/
abbrev TorusMap (s : ℕ) : Type := ↥(torusFaces s)

/-- The rank: `-1` for the empty face, `0` for vertices, `1` for edges (two
vertices), `2` for squares (four vertices) and `3` for the whole map. -/
noncomputable def torusRank (s : ℕ) (F : TorusMap s) : ℤ :=
  if (F : Set (TorusVertex s)) = Set.univ then 3
  else if (F : Set (TorusVertex s)).ncard = 4 then 2
  else ((F : Set (TorusVertex s)).ncard : ℤ) - 1

end P16c
