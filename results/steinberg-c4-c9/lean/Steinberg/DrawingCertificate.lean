import Steinberg.DrawingData

namespace Steinberg.Drawing

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def distinctCheck (points : Nat → IPoint) (n : Nat) : Bool :=
  (List.range n).all fun i => (List.range n).all fun j =>
    i == j || !(points i == points j)

def edgeRow (points : Nat → IPoint) (n : Nat) (edges : List (Nat × Nat))
    (e : Nat × Nat) : Bool :=
  ((List.range n).all fun v =>
    if v == e.1 || v == e.2 then true
    else vertexCheck (points e.1) (points e.2) (points v)) &&
  edges.all (pairCheck points e)

theorem distinct_sound {points : Nat → IPoint} {n : Nat}
    (h : distinctCheck points n = true) (i j : Nat) (hi : i < n) (hj : j < n)
    (he : points i = points j) : i = j := by
  have h' := List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_range.mpr hi))
    j (List.mem_range.mpr hj)
  simpa [he] using h'

/-- A solved square control with exactly the same geometric checker. -/
def squarePoints (v : Nat) : IPoint :=
  [(0, 0), (1000000, 0), (1000000, 1000000), (0, 1000000)][v]?.getD (0, 0)

def squareEdges : List (Nat × Nat) := [(0, 1), (1, 2), (2, 3), (0, 3)]

theorem square_checked : distinctCheck squarePoints 4 = true ∧
    squareEdges.all (edgeRow squarePoints 4 squareEdges) = true := by decide +kernel

/-- Crossing diagonals are rejected geometrically, without using incidence or
coincident vertices as a proxy. -/
theorem square_diagonals_rejected :
    pairCheck squarePoints (0, 2) (1, 3) = false := by decide +kernel

/-- Collinear adjacent edges that overlap away from their common endpoint are
rejected. Opposite rays are accepted by the same checker. -/
theorem adjacent_ray_controls :
    rayCheck (0, 0) (2, 0) (1, 0) = false ∧
    rayCheck (0, 0) (2, 0) (-1, 0) = true := by decide +kernel

end Steinberg.Drawing
