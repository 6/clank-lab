import Steinberg.Planarity

namespace Steinberg.Drawing

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Move vertex 32 to (400,400) in the actual published drawing. -/
def crossingPoints (v : Nat) : IPoint :=
  if v == 32 then (400000000, 400000000) else points v

/-- The corrupted drawing still has distinct vertices, but its nonincident
segments 2--23 and 32--33 fail the same exact separation check. -/
theorem crossing_corruption_rejected :
    distinctCheck crossingPoints 82 = true ∧
    pairCheck crossingPoints (2, 23) (32, 33) = false ∧
    edgeRow crossingPoints 82 drawingEdges (2, 23) = false := by decide +kernel

/-- Move vertex 32 exactly onto the midpoint of edge 0--1. Both coordinate
sums are even, so these are again integer millionths of a point. -/
def midpointPoints (v : Nat) : IPoint :=
  if v == 32 then
    ((points 0).1 + (points 1).1, (points 0).2 + (points 1).2).map
      (fun z => z / 2) (fun z => z / 2)
  else points v

theorem midpoint_corruption_rejected :
    distinctCheck midpointPoints 82 = true ∧
    vertexCheck (midpointPoints 0) (midpointPoints 1) (midpointPoints 32) = false := by
  decide +kernel

/-- A direct geometric witness explains the nonincident-vertex rejection. -/
theorem midpoint_on_segment :
    OnSegment (rational (midpointPoints 0)) (rational (midpointPoints 1))
      (realPoint (rational (midpointPoints 32))) := by
  refine ⟨1/2, by norm_num, by norm_num, ?_, ?_⟩ <;>
    norm_num [midpointPoints, points, pointList, rational, realPoint]

/-- Move vertex 32 onto vertex 0, so injectivity fails. -/
def coincidentPoints (v : Nat) : IPoint :=
  if v == 32 then points 0 else points v

theorem coincidence_corruption_rejected : distinctCheck coincidentPoints 82 = false := by
  decide +kernel

/-- info: 'Steinberg.Drawing.crossing_corruption_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms crossing_corruption_rejected

/-- info: 'Steinberg.Drawing.midpoint_on_segment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms midpoint_on_segment

end Steinberg.Drawing
