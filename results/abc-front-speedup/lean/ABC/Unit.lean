import ABC.Defs

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace ABC

/-- The ABC field rescaled to period `1`: `u(x) = V(2πx)`. -/
def abcUnit (x : E 3) : E 3 := abcField ((2 * Real.pi) • x)

end ABC
