import Unit3
import Kernel

noncomputable section

namespace BLSFinal

/-- Discharges the sole explicit hypothesis of the finite representation theorem. -/
theorem hConvexity : BLSUnit3.HConvexity :=
  fun m d => BLSH.complete_convex m d

/-- Stronger orthant result, for every natural degree and nonempty edge size. -/
theorem source_orthant {n L : Nat} (hL : 1 ≤ L) (d : Nat) :
    ConvexOn Real {x : BLSUnit1.Edge n L → Real | ∀ e, 0 ≤ x e}
      (BLSUnit1.sourcePolynomial n L d) :=
  BLSUnit3.conditional_source_orthant hConvexity hL d

/-- Exact full BLS endpoint, including the empty simplex when L > n. -/
theorem fullEndpoint :
    ∀ (n L d : Nat), 2 ≤ n → 2 ≤ L → 2 ≤ d →
      ConvexOn Real (stdSimplex Real (BLSUnit1.Edge n L))
        (BLSUnit1.sourcePolynomial n L d) :=
  BLSUnit3.conditional_fullEndpoint hConvexity

end BLSFinal
