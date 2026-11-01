import FT23.MeasureBridge

/- Self-contained target statement and conditional assembly. Final.lean supplies all
   four obligations from proved declarations and exports the unconditional endpoint.
   This interface alone is not a completed construction. -/
namespace FT23

/-- The complete fixed-generator endpoint: generator, full copula/PQD, actual non-PMI,
    and a negative rectangle with the specified dyadic radius. -/
def FullEndpoint : Prop :=
  StrictGenerator phi psi ∧ IsCopula C ∧ PQD C ∧ ¬ PrimaryPMI C ∧ AllowedNegativeRectangle

/-- Dependency interface, not an existence assertion or an added foundation. -/
structure Construction : Prop where
  generator_properties : StrictGenerator phi psi
  copula_valid : IsCopula C
  pqd_global : PQD C
  rectangle_negative : AllowedNegativeRectangle

/-- Conditional assembly; Final.lean discharges its Construction interface. -/
theorem assemble_endpoint (built : Construction) : FullEndpoint := by
  refine ⟨built.generator_properties, built.copula_valid, built.pqd_global, ?_, built.rectangle_negative⟩
  obtain ⟨j, _, _, hr, hn⟩ := built.rectangle_negative
  exact negative_rectangle_not_PMI hr hn

/-- A completed construction refutes the universal equivalence on this strict subclass. -/
theorem construction_refutes_equivalence (built : Construction) :
    ¬ (∀ (f p : ℝ → ℝ), StrictGenerator f p →
      let F := fun u v : ℝ => if 0 < u ∧ 0 < v then p (f u + f v) else 0
      IsCopula F → (PQD F ↔ PrimaryPMI F)) := by
  have full := assemble_endpoint built
  intro h
  exact full.2.2.2.1 ((h phi psi full.1 full.2.1).mp full.2.2.1)

end FT23

#print axioms FT23.assemble_endpoint
#print axioms FT23.construction_refutes_equivalence
