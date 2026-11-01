import FT23.Endpoint
import FT23.GeneratorAdmissible
import FT23.PQD
import FT23.Witness

/- Unconditional assembly from the exact generator, global copula/PQD proofs and
   the rationally enclosed witness. -/
namespace FT23

theorem endpoint : FullEndpoint :=
  assemble_endpoint ⟨exact_generator, exact_copula, exact_PQD, witness_allowed⟩

theorem conjecture_counterexample :
    StrictGenerator phi psi ∧ IsCopula C ∧ PQD C ∧ ¬ PrimaryPMI C := by
  have h := endpoint
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem conjecture_equivalence_false :
    ¬ (∀ (f p : ℝ → ℝ), StrictGenerator f p →
      let F := fun u v : ℝ => if 0 < u ∧ 0 < v then p (f u + f v) else 0
      IsCopula F → (PQD F ↔ PrimaryPMI F)) :=
  construction_refutes_equivalence ⟨exact_generator, exact_copula, exact_PQD, witness_allowed⟩

end FT23

#print axioms FT23.endpoint
#print axioms FT23.conjecture_counterexample
#print axioms FT23.conjecture_equivalence_false
