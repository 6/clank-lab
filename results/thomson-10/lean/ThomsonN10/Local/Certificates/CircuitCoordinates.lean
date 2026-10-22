/- Adapted from proof/lean/ThomsonN9/Certificates/CircuitCoordinates.lean,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.CircuitAlgebra
import ThomsonN10.Data
namespace ThomsonN10.Local.Certificates.IntervalCircuit
def coordinateOps : Array Op := #[.input 0,.mul 0 0,.constant 1 1,.neg 1,.add 2 3,.sqrt 4,.constant 2 1,.sqrt 6,.constant 1 2,.mul 5 7,.mul 9 8,.constant 0 1,.neg 0,.neg 5,.neg 10,.constant (-1) 1]
def CoordinateCheck (nodes : ℕ → Node) : Prop :=
  ∀ i : Fin 16, (nodes i).op = coordinateOps[i.val]?.getD (.input 0)
instance (nodes : ℕ → Node) : Decidable (CoordinateCheck nodes) := by
  unfold CoordinateCheck
  infer_instance
def pointIndices : Fin 10 → Fin 3 → ℕ := ![![11,11,2],![11,11,15],![5,11,0],![11,5,0],![13,11,0],![11,13,0],![10,10,12],![14,10,12],![14,14,12],![10,14,12]]
noncomputable def parameterInputs (r : ℝ) (i : ℕ) : ℝ := if i = 0 then r else 0
theorem coordinate_recipe_sound (r : ℝ) (nodes : ℕ → Node) (h : CoordinateCheck nodes)
    (i : Fin 10) (a : Fin 3) :
    value (parameterInputs r) nodes (pointIndices i a) = candidateAt r i a := by
  let V := value (parameterInputs r) nodes
  have h0 : (nodes 0).op = .input 0 := h ⟨0, by decide⟩
  have v0 : V 0 = r := by
    simpa [V,parameterInputs] using value_input (parameterInputs r) nodes 0 0 h0
  have h1 : (nodes 1).op = .mul 0 0 := h ⟨1, by decide⟩
  have v1 : V 1 = r*r := by
    rw [show V 1 = V 0*V 0 from value_mul _ _ _ _ _ h1 (by decide) (by decide), v0]
    all_goals (try simp only [rho, q])
    all_goals ring
  have h2 : (nodes 2).op = .constant 1 1 := h ⟨2, by decide⟩
  have v2 : V 2 = 1 := by
    simpa [V] using value_constant (parameterInputs r) nodes 2 1 1 h2
  have h3 : (nodes 3).op = .neg 1 := h ⟨3, by decide⟩
  have v3 : V 3 = -(r*r) := by
    rw [show V 3 = -V 1 from value_neg _ _ _ _ h3 (by decide), v1]
    all_goals (try simp only [rho, q])
    all_goals ring
  have h4 : (nodes 4).op = .add 2 3 := h ⟨4, by decide⟩
  have v4 : V 4 = 1-r^2 := by
    rw [show V 4 = V 2+V 3 from value_add _ _ _ _ _ h4 (by decide) (by decide), v2,v3]
    all_goals (try simp only [rho, q])
    all_goals ring
  have h5 : (nodes 5).op = .sqrt 4 := h ⟨5, by decide⟩
  have v5 : V 5 = rho r := by
    rw [show V 5 = Real.sqrt (V 4) from value_sqrt _ _ _ _ h5 (by decide), v4]
    all_goals (try simp only [rho, q])
    all_goals ring
  have h6 : (nodes 6).op = .constant 2 1 := h ⟨6, by decide⟩
  have v6 : V 6 = 2 := by
    simpa [V] using value_constant (parameterInputs r) nodes 6 2 1 h6
  have h7 : (nodes 7).op = .sqrt 6 := h ⟨7, by decide⟩
  have v7 : V 7 = Real.sqrt 2 := by
    rw [show V 7 = Real.sqrt (V 6) from value_sqrt _ _ _ _ h7 (by decide), v6]
    all_goals (try simp only [rho, q])
    all_goals ring
  have h8 : (nodes 8).op = .constant 1 2 := h ⟨8, by decide⟩
  have v8 : V 8 = 1/2 := by
    simpa [V] using value_constant (parameterInputs r) nodes 8 1 2 h8
  have h9 : (nodes 9).op = .mul 5 7 := h ⟨9, by decide⟩
  have v9 : V 9 = rho r*Real.sqrt 2 := by
    rw [show V 9 = V 5*V 7 from value_mul _ _ _ _ _ h9 (by decide) (by decide), v5,v7]
    all_goals (try simp only [rho, q])
    all_goals ring
  have h10 : (nodes 10).op = .mul 9 8 := h ⟨10, by decide⟩
  have v10 : V 10 = q r := by
    rw [show V 10 = V 9*V 8 from value_mul _ _ _ _ _ h10 (by decide) (by decide), v9,v8]
    all_goals (try simp only [rho, q])
    all_goals ring
  have h11 : (nodes 11).op = .constant 0 1 := h ⟨11, by decide⟩
  have v11 : V 11 = 0 := by
    simpa [V] using value_constant (parameterInputs r) nodes 11 0 1 h11
  have h12 : (nodes 12).op = .neg 0 := h ⟨12, by decide⟩
  have v12 : V 12 = -r := by
    rw [show V 12 = -V 0 from value_neg _ _ _ _ h12 (by decide), v0]
    all_goals (try simp only [rho, q])
    all_goals ring
  have h13 : (nodes 13).op = .neg 5 := h ⟨13, by decide⟩
  have v13 : V 13 = -rho r := by
    rw [show V 13 = -V 5 from value_neg _ _ _ _ h13 (by decide), v5]
    all_goals (try simp only [rho, q])
    all_goals ring
  have h14 : (nodes 14).op = .neg 10 := h ⟨14, by decide⟩
  have v14 : V 14 = -q r := by
    rw [show V 14 = -V 10 from value_neg _ _ _ _ h14 (by decide), v10]
    all_goals (try simp only [rho, q])
    all_goals ring
  have h15 : (nodes 15).op = .constant (-1) 1 := h ⟨15, by decide⟩
  have v15 : V 15 = -1 := by
    simpa [V] using value_constant (parameterInputs r) nodes 15 (-1) 1 h15
  change V (pointIndices i a) = candidateAt r i a
  fin_cases i <;> fin_cases a <;>
    simp [pointIndices,candidateAt,vec,v0,v2,v5,v10,v11,v12,v13,v14,v15]
#print axioms coordinate_recipe_sound
end ThomsonN10.Local.Certificates.IntervalCircuit
