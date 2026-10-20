import Uniform5.CompositionWedgeInput

/-! Small kernel checks for finite W parameters, excluded boundary parameters and the
geometric realization guard. No computation certificate is used. -/
noncomputable section
namespace Uniform5.Composition.Wedge

example : parameterChord none = 2 := rfl
example : parameterChord (some 4) = Real.sqrt 2 := CaseB.chord_four

example : atInfinity none (.unpairedI [4,4,4]) := by simp [atInfinity, finiteParameters]
example : atInfinity (some 17) (.pairedI none [4,4]) := by simp [atInfinity, finiteParameters]
example : atInfinity none (.pairedII (some 17)) := by simp [atInfinity, finiteParameters]
example : ¬ finiteParameters (some 17) (.pairedI none [4,4]) := by simp [atInfinity, finiteParameters]
example : finiteParameters (some 17) (.unpairedIII 3 5) := by simp [atInfinity, finiteParameters]
example : finiteParameters (some 17) (.pairedII (some 19)) := by simp [atInfinity, finiteParameters]

example : finRotate 3 (finRotate 3 (finRotate 3 (0 : Fin 3))) = 0 := by decide

/-- For this parameter pair, no choice of ambient limiting geometry
can enter the finite W domain. -/
theorem audit_boundary_excluded (p1 : CaseB.P1) (F : Geometry) :
    ¬ RealizesWFan p1 (some 17) (.pairedI none [4,4]) F := by
  intro h
  exact h.1 (by simp [atInfinity])

/-- Every W application carries the finite guard explicitly. -/
theorem realizesWFan_finite {p1 : CaseB.P1} {n : Parameter}
    {f : CaseB.WFan} {F : Geometry} (h : RealizesWFan p1 n f F) :
    ¬ atInfinity n f := h.1

/-- Algebra of the retained inequality in rescaled coordinates.
Here z is the rescaled third coordinate. No limit interchange is assumed. -/
theorem rescaled_constraint {s t₁ t₅ z d : ℝ} (hs : 0 < s)
    (hsphere : t₁ / s + z + t₅ = 1) (hside : d ≤ z) :
    t₁ ≤ s * (1 - t₅ - d) := by
  rw [mul_comm s]
  apply (div_le_iff₀ hs).mp
  linarith

/-- The point p=e1 violates the retained constraint whenever
0<s<1; for example, s=sin(pi/17). -/
theorem audit_point_excluded {s : ℝ} (hs : s < 1) :
    ¬ ((1 : ℝ) ≤ s * (1 - 0 - |0|)) := by
  simpa using not_le_of_gt hs

/-- A zero normal is not a finite W geometry, regardless of labels. -/
theorem realizesFiniteFan_normal_unit {n : Parameter} {f : CaseB.WFan} {F : Geometry}
    (h : RealizesFiniteFan n f F) : ‖F.normal‖ = 1 := by
  cases f <;> obtain ⟨_, h⟩ := h <;> exact h.1

example {n : Parameter} {f : CaseB.WFan} {F : Geometry}
    (hzero : F.normal = 0) : ¬ RealizesFiniteFan n f F := by
  intro h
  have hh := realizesFiniteFan_normal_unit h
  rw [hzero, norm_zero] at hh
  norm_num at hh

end Uniform5.Composition.Wedge
