import Uniform5.CompositionB4F4Seeds
import Uniform5.CompositionF4DiagramAliases

/-! Six B4/F4 aliases from the triality fixed slice and the already proved
F4 diagram reversal. -/
noncomputable section
namespace Uniform5.Composition

noncomputable def b4F4AliasPairs : List (Fin 15 × Fin 15) :=
  [(0, 3), (7, 3), (1, 9), (3, 9), (2, 13), (11, 13)]

theorem b4F4AliasPairs_table :
    b4F4AliasPairs.map (fun p => (FacetLibraryName.wythoff 3 p.1,
      FacetLibraryName.wythoff 1 p.2)) =
      facetAliasTable.filter (fun p => match p.1, p.2 with
        | .wythoff d _, .wythoff e _ => d == 3 && e == 1
        | _, _ => false) := by decide

variable {E : Type*} [PseudoMetricSpace E]

theorem b4_f4_aliases_geometric {m n : Fin 15} (hmn : (m, n) ∈ b4F4AliasPairs)
    (P : Set E) : FacetLibraryModel (.wythoff 3 m) P ↔ FacetLibraryModel (.wythoff 1 n) P := by
  have h7 : NamedWythoff4Model 3 7 P ↔ NamedWythoff4Model 1 3 P :=
    f4_b4_named_slice_iff (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) P
  have h3 : NamedWythoff4Model 3 3 P ↔ NamedWythoff4Model 1 9 P :=
    f4_b4_named_slice_iff (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) P
  have h11 : NamedWythoff4Model 3 11 P ↔ NamedWythoff4Model 1 13 P :=
    f4_b4_named_slice_iff (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) P
  simp only [b4F4AliasPairs, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, Prod.mk.injEq] at hmn
  rcases hmn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (show NamedWythoff4Model 3 0 P ↔ NamedWythoff4Model 3 7 P from
      ⟨f4_named_reversal (by decide), f4_named_reversal (by decide)⟩).trans h7
  · exact h7
  · exact (show NamedWythoff4Model 3 1 P ↔ NamedWythoff4Model 3 3 P from
      ⟨f4_named_reversal (by decide), f4_named_reversal (by decide)⟩).trans h3
  · exact h3
  · exact (show NamedWythoff4Model 3 2 P ↔ NamedWythoff4Model 3 11 P from
      ⟨f4_named_reversal (by decide), f4_named_reversal (by decide)⟩).trans h11
  · exact h11

end Uniform5.Composition
