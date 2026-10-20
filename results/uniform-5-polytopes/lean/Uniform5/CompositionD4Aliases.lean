import Uniform5.CompositionD4B4Seeds
import Uniform5.CompositionD4Triality

/-! All fifteen D4 aliases in the fixed facet table, proved by explicit
triality and reflection-word identities. -/
noncomputable section
namespace Uniform5.Composition

noncomputable def d4CanonicalBMask (m : Fin 15) : Fin 15 :=
  ![7, 7, 1, 3, 11, 11, 5, 7, 1, 1, 9, 11, 5, 5, 13] m

variable {E : Type*} [PseudoMetricSpace E]

theorem d4_named_b4_canonical (m : Fin 15) (P : Set E) :
    NamedWythoff4Model 2 m P ↔ NamedWythoff4Model 1 (d4CanonicalBMask m) P := by
  fin_cases m
  · change NamedWythoff4Model 2 0 P ↔ NamedWythoff4Model 1 7 P
    exact (d4_named_symmetry_iff d4Triality (Equiv.swap 0 3) d4Triality_roots
      (n := 7) (by decide) P).trans (d4_b4_named_fork_iff (by decide) (by decide) P)
  · change NamedWythoff4Model 2 1 P ↔ NamedWythoff4Model 1 7 P
    exact (d4_named_symmetry_iff (d4ForkSwap.trans d4Triality) ((Equiv.swap 2 3).trans (Equiv.swap 0 3)) d4ForkTriality_roots
      (n := 7) (by decide) P).trans (d4_b4_named_fork_iff (by decide) (by decide) P)
  · change NamedWythoff4Model 2 2 P ↔ NamedWythoff4Model 1 1 P
    exact d4_b4_named_fork_iff (by decide) (by decide) P
  · change NamedWythoff4Model 2 3 P ↔ NamedWythoff4Model 1 3 P
    exact d4_b4_named_fork_iff (by decide) (by decide) P
  · change NamedWythoff4Model 2 4 P ↔ NamedWythoff4Model 1 11 P
    exact (d4_named_symmetry_iff d4Triality (Equiv.swap 0 3) d4Triality_roots
      (n := 11) (by decide) P).trans (d4_b4_named_fork_iff (by decide) (by decide) P)
  · change NamedWythoff4Model 2 5 P ↔ NamedWythoff4Model 1 11 P
    exact (d4_named_symmetry_iff (d4ForkSwap.trans d4Triality) ((Equiv.swap 2 3).trans (Equiv.swap 0 3)) d4ForkTriality_roots
      (n := 11) (by decide) P).trans (d4_b4_named_fork_iff (by decide) (by decide) P)
  · change NamedWythoff4Model 2 6 P ↔ NamedWythoff4Model 1 5 P
    exact d4_b4_named_fork_iff (by decide) (by decide) P
  · change NamedWythoff4Model 2 7 P ↔ NamedWythoff4Model 1 7 P
    exact d4_b4_named_fork_iff (by decide) (by decide) P
  · change NamedWythoff4Model 2 8 P ↔ NamedWythoff4Model 1 1 P
    exact (d4_named_symmetry_iff (d4ForkSwap.trans d4Triality) ((Equiv.swap 2 3).trans (Equiv.swap 0 3)) d4ForkTriality_roots
      (n := 2) (by decide) P).trans (d4_b4_named_fork_iff (by decide) (by decide) P)
  · change NamedWythoff4Model 2 9 P ↔ NamedWythoff4Model 1 1 P
    exact (d4_named_symmetry_iff d4Triality (Equiv.swap 0 3) d4Triality_roots
      (n := 2) (by decide) P).trans (d4_b4_named_fork_iff (by decide) (by decide) P)
  · change NamedWythoff4Model 2 10 P ↔ NamedWythoff4Model 1 9 P
    exact d4_b4_named_fork_iff (by decide) (by decide) P
  · change NamedWythoff4Model 2 11 P ↔ NamedWythoff4Model 1 11 P
    exact d4_b4_named_fork_iff (by decide) (by decide) P
  · change NamedWythoff4Model 2 12 P ↔ NamedWythoff4Model 1 5 P
    exact (d4_named_symmetry_iff (d4ForkSwap.trans d4Triality) ((Equiv.swap 2 3).trans (Equiv.swap 0 3)) d4ForkTriality_roots
      (n := 6) (by decide) P).trans (d4_b4_named_fork_iff (by decide) (by decide) P)
  · change NamedWythoff4Model 2 13 P ↔ NamedWythoff4Model 1 5 P
    exact (d4_named_symmetry_iff d4Triality (Equiv.swap 0 3) d4Triality_roots
      (n := 6) (by decide) P).trans (d4_b4_named_fork_iff (by decide) (by decide) P)
  · change NamedWythoff4Model 2 14 P ↔ NamedWythoff4Model 1 13 P
    exact d4_b4_named_fork_iff (by decide) (by decide) P

noncomputable def d4AliasPairs : List (Fin 15 × Fin 15) :=
  [(2, 1), (8, 1), (9, 1), (3, 3), (6, 5), (12, 5), (13, 5),
   (0, 7), (1, 7), (7, 7), (10, 9), (4, 11), (5, 11), (11, 11), (14, 13)]

theorem d4AliasPairs_table :
    d4AliasPairs.map (fun p => (FacetLibraryName.wythoff 2 p.1,
      FacetLibraryName.wythoff 1 p.2)) =
      facetAliasTable.filter (fun p => match p.1 with | .wythoff d _ => d == 2 | _ => false) := by decide

theorem d4_aliases_geometric {m n : Fin 15} (hmn : (m, n) ∈ d4AliasPairs)
    (P : Set E) : FacetLibraryModel (.wythoff 2 m) P ↔ FacetLibraryModel (.wythoff 1 n) P := by
  have hn : d4CanonicalBMask m = n := by
    revert m n
    decide
  rw [← hn]
  exact d4_named_b4_canonical m P

end Uniform5.Composition
