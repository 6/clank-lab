import Uniform5.CompositionD4Aliases
import Uniform5.CompositionB4F4Aliases
import Uniform5.CompositionCubeProductAliases
import Uniform5.CompositionTriangularAntiprism

/-! Every one of the paper's thirty-three facet aliases is geometric.
The finite lookup therefore reduces all 214 concrete names to the 181
canonical names without adding an agreement or alias premise. -/
noncomputable section
namespace Uniform5.Composition

/-- The proved geometric groups cover exactly the literal alias table. -/
theorem facetAliasTable_partition : facetAliasTable.toFinset =
    ((a4AliasPairs.map (fun (p : Fin 15 × Fin 15) => (FacetLibraryName.wythoff 0 p.1,
        FacetLibraryName.wythoff 0 p.2))) ++
      (f4AliasPairs.map (fun (p : Fin 15 × Fin 15) => (FacetLibraryName.wythoff 3 p.1,
        FacetLibraryName.wythoff 3 p.2))) ++
      (d4AliasPairs.map (fun (p : Fin 15 × Fin 15) => (FacetLibraryName.wythoff 2 p.1,
        FacetLibraryName.wythoff 1 p.2))) ++
      (b4F4AliasPairs.map (fun (p : Fin 15 × Fin 15) => (FacetLibraryName.wythoff 3 p.1,
        FacetLibraryName.wythoff 1 p.2))) ++
      [(FacetLibraryName.polyhedronPrism 2, FacetLibraryName.wythoff 1 0),
       (FacetLibraryName.duoprism ⟨(1, 1), by decide⟩, FacetLibraryName.wythoff 1 0),
       (FacetLibraryName.antiprismPrism 0, FacetLibraryName.polyhedronPrism 1)]).toFinset := by decide

variable {E : Type*} [NormedAddCommGroup E]

/-- All thirty-three identities hold for actual models in any ambient
normed additive group, including facets embedded in the five-dimensional polytope. -/
theorem facetAliasTable_geometric {p : FacetLibraryName × FacetLibraryName}
    (hp : p ∈ facetAliasTable) (P : Set E) :
    FacetLibraryModel p.1 P ↔ FacetLibraryModel p.2 P := by
  simp only [facetAliasTable, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact a4_aliases_geometric (by decide) P
  · exact a4_aliases_geometric (by decide) P
  · exact a4_aliases_geometric (by decide) P
  · exact a4_aliases_geometric (by decide) P
  · exact a4_aliases_geometric (by decide) P
  · exact a4_aliases_geometric (by decide) P
  · exact cubePrism_b4_alias
  · exact squareDuoprism_b4_alias
  · exact d4_aliases_geometric (by decide) P
  · exact d4_aliases_geometric (by decide) P
  · exact d4_aliases_geometric (by decide) P
  · exact d4_aliases_geometric (by decide) P
  · exact b4_f4_aliases_geometric (by decide) P
  · exact b4_f4_aliases_geometric (by decide) P
  · exact d4_aliases_geometric (by decide) P
  · exact d4_aliases_geometric (by decide) P
  · exact d4_aliases_geometric (by decide) P
  · exact d4_aliases_geometric (by decide) P
  · exact d4_aliases_geometric (by decide) P
  · exact d4_aliases_geometric (by decide) P
  · exact d4_aliases_geometric (by decide) P
  · exact b4_f4_aliases_geometric (by decide) P
  · exact b4_f4_aliases_geometric (by decide) P
  · exact d4_aliases_geometric (by decide) P
  · exact d4_aliases_geometric (by decide) P
  · exact d4_aliases_geometric (by decide) P
  · exact d4_aliases_geometric (by decide) P
  · exact b4_f4_aliases_geometric (by decide) P
  · exact b4_f4_aliases_geometric (by decide) P
  · exact f4_aliases_geometric (by decide) P
  · exact f4_aliases_geometric (by decide) P
  · exact f4_aliases_geometric (by decide) P
  · exact triangularAntiprismPrism_octahedron_alias

/-- The previously exposed geometric obligation is now a theorem. -/
theorem facetAliasGeometry_proved : FacetAliasGeometry := by
  intro p hp P
  exact facetAliasTable_geometric hp P

/-- Lookup preserves the actual geometric model predicate in both directions. -/
theorem canonicalFacetName_model_iff (n : FacetLibraryName) (P : Set E) :
    FacetLibraryModel n P ↔ FacetLibraryModel (canonicalFacetName n) P := by
  classical
  cases h : facetAliasTable.find? (fun p => p.1 == n) with
  | none => simp [canonicalFacetName, h]
  | some p =>
    have hp : p ∈ facetAliasTable := List.mem_of_find?_eq_some h
    have hn : p.1 = n := by simpa using List.find?_some h
    simpa [canonicalFacetName, h, hn] using facetAliasTable_geometric hp P

noncomputable def canonicalFacetIndex (n : FacetLibraryName) : CanonicalFacetName :=
  ⟨canonicalFacetName n, canonicalFacetName_idempotent n⟩

theorem canonicalFacetIndex_model_iff (n : FacetLibraryName) (P : Set E) :
    FacetLibraryModel n P ↔ FacetLibraryModel (canonicalFacetIndex n).val P :=
  canonicalFacetName_model_iff n P

/-- Coverage by the 214 concrete names is exactly coverage by the 181
canonical names. The reduction has no unproved geometric premise. -/
theorem facetLibraryModel_exists_canonical (P : Set E) :
    (∃ n : FacetLibraryName, FacetLibraryModel n P) ↔
      ∃ n : CanonicalFacetName, FacetLibraryModel n.val P := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨canonicalFacetIndex n, (canonicalFacetIndex_model_iff n P).mp hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n.val, hn⟩

end Uniform5.Composition
