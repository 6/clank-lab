import Uniform5.CompositionClassificationInputs

/-! The exact 214 names and the 33-entry syntactic alias table of the
paper's facet library. Cardinalities and canonicalization are finite kernel
computations. Geometric validity of the alias table is kept as an explicit
unproved proposition, not imported into any theorem. -/
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Uniform5.Composition
open Set

/-- A sorted pair of polygon sizes in the interval 3 through 16. -/
abbrev DuoprismIndex := {p : Fin 14 × Fin 14 // p.1 ≤ p.2}

/-- Five diagrams and fifteen nonempty ring patterns, two exceptions,
eighteen polyhedron prisms, fourteen antiprism prisms, and sorted duoprisms. -/
inductive FacetLibraryName where
  | wythoff (diagram : Fin 5) (rings : Fin 15)
  | exceptional (index : Fin 2)
  | polyhedronPrism (index : Fin 18)
  | antiprismPrism (index : Fin 14)
  | duoprism (index : DuoprismIndex)

/-- Explicit finite coding. The equivalence and finite enumeration are
transparent kernel definitions with no generated runtime implementation. -/
abbrev FacetLibraryCode := (Fin 5 × Fin 15) ⊕ Fin 2 ⊕ Fin 18 ⊕ Fin 14 ⊕ DuoprismIndex

noncomputable def facetLibraryCodeEquiv : FacetLibraryName ≃ FacetLibraryCode where
  toFun
    | .wythoff d m => Sum.inl (d, m)
    | .exceptional i => Sum.inr (Sum.inl i)
    | .polyhedronPrism i => Sum.inr (Sum.inr (Sum.inl i))
    | .antiprismPrism i => Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))
    | .duoprism p => Sum.inr (Sum.inr (Sum.inr (Sum.inr p)))
  invFun
    | Sum.inl (d, m) => .wythoff d m
    | Sum.inr (Sum.inl i) => .exceptional i
    | Sum.inr (Sum.inr (Sum.inl i)) => .polyhedronPrism i
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl i))) => .antiprismPrism i
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr p))) => .duoprism p
  left_inv n := by cases n <;> rfl
  right_inv n := by rcases n with ⟨d, m⟩ | i | i | i | p <;> rfl

noncomputable instance : DecidableEq FacetLibraryName :=
  fun a b => decidable_of_iff (facetLibraryCodeEquiv a = facetLibraryCodeEquiv b)
    facetLibraryCodeEquiv.injective.eq_iff

noncomputable instance : Fintype FacetLibraryName :=
  Fintype.ofEquiv FacetLibraryCode facetLibraryCodeEquiv.symm

/-- The integer is one less than the nonzero four-bit ring mask. Bit 3
is node 0, so index 0 is the source's 0001 and index 7 is 1000. -/
noncomputable def libraryRingSet (m : Fin 15) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => (m.val + 1).testBit (3 - i.val))

theorem libraryRingSet_nonempty (m : Fin 15) : (libraryRingSet m).Nonempty := by
  revert m
  decide

theorem libraryRingSet_bijective :
    Function.Bijective (fun m : Fin 15 =>
      (⟨libraryRingSet m, libraryRingSet_nonempty m⟩ : {J : Finset (Fin 4) // J.Nonempty})) := by
  decide

theorem duoprismIndex_card : Fintype.card DuoprismIndex = 105 := by decide

theorem facetLibraryName_card : Fintype.card FacetLibraryName = 214 := by decide

/-- The ordered table is transcribed from Appendix Names, Table aliases. Each pair is (alias, chosen canonical name). -/
noncomputable def facetAliasTable : List (FacetLibraryName × FacetLibraryName) :=
  [(.wythoff 0 7, .wythoff 0 0),
   (.wythoff 0 3, .wythoff 0 1),
   (.wythoff 0 11, .wythoff 0 2),
   (.wythoff 0 9, .wythoff 0 4),
   (.wythoff 0 13, .wythoff 0 6),
   (.wythoff 0 12, .wythoff 0 10),
   (.polyhedronPrism 2, .wythoff 1 0),
   (.duoprism ⟨(1, 1), by decide⟩, .wythoff 1 0),
   (.wythoff 2 2, .wythoff 1 1),
   (.wythoff 2 8, .wythoff 1 1),
   (.wythoff 2 9, .wythoff 1 1),
   (.wythoff 2 3, .wythoff 1 3),
   (.wythoff 3 0, .wythoff 1 3),
   (.wythoff 3 7, .wythoff 1 3),
   (.wythoff 2 6, .wythoff 1 5),
   (.wythoff 2 12, .wythoff 1 5),
   (.wythoff 2 13, .wythoff 1 5),
   (.wythoff 2 0, .wythoff 1 7),
   (.wythoff 2 1, .wythoff 1 7),
   (.wythoff 2 7, .wythoff 1 7),
   (.wythoff 2 10, .wythoff 1 9),
   (.wythoff 3 1, .wythoff 1 9),
   (.wythoff 3 3, .wythoff 1 9),
   (.wythoff 2 4, .wythoff 1 11),
   (.wythoff 2 5, .wythoff 1 11),
   (.wythoff 2 11, .wythoff 1 11),
   (.wythoff 2 14, .wythoff 1 13),
   (.wythoff 3 2, .wythoff 1 13),
   (.wythoff 3 11, .wythoff 1 13),
   (.wythoff 3 9, .wythoff 3 4),
   (.wythoff 3 13, .wythoff 3 6),
   (.wythoff 3 12, .wythoff 3 10),
   (.antiprismPrism 0, .polyhedronPrism 1)]

/-- Syntactic table lookup only; this definition does not identify hulls. -/
noncomputable def canonicalFacetName (n : FacetLibraryName) : FacetLibraryName :=
  ((facetAliasTable.find? (fun p => p.1 == n)).map Prod.snd).getD n

abbrev CanonicalFacetName := {n : FacetLibraryName // canonicalFacetName n = n}

theorem facetAliasTable_length : facetAliasTable.length = 33 := by decide

theorem facetAliasTable_distinct : (facetAliasTable.map Prod.fst).Nodup := by decide

theorem canonicalFacetName_idempotent (n : FacetLibraryName) :
    canonicalFacetName (canonicalFacetName n) = canonicalFacetName n := by
  revert n
  decide

theorem canonicalFacetName_card : Fintype.card CanonicalFacetName = 181 := by decide

/-- The table accounts for precisely all noncanonical names, once each. -/
theorem facetAliasTable_complete (n : FacetLibraryName) :
    canonicalFacetName n ≠ n ↔ n ∈ facetAliasTable.map Prod.fst := by
  revert n
  decide

theorem facetAliasTable_targets (p : FacetLibraryName × FacetLibraryName)
    (hp : p ∈ facetAliasTable) :
    canonicalFacetName p.1 = p.2 ∧ canonicalFacetName p.2 = p.2 := by
  simp only [facetAliasTable, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

noncomputable def facetNameKind : FacetLibraryName → Fin 5
  | .wythoff _ _ => 0
  | .exceptional _ => 1
  | .polyhedronPrism _ => 2
  | .antiprismPrism _ => 3
  | .duoprism _ => 4

/-- Canonical names by construction family: 45, 2, 17, 13, and 104. -/
theorem canonicalFacetName_family_counts :
    ((Finset.univ : Finset FacetLibraryName).filter (fun n => canonicalFacetName n = n ∧
      facetNameKind n = 0)).card = 45 ∧
    ((Finset.univ : Finset FacetLibraryName).filter (fun n => canonicalFacetName n = n ∧
      facetNameKind n = 1)).card = 2 ∧
    ((Finset.univ : Finset FacetLibraryName).filter (fun n => canonicalFacetName n = n ∧
      facetNameKind n = 2)).card = 17 ∧
    ((Finset.univ : Finset FacetLibraryName).filter (fun n => canonicalFacetName n = n ∧
      facetNameKind n = 3)).card = 13 ∧
    ((Finset.univ : Finset FacetLibraryName).filter (fun n => canonicalFacetName n = n ∧
      facetNameKind n = 4)).card = 104 := by decide

noncomputable section
variable {E : Type*} [PseudoMetricSpace E]

/-- An individual Wythoff name fixes both its diagram and its ring set. -/
noncomputable def NamedWythoff4Model (d : Fin 5) (m : Fin 15) (P : Set E) : Prop :=
  ![∃ x : ModelSpace 5, (∑ i, x i) = 0 ∧
      WythoffSeed rootsA4 (libraryRingSet m) x ∧ Congruent P (WythoffHull rootsA4 x),
    ∃ x : ModelSpace 4, WythoffSeed rootsB4 (libraryRingSet m) x ∧
      Congruent P (WythoffHull rootsB4 x),
    ∃ x : ModelSpace 4, WythoffSeed rootsD4 (libraryRingSet m) x ∧
      Congruent P (WythoffHull rootsD4 x),
    ∃ x : ModelSpace 4, WythoffSeed rootsF4 (libraryRingSet m) x ∧
      Congruent P (WythoffHull rootsF4 x),
    ∃ x : ModelSpace 4, WythoffSeed rootsH4 (libraryRingSet m) x ∧
      Congruent P (WythoffHull rootsH4 x)] d

theorem exists_libraryRingSet {J : Finset (Fin 4)} (hJ : J.Nonempty) :
    ∃ m : Fin 15, libraryRingSet m = J := by
  obtain ⟨m, hm⟩ := libraryRingSet_bijective.2 ⟨J, hJ⟩
  exact ⟨m, congrArg Subtype.val hm⟩

/-- All and only the nonempty ring choices of the five reflection families
occur among the 75 Wythoff names. -/
theorem isWythoff4_iff_named {P : Set E} :
    IsWythoff4 P ↔ ∃ d m, NamedWythoff4Model d m P := by
  constructor
  · intro h
    rcases h with h | h | h | h | h
    · obtain ⟨J, x, hJ, hx⟩ := h
      obtain ⟨m, rfl⟩ := exists_libraryRingSet hJ
      exact ⟨0, m, by simpa [NamedWythoff4Model] using
        (⟨x, hx⟩ : ∃ x, (∑ i, x i) = 0 ∧ WythoffSeed rootsA4 (libraryRingSet m) x ∧
          Congruent P (WythoffHull rootsA4 x))⟩
    · obtain ⟨J, x, hJ, hx⟩ := h
      obtain ⟨m, rfl⟩ := exists_libraryRingSet hJ
      exact ⟨1, m, by simpa [NamedWythoff4Model] using
        (⟨x, hx⟩ : ∃ x, WythoffSeed rootsB4 (libraryRingSet m) x ∧
          Congruent P (WythoffHull rootsB4 x))⟩
    · obtain ⟨J, x, hJ, hx⟩ := h
      obtain ⟨m, rfl⟩ := exists_libraryRingSet hJ
      exact ⟨2, m, by simpa [NamedWythoff4Model] using
        (⟨x, hx⟩ : ∃ x, WythoffSeed rootsD4 (libraryRingSet m) x ∧
          Congruent P (WythoffHull rootsD4 x))⟩
    · obtain ⟨J, x, hJ, hx⟩ := h
      obtain ⟨m, rfl⟩ := exists_libraryRingSet hJ
      exact ⟨3, m, by simpa [NamedWythoff4Model] using
        (⟨x, hx⟩ : ∃ x, WythoffSeed rootsF4 (libraryRingSet m) x ∧
          Congruent P (WythoffHull rootsF4 x))⟩
    · obtain ⟨J, x, hJ, hx⟩ := h
      obtain ⟨m, rfl⟩ := exists_libraryRingSet hJ
      exact ⟨4, m, by simpa [NamedWythoff4Model] using
        (⟨x, hx⟩ : ∃ x, WythoffSeed rootsH4 (libraryRingSet m) x ∧
          Congruent P (WythoffHull rootsH4 x))⟩
  · rintro ⟨d, m, h⟩
    fin_cases d
    · simp only [NamedWythoff4Model, Matrix.cons_val_zero, Matrix.cons_val_succ] at h
      obtain ⟨x, hx⟩ := h
      exact Or.inl ⟨libraryRingSet m, x, libraryRingSet_nonempty m, hx⟩
    · simp only [NamedWythoff4Model, Matrix.cons_val_zero, Matrix.cons_val_succ] at h
      obtain ⟨x, hx⟩ := h
      exact Or.inr (Or.inl ⟨libraryRingSet m, x, libraryRingSet_nonempty m, hx⟩)
    · simp only [NamedWythoff4Model, Matrix.cons_val_zero, Matrix.cons_val_succ] at h
      obtain ⟨x, hx⟩ := h
      exact Or.inr (Or.inr (Or.inl ⟨libraryRingSet m, x, libraryRingSet_nonempty m, hx⟩))
    · simp only [NamedWythoff4Model, Matrix.cons_val_zero, Matrix.cons_val_succ] at h
      obtain ⟨x, hx⟩ := h
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨libraryRingSet m, x, libraryRingSet_nonempty m, hx⟩)))
    · simp only [NamedWythoff4Model, Matrix.cons_val_zero, Matrix.cons_val_succ] at h
      obtain ⟨x, hx⟩ := h
      exact Or.inr (Or.inr (Or.inr (Or.inr (⟨libraryRingSet m, x, libraryRingSet_nonempty m, hx⟩))))

/-- The five Platonic names followed by the thirteen Archimedean names,
using the coordinate library ordering. -/
noncomputable def NamedPolyhedronModel (i : Fin 18) (P : Set (Space 3)) : Prop :=
  if h : i.val < 5 then PlatonicModel ⟨i.val, h⟩ P
  else ArchimedeanModel ⟨i.val - 5, by omega⟩ P

theorem namedPolyhedronModel_coverage (P : Set (Space 3)) :
    (∃ i, NamedPolyhedronModel i P) ↔
      (∃ i, PlatonicModel i P) ∨ (∃ i, ArchimedeanModel i P) := by
  constructor
  · rintro ⟨i, hi⟩
    unfold NamedPolyhedronModel at hi
    split_ifs at hi with h
    · exact Or.inl ⟨_, hi⟩
    · exact Or.inr ⟨_, hi⟩
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · refine ⟨⟨i.val, by omega⟩, ?_⟩
      simpa [NamedPolyhedronModel, i.isLt] using hi
    · refine ⟨⟨i.val + 5, by omega⟩, ?_⟩
      simpa [NamedPolyhedronModel, Nat.not_lt.mpr (show 5 ≤ i.val + 5 by omega)] using hi

/-- Actual coordinate hulls and reflection orbits interpret every name.
The definition does not assert any model's uniformity or completeness. -/
noncomputable def FacetLibraryModel : FacetLibraryName → Set E → Prop
  | .wythoff d m, P => NamedWythoff4Model d m P
  | .exceptional i, P => ![IsSnub24 P, IsGrandAntiprism P] i
  | .polyhedronPrism i, P => ∃ Q : Set (Space 3), NamedPolyhedronModel i Q ∧
      Congruent P (polyhedralPrismModel Q)
  | .antiprismPrism i, P => Congruent P (antiprismPrismModel (i.val + 3))
  | .duoprism p, P => Congruent P (duoprismModel (p.val.1.val + 3) (p.val.2.val + 3))

/-- This is the remaining geometric obligation behind the syntactic table.
It is a proposition only, and is neither proved nor used as a premise here. -/
noncomputable def FacetAliasGeometry : Prop :=
  ∀ p ∈ facetAliasTable, ∀ P : Set (Space 4),
    FacetLibraryModel p.1 P ↔ FacetLibraryModel p.2 P

/-- Concrete normalization check for the B40001 name. -/
theorem cubeCorner4_library_name :
    FacetLibraryModel (.wythoff 1 0) (WythoffHull rootsB4 cubeCorner4) := by
  change ∃ x, WythoffSeed rootsB4 (libraryRingSet 0) x ∧ _
  have hring : libraryRingSet 0 = {3} := by decide
  rw [hring]
  exact ⟨cubeCorner4, cubeCorner4_seed, congruent_refl _⟩

end
end Uniform5.Composition
