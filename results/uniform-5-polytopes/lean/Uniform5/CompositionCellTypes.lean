import Uniform5.CompositionCycleLabelsConstructor

/-! Semantic cell types are actual intrinsic congruence classes. -/
noncomputable section
namespace Uniform5.Composition
open Set

noncomputable def cellTypeSetoid : Setoid (Set (Space 3)) where
  r := Congruent
  iseqv := ⟨congruent_refl, fun h => congruent_symm h, fun h h' => congruent_trans h h'⟩

/-- Cell types identify whole metric hulls, rather than radii or signatures. -/
abbrev CellType := Quotient cellTypeSetoid

noncomputable def cellType (P : Set (Space 3)) : CellType := Quotient.mk cellTypeSetoid P

noncomputable def cellTypeModel (c : CellType) : Set (Space 3) := Quotient.out c

theorem cellType_eq_iff {P Q : Set (Space 3)} :
    cellType P = cellType Q ↔ Congruent P Q := Quotient.eq

theorem cellType_model_congruent (P : Set (Space 3)) :
    Congruent P (cellTypeModel (cellType P)) := by
  apply cellType_eq_iff.mp
  exact (Quotient.out_eq (cellType P)).symm

theorem cellType_of_model (c : CellType) : cellType (cellTypeModel c) = c :=
  Quotient.out_eq c

theorem cellType_radius (P : Set (Space 3)) :
    intrinsicRadius (cellTypeModel (cellType P)) = intrinsicRadius P :=
  (intrinsicRadius_cross_congruent (cellType_model_congruent P)).symm

theorem modelPolygonWord_cell_congruent {K : Set (Space 4)} {k : ℕ}
    {A B A' B' : Set (Space 3)} (hA : Congruent A A') (hB : Congruent B B') :
    ModelPolygonWord K k A B ↔ ModelPolygonWord K k A' B' := by
  constructor
  · rintro ⟨G, C, D, hG, hC, hD, hGC, hGD, hCD, hCA, hDB⟩
    exact ⟨G, C, D, hG, hC, hD, hGC, hGD, hCD,
      congruent_trans hCA hA, congruent_trans hDB hB⟩
  · rintro ⟨G, C, D, hG, hC, hD, hGC, hGD, hCD, hCA, hDB⟩
    exact ⟨G, C, D, hG, hC, hD, hGC, hGD, hCD,
      congruent_trans hCA (congruent_symm hA), congruent_trans hDB (congruent_symm hB)⟩

/-- Choice of a representative changes neither incidence nor the cell type. -/
theorem modelPolygonWord_cellType {K : Set (Space 4)} {k : ℕ}
    (A B : Set (Space 3)) :
    ModelPolygonWord K k (cellTypeModel (cellType A)) (cellTypeModel (cellType B)) ↔
      ModelPolygonWord K k A B :=
  (modelPolygonWord_cell_congruent (cellType_model_congruent A)
    (cellType_model_congruent B)).symm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_actual_cellType {P : Set E} (hP : FinitePolytope P)
    (hd : affineDimension P = 3) : ∃ c : CellType, Congruent P (cellTypeModel c) := by
  obtain ⟨_, Q, _, hQP, _, _⟩ := exists_finitePolytope_intrinsic_model P hP 3 hd
  exact ⟨cellType Q, congruent_trans (congruent_symm hQP) (cellType_model_congruent Q)⟩

/-- Only facet model coverage is needed to label an actual cycle: its cell
types are constructed from actual three-dimensional hulls, without a
separate list or a classification assumption for those cells. -/
theorem actual_cycle_exists_type_labels {P G : Set (Space 5)}
    (D : ActualPolygonCycle P G) (hP : UnitUniform 5 P) {k : ℕ}
    (hG : PolygonFace P G k) {FacetName : Type*} (F : FacetName → Set (Space 4))
    (hF : ∀ i, ∃ f, Congruent (D.facet i) (F f)) :
    ∃ L : CycleModelLabels D CellType FacetName,
      L.cellModel = cellTypeModel ∧ L.facetModel = F ∧
      L.cellLabel D.length = L.cellLabel 0 := by
  apply exists_closed_cycleModelLabels D cellTypeModel F ?_ hF
  rintro K ⟨i, rfl⟩
  exact exists_actual_cellType (uniform_finitePolytope (D.cell_unitUniform hP hG i).1)
    (D.cell_dimension i)

end Uniform5.Composition
