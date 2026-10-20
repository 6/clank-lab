import Uniform5.CompositionCycleReindex

/-! Cyclic words modulo exactly the generated rotations and reversals. -/
noncomputable section
namespace Uniform5.Composition

/-- Cell i precedes facet i, which joins cell i to cell i+1. -/
structure CyclicWord (n : ℕ) (FacetName Cell : Type*) where
  facet : Fin n → FacetName
  cell : Fin n → Cell

namespace CyclicWord
variable {n : ℕ} [NeZero n] {FacetName Cell : Type*}

noncomputable def rotate (W : CyclicWord n FacetName Cell) (t : Fin n) :
    CyclicWord n FacetName Cell :=
  ⟨fun i => W.facet (i + t), fun i => W.cell (i + t)⟩

noncomputable def reverse (W : CyclicWord n FacetName Cell) : CyclicWord n FacetName Cell :=
  ⟨fun i => W.facet (-(i + 1)), fun i => W.cell (-i)⟩

/-- Only a cyclic shift or reversal is an elementary identification. -/
noncomputable def ReindexStep (U V : CyclicWord n FacetName Cell) : Prop :=
  (∃ t, V = U.rotate t) ∨ V = U.reverse

noncomputable def wordSetoid : Setoid (CyclicWord n FacetName Cell) :=
  Relation.EqvGen.setoid ReindexStep

abbrev Class (n : ℕ) [NeZero n] (FacetName Cell : Type*) :=
  Quotient (wordSetoid (n := n) (FacetName := FacetName) (Cell := Cell))

noncomputable def closure (W : CyclicWord n FacetName Cell) (k : ℕ)
    (facetRadius : FacetName → ℝ) (cellRadius : Cell → ℝ) (s : ℝ) : ℝ :=
  finiteWordClosure k (facetRadius ∘ W.facet) (cellRadius ∘ W.cell) s

theorem closure_rotate (W : CyclicWord n FacetName Cell) (t : Fin n) (k : ℕ)
    (F : FacetName → ℝ) (C : Cell → ℝ) (s : ℝ) :
    (W.rotate t).closure k F C s = W.closure k F C s :=
  finiteWordClosure_rotate k (F ∘ W.facet) (C ∘ W.cell) s t

theorem closure_reverse (W : CyclicWord n FacetName Cell) (k : ℕ)
    (F : FacetName → ℝ) (C : Cell → ℝ) (s : ℝ) :
    W.reverse.closure k F C s = W.closure k F C s :=
  finiteWordClosure_reverse k (F ∘ W.facet) (C ∘ W.cell) s

theorem closure_eq_of_reindex {U V : CyclicWord n FacetName Cell}
    (h : Relation.EqvGen ReindexStep U V) (k : ℕ)
    (F : FacetName → ℝ) (C : Cell → ℝ) (s : ℝ) :
    U.closure k F C s = V.closure k F C s := by
  induction h with
  | rel U V h =>
    rcases h with ⟨t, rfl⟩ | rfl
    · exact (closure_rotate U t k F C s).symm
    · exact (closure_reverse U k F C s).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The entire closure function is well-defined on rotation/reversal
classes, not just its zero set or one chosen numerical root. -/
noncomputable def classClosure (W : Class n FacetName Cell) (k : ℕ)
    (F : FacetName → ℝ) (C : Cell → ℝ) (s : ℝ) : ℝ :=
  Quotient.lift (fun V => V.closure k F C s)
    (fun _ _ h => closure_eq_of_reindex h k F C s) W

/-- Semantic word incidence: every facet has the prescribed polygon
between its two endpoint cell models. -/
noncomputable def Valid (occurs : FacetName → Cell → Cell → Prop)
    (W : CyclicWord n FacetName Cell) : Prop :=
  ∀ i, occurs (W.facet i) (W.cell i) (W.cell (finRotate n i))

theorem valid_rotate {occurs : FacetName → Cell → Cell → Prop}
    {W : CyclicWord n FacetName Cell} (h : W.Valid occurs) (t : Fin n) :
    (W.rotate t).Valid occurs := by
  intro i
  have hh := h (i + t)
  change occurs (W.facet (i + t)) (W.cell (i + t)) (W.cell (finRotate n i + t))
  have heq : finRotate n i + t = finRotate n (i + t) := by
    simp only [finRotate_eq_add_one]
    abel
  rwa [heq]

theorem valid_reverse {occurs : FacetName → Cell → Cell → Prop}
    (hsymm : ∀ f a b, occurs f a b → occurs f b a)
    {W : CyclicWord n FacetName Cell} (h : W.Valid occurs) : W.reverse.Valid occurs := by
  intro i
  have hh := h (-(i + 1))
  have heq : finRotate n (-(i + 1)) = -i := by rw [finRotate_eq_add_one]; abel
  rw [heq] at hh
  change occurs (W.facet (-(i + 1))) (W.cell (-i)) (W.cell (-(finRotate n i)))
  rw [finRotate_eq_add_one]
  exact hsymm _ _ _ hh

theorem reverse_reverse (W : CyclicWord n FacetName Cell) : W.reverse.reverse = W := by
  cases W with
  | mk F C =>
    dsimp only [reverse]
    congr 1
    · funext i
      have hh : -(-(i + 1) + 1) = i := by abel
      simp only [reverse, hh]
    · funext i
      simp only [reverse, neg_neg]

theorem rotate_inverse (W : CyclicWord n FacetName Cell) (t : Fin n) :
    (W.rotate t).rotate (-t) = W := by
  cases W with
  | mk F C =>
    dsimp only [rotate]
    congr 1 <;> funext i <;> simp

theorem valid_rotate_iff {occurs : FacetName → Cell → Cell → Prop}
    (W : CyclicWord n FacetName Cell) (t : Fin n) :
    (W.rotate t).Valid occurs ↔ W.Valid occurs := by
  constructor
  · intro h
    simpa only [rotate_inverse] using valid_rotate h (-t)
  · exact fun h => valid_rotate h t

theorem valid_reverse_iff {occurs : FacetName → Cell → Cell → Prop}
    (hsymm : ∀ f a b, occurs f a b → occurs f b a)
    (W : CyclicWord n FacetName Cell) : W.reverse.Valid occurs ↔ W.Valid occurs := by
  constructor
  · intro h
    simpa only [reverse_reverse] using valid_reverse hsymm h
  · exact valid_reverse hsymm

theorem valid_iff_of_reindex {occurs : FacetName → Cell → Cell → Prop}
    (hsymm : ∀ f a b, occurs f a b → occurs f b a)
    {U V : CyclicWord n FacetName Cell} (h : Relation.EqvGen ReindexStep U V) :
    U.Valid occurs ↔ V.Valid occurs := by
  induction h with
  | rel U V h =>
    rcases h with ⟨t, rfl⟩ | rfl
    · exact (valid_rotate_iff U t).symm
    · exact (valid_reverse_iff hsymm U).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Actual model incidence descends to the same quotient as closure. -/
noncomputable def classValid (occurs : FacetName → Cell → Cell → Prop)
    (hsymm : ∀ f a b, occurs f a b → occurs f b a)
    (W : Class n FacetName Cell) : Prop :=
  Quotient.lift (fun V => V.Valid occurs)
    (fun _ _ h => propext (valid_iff_of_reindex hsymm h)) W

/-- Chosen representatives are connected by the stated reindexing
relation; choosing one does not assume coverage of a library enumeration. -/
theorem representative_related (W : CyclicWord n FacetName Cell) :
    Relation.EqvGen ReindexStep W (Quotient.out (Quotient.mk wordSetoid W)) :=
  @Quotient.exact (CyclicWord n FacetName Cell) wordSetoid W
    (Quotient.out (Quotient.mk wordSetoid W)) (Quotient.out_eq _).symm

end CyclicWord
end Uniform5.Composition
