import Uniform5.CompositionStageOneInputs

/-! The clipped geometric domain, as well as closure, survives reindexing. -/
noncomputable section
namespace Uniform5.Composition
open Set

noncomputable def finiteClosureDomain {n : ℕ} (ρ : ℝ) (d α : Fin n → ℝ) (s : ℝ) : Prop :=
  0 < 1 - ρ ^ 2 * s ^ 2 ∧
    (∀ i, 0 < Real.sqrt (1 - cyclePolarCosine ρ (d i) s ^ 2)) ∧
    ∀ i, closureArgument ρ (d i) (d (finRotate n i)) (α i) s ∈ Icc (-1) 1

theorem closureArgument_swap (ρ a b α s : ℝ) :
    closureArgument ρ a b α s = closureArgument ρ b a α s := by
  simp only [closureArgument, mul_comm]

theorem finiteClosureDomain_reindex {n : ℕ} (ρ : ℝ) (d α : Fin n → ℝ) (s : ℝ)
    (c f : Equiv.Perm (Fin n))
    (hinc : ∀ i, (c i = f i ∧ c (finRotate n i) = finRotate n (f i)) ∨
      (c i = finRotate n (f i) ∧ c (finRotate n i) = f i)) :
    finiteClosureDomain ρ (d ∘ c) (α ∘ f) s ↔ finiteClosureDomain ρ d α s := by
  have harg (i : Fin n) :
      closureArgument ρ ((d ∘ c) i) ((d ∘ c) (finRotate n i)) ((α ∘ f) i) s =
        closureArgument ρ (d (f i)) (d (finRotate n (f i))) (α (f i)) s := by
    rcases hinc i with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · simp only [Function.comp_apply, h₁, h₂]
    · simp only [Function.comp_apply, h₁, h₂]
      exact closureArgument_swap _ _ _ _ _
  constructor
  · rintro ⟨hbase, hden, hangle⟩
    refine ⟨hbase, ?_, ?_⟩
    · intro i
      simpa only [Function.comp_apply, c.apply_symm_apply] using hden (c.symm i)
    · intro i
      have hh := hangle (f.symm i)
      rwa [harg, f.apply_symm_apply] at hh
  · rintro ⟨hbase, hden, hangle⟩
    refine ⟨hbase, fun i => hden (c i), ?_⟩
    intro i
    rw [harg]
    exact hangle (f i)

namespace CyclicWord
variable {n : ℕ} [NeZero n] {FacetName Cell : Type*}

noncomputable def domain (W : CyclicWord n FacetName Cell) (k : ℕ)
    (F : FacetName → ℝ) (C : Cell → ℝ) (s : ℝ) : Prop :=
  finiteClosureDomain (unitPolygonRadius k)
    (fun i => Real.sqrt (C (W.cell i) ^ 2 - unitPolygonRadius k ^ 2))
    (fun i => facetWordAngle k (F (W.facet i)) (C (W.cell i))
      (C (W.cell (finRotate n i)))) s

theorem domain_rotate (W : CyclicWord n FacetName Cell) (t : Fin n) (k : ℕ)
    (F : FacetName → ℝ) (C : Cell → ℝ) (s : ℝ) :
    (W.rotate t).domain k F C s ↔ W.domain k F C s := by
  unfold domain
  have heq : (fun i : Fin n => facetWordAngle k (F ((W.rotate t).facet i))
      (C ((W.rotate t).cell i)) (C ((W.rotate t).cell (finRotate n i)))) =
      fun i : Fin n => facetWordAngle k (F (W.facet (i + t)))
        (C (W.cell (i + t))) (C (W.cell (finRotate n (i + t)))) := by
    funext i
    have hh : finRotate n i + t = finRotate n (i + t) := by
      simp only [finRotate_eq_add_one]
      abel
    simp only [rotate, hh]
  rw [heq]
  apply finiteClosureDomain_reindex (unitPolygonRadius k)
    (fun i => Real.sqrt (C (W.cell i) ^ 2 - unitPolygonRadius k ^ 2))
    (fun i => facetWordAngle k (F (W.facet i)) (C (W.cell i))
      (C (W.cell (finRotate n i)))) s (Equiv.addRight t) (Equiv.addRight t)
  intro i
  left
  refine ⟨rfl, ?_⟩
  change finRotate n i + t = finRotate n (i + t)
  simp only [finRotate_eq_add_one]
  abel

theorem domain_reverse (W : CyclicWord n FacetName Cell) (k : ℕ)
    (F : FacetName → ℝ) (C : Cell → ℝ) (s : ℝ) :
    W.reverse.domain k F C s ↔ W.domain k F C s := by
  unfold domain
  have heq : (fun i : Fin n => facetWordAngle k (F (W.reverse.facet i))
      (C (W.reverse.cell i)) (C (W.reverse.cell (finRotate n i)))) =
      fun i : Fin n => facetWordAngle k (F (W.facet (-(i + 1))))
        (C (W.cell (-(i + 1)))) (C (W.cell (finRotate n (-(i + 1))))) := by
    funext i
    simp only [reverse, finRotate_eq_add_one]
    have hh : -(i + 1) + 1 = -i := by abel
    rw [hh]
    exact facetWordAngle_swap _ _ _ _
  rw [heq]
  apply finiteClosureDomain_reindex (unitPolygonRadius k)
    (fun i => Real.sqrt (C (W.cell i) ^ 2 - unitPolygonRadius k ^ 2))
    (fun i => facetWordAngle k (F (W.facet i)) (C (W.cell i))
      (C (W.cell (finRotate n i)))) s (Equiv.neg (Fin n))
    ((Equiv.addRight (1 : Fin n)).trans (Equiv.neg (Fin n)))
  intro i
  right
  constructor
  · change -i = finRotate n (-(i + 1))
    rw [finRotate_eq_add_one]
    abel
  · change -(finRotate n i) = -(i + 1)
    rw [finRotate_eq_add_one]

theorem domain_iff_of_reindex {U V : CyclicWord n FacetName Cell}
    (h : Relation.EqvGen ReindexStep U V) (k : ℕ)
    (F : FacetName → ℝ) (C : Cell → ℝ) (s : ℝ) :
    U.domain k F C s ↔ V.domain k F C s := by
  induction h with
  | rel U V h =>
    rcases h with ⟨t, rfl⟩ | rfl
    · exact (domain_rotate U t k F C s).symm
    · exact (domain_reverse U k F C s).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

noncomputable def classDomain (W : Class n FacetName Cell) (k : ℕ)
    (F : FacetName → ℝ) (C : Cell → ℝ) (s : ℝ) : Prop :=
  Quotient.lift (fun V => V.domain k F C s)
    (fun _ _ h => propext (domain_iff_of_reindex h k F C s)) W
end CyclicWord

noncomputable def LibraryCycleClass.domain (c : LibraryCycleClass)
    (N : LibraryNumericalData) (s : ℝ) : Prop :=
  CyclicWord.classDomain c.2.2 c.1.val (intrinsicRadius ∘ N.model)
    (intrinsicRadius ∘ cellTypeModel) s

theorem LibraryCycleWord.domain_iff_of_class {U V : LibraryCycleWord}
    (h : U.classCode = V.classCode) (N : LibraryNumericalData) (s : ℝ) :
    U.Domain N s ↔ V.Domain N s :=
  Iff.of_eq (congrArg (fun c => LibraryCycleClass.domain c N s) h)

end Uniform5.Composition
