import Uniform5.CompositionCycleQuotient

/-! Flatness and the maximum facet radius depend on the cyclic word class. -/
noncomputable section
namespace Uniform5.Composition.CyclicWord
variable {n : ℕ} [NeZero n] {FacetName Cell : Type*}

noncomputable def angleSum (W : CyclicWord n FacetName Cell) (k : ℕ)
    (F : FacetName → ℝ) (C : Cell → ℝ) : ℝ :=
  ∑ i, facetWordAngle k (F (W.facet i)) (C (W.cell i)) (C (W.cell (finRotate n i)))

noncomputable def maxRadius (W : CyclicWord n FacetName Cell) (F : FacetName → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (F ∘ W.facet)

theorem angleSum_rotate (W : CyclicWord n FacetName Cell) (t : Fin n) (k : ℕ)
    (F : FacetName → ℝ) (C : Cell → ℝ) :
    (W.rotate t).angleSum k F C = W.angleSum k F C := by
  unfold angleSum
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
  exact Equiv.sum_comp (Equiv.addRight t) (fun i =>
    facetWordAngle k (F (W.facet i)) (C (W.cell i)) (C (W.cell (finRotate n i))))

theorem angleSum_reverse (W : CyclicWord n FacetName Cell) (k : ℕ)
    (F : FacetName → ℝ) (C : Cell → ℝ) :
    W.reverse.angleSum k F C = W.angleSum k F C := by
  unfold angleSum
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
  exact Equiv.sum_comp ((Equiv.addRight (1 : Fin n)).trans (Equiv.neg (Fin n)))
    (fun i => facetWordAngle k (F (W.facet i)) (C (W.cell i))
      (C (W.cell (finRotate n i))))

theorem maxRadius_rotate (W : CyclicWord n FacetName Cell) (t : Fin n)
    (F : FacetName → ℝ) : (W.rotate t).maxRadius F = W.maxRadius F :=
  cycle_max_radius_reindex (F ∘ W.facet) (Equiv.addRight t)

theorem maxRadius_reverse (W : CyclicWord n FacetName Cell) (F : FacetName → ℝ) :
    W.reverse.maxRadius F = W.maxRadius F :=
  cycle_max_radius_reindex (F ∘ W.facet)
    ((Equiv.addRight (1 : Fin n)).trans (Equiv.neg (Fin n)))

theorem angleSum_eq_of_reindex {U V : CyclicWord n FacetName Cell}
    (h : Relation.EqvGen ReindexStep U V) (k : ℕ)
    (F : FacetName → ℝ) (C : Cell → ℝ) : U.angleSum k F C = V.angleSum k F C := by
  induction h with
  | rel U V h =>
    rcases h with ⟨t, rfl⟩ | rfl
    · exact (angleSum_rotate U t k F C).symm
    · exact (angleSum_reverse U k F C).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem maxRadius_eq_of_reindex {U V : CyclicWord n FacetName Cell}
    (h : Relation.EqvGen ReindexStep U V) (F : FacetName → ℝ) :
    U.maxRadius F = V.maxRadius F := by
  induction h with
  | rel U V h =>
    rcases h with ⟨t, rfl⟩ | rfl
    · exact (maxRadius_rotate U t F).symm
    · exact (maxRadius_reverse U F).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

noncomputable def classAngleSum (W : Class n FacetName Cell) (k : ℕ)
    (F : FacetName → ℝ) (C : Cell → ℝ) : ℝ :=
  Quotient.lift (fun V => V.angleSum k F C)
    (fun _ _ h => angleSum_eq_of_reindex h k F C) W

noncomputable def classMaxRadius (W : Class n FacetName Cell) (F : FacetName → ℝ) : ℝ :=
  Quotient.lift (fun V => V.maxRadius F) (fun _ _ h => maxRadius_eq_of_reindex h F) W

end Uniform5.Composition.CyclicWord
