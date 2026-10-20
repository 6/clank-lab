import Uniform5.CompositionCycleWords

/-! Exact rotation and reversal invariance of the geometric closure word. -/
noncomputable section
namespace Uniform5.Composition
open scoped BigOperators

/-- One summand of the literal closure function. -/
noncomputable def closureSummand (ρ a b α s : ℝ) : ℝ :=
  Real.arccos ((Real.cos α - cyclePolarCosine ρ a s * cyclePolarCosine ρ b s) /
    (Real.sqrt (1 - cyclePolarCosine ρ a s ^ 2) *
      Real.sqrt (1 - cyclePolarCosine ρ b s ^ 2)))

theorem closureSummand_swap (ρ a b α s : ℝ) :
    closureSummand ρ a b α s = closureSummand ρ b a α s := by
  simp only [closureSummand, mul_comm]

theorem facetWordAngle_swap (k : ℕ) (R a b : ℝ) :
    facetWordAngle k R a b = facetWordAngle k R b a := by
  exact add_comm _ _

/-- Finite cyclic form, equivalent to the actual natural-index cycle. -/
noncomputable def finiteCycleClosure {n : ℕ} (ρ : ℝ) (d α : Fin n → ℝ) (s : ℝ) : ℝ :=
  (∑ i, closureSummand ρ (d i) (d (finRotate n i)) (α i) s) - 2 * Real.pi

theorem finiteCycleClosure_eq {n : ℕ} (hn : 2 ≤ n) (ρ : ℝ) (d α : ℕ → ℝ)
    (hcycle : d n = d 0) (s : ℝ) :
    finiteCycleClosure ρ (fun i : Fin n => d i) (fun i => α i) s =
      cycleClosureFunction n ρ d α s := by
  unfold finiteCycleClosure cycleClosureFunction
  simp_rw [cycle_apply_finRotate hn d hcycle]
  exact congrArg (fun z => z - 2 * Real.pi)
    (Fin.sum_univ_eq_sum_range (fun i => closureSummand ρ (d i) (d (i + 1)) (α i) s) n)

/-- Reindexing edges and vertices consistently preserves the whole function,
including reversal, since each summand is symmetric in its endpoint heights. -/
theorem finiteCycleClosure_reindex {n : ℕ} (ρ : ℝ) (d α : Fin n → ℝ) (s : ℝ)
    (c f : Equiv.Perm (Fin n))
    (hinc : ∀ i, (c i = f i ∧ c (finRotate n i) = finRotate n (f i)) ∨
      (c i = finRotate n (f i) ∧ c (finRotate n i) = f i)) :
    finiteCycleClosure ρ (d ∘ c) (α ∘ f) s = finiteCycleClosure ρ d α s := by
  unfold finiteCycleClosure
  congr 1
  calc
    ∑ i, closureSummand ρ ((d ∘ c) i) ((d ∘ c) (finRotate n i)) ((α ∘ f) i) s =
        ∑ i, closureSummand ρ (d (f i)) (d (finRotate n (f i))) (α (f i)) s := by
      apply Finset.sum_congr rfl
      intro i _
      rcases hinc i with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [Function.comp_apply, h1, h2]
      · simp only [Function.comp_apply, h1, h2]
        exact closureSummand_swap _ _ _ _ _
    _ = _ := Equiv.sum_comp f (fun i => closureSummand ρ (d i) (d (finRotate n i)) (α i) s)

theorem finRotate_eq_add_one {n : ℕ} [NeZero n] (i : Fin n) : finRotate n i = i + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact finRotate_succ_apply i

/-- Any cyclic shift of the starting point preserves closure exactly. -/
theorem finiteCycleClosure_rotate {n : ℕ} [NeZero n]
    (ρ : ℝ) (d α : Fin n → ℝ) (s : ℝ) (t : Fin n) :
    finiteCycleClosure ρ (fun i => d (i + t)) (fun i => α (i + t)) s =
      finiteCycleClosure ρ d α s := by
  apply finiteCycleClosure_reindex ρ d α s (Equiv.addRight t) (Equiv.addRight t)
  intro i
  left
  constructor
  · rfl
  · change finRotate n i + t = finRotate n (i + t)
    simp only [finRotate_eq_add_one]
    abel

/-- Reversal fixes cell zero and sends the edge at i to the edge at -(i+1). -/
theorem finiteCycleClosure_reverse {n : ℕ} [NeZero n]
    (ρ : ℝ) (d α : Fin n → ℝ) (s : ℝ) :
    finiteCycleClosure ρ (fun i => d (-i)) (fun i => α (-(i + 1))) s =
      finiteCycleClosure ρ d α s := by
  let c := Equiv.neg (Fin n)
  let f := (Equiv.addRight (1 : Fin n)).trans c
  apply finiteCycleClosure_reindex ρ d α s c f
  intro i
  right
  constructor
  · change -i = finRotate n (-(i + 1))
    rw [finRotate_eq_add_one]
    abel
  · change -(finRotate n i) = -(i + 1)
    rw [finRotate_eq_add_one]

/-- A cycle expressed entirely by intrinsic facet and cell radii. -/
noncomputable def finiteWordClosure {n : ℕ} (k : ℕ) (facetRadius cellRadius : Fin n → ℝ)
    (s : ℝ) : ℝ :=
  finiteCycleClosure (unitPolygonRadius k)
    (fun i => Real.sqrt (cellRadius i ^ 2 - (unitPolygonRadius k) ^ 2))
    (fun i => facetWordAngle k (facetRadius i) (cellRadius i) (cellRadius (finRotate n i))) s

theorem finiteWordClosure_rotate {n : ℕ} [NeZero n] (k : ℕ)
    (F C : Fin n → ℝ) (s : ℝ) (t : Fin n) :
    finiteWordClosure k (fun i => F (i + t)) (fun i => C (i + t)) s =
      finiteWordClosure k F C s := by
  unfold finiteWordClosure
  have heq : (fun i : Fin n => facetWordAngle k (F (i + t)) (C (i + t)) (C (finRotate n i + t))) =
      (fun i => facetWordAngle k (F (i + t)) (C (i + t)) (C (finRotate n (i + t)))) := by
    funext i
    have hh : finRotate n i + t = finRotate n (i + t) := by
      simp only [finRotate_eq_add_one]
      abel
    rw [hh]
  rw [heq]
  exact finiteCycleClosure_rotate (unitPolygonRadius k)
    (fun i => Real.sqrt (C i ^ 2 - (unitPolygonRadius k) ^ 2))
    (fun i => facetWordAngle k (F i) (C i) (C (finRotate n i))) s t

/-- Reversal includes the cell-label swap in each word; angle symmetry
proves this is exact even when the polygon occurrences are in distinct orbits. -/
theorem finiteWordClosure_reverse {n : ℕ} [NeZero n] (k : ℕ)
    (F C : Fin n → ℝ) (s : ℝ) :
    finiteWordClosure k (fun i => F (-(i + 1))) (fun i => C (-i)) s =
      finiteWordClosure k F C s := by
  unfold finiteWordClosure
  have heq : (fun i : Fin n => facetWordAngle k (F (-(i + 1))) (C (-i)) (C (-(finRotate n i)))) =
      (fun i => facetWordAngle k (F (-(i + 1))) (C (-(i + 1))) (C (finRotate n (-(i + 1))))) := by
    funext i
    simp only [finRotate_eq_add_one]
    have hh : -(i + 1) + 1 = -i := by abel
    rw [hh]
    exact facetWordAngle_swap _ _ _ _
  rw [heq]
  exact finiteCycleClosure_reverse (unitPolygonRadius k)
    (fun i => Real.sqrt (C i ^ 2 - (unitPolygonRadius k) ^ 2))
    (fun i => facetWordAngle k (F i) (C i) (C (finRotate n i))) s

/-- The maximum facet radius is independent of the cycle's numbering. -/
theorem cycle_max_radius_reindex {ι : Type*} [Fintype ι] [Nonempty ι]
    (F : ι → ℝ) (e : Equiv.Perm ι) :
    Finset.univ.sup' Finset.univ_nonempty (F ∘ e) =
      Finset.univ.sup' Finset.univ_nonempty F := by
  classical
  apply le_antisymm
  · apply (Finset.sup'_le_iff Finset.univ_nonempty _).mpr
    intro i _
    exact Finset.le_sup' F (Finset.mem_univ (e i))
  · apply (Finset.sup'_le_iff Finset.univ_nonempty _).mpr
    intro i _
    have hh := Finset.le_sup' (F ∘ e) (Finset.mem_univ (e.symm i))
    simpa only [Function.comp_apply, e.apply_symm_apply] using hh

/-- The flat/nonflat angle sum likewise depends only on the cyclic word. -/
theorem cycle_angle_sum_reindex {ι : Type*} [Fintype ι]
    (α : ι → ℝ) (e : Equiv.Perm ι) : (∑ i, α (e i)) = ∑ i, α i :=
  Equiv.sum_comp e α

end Uniform5.Composition
