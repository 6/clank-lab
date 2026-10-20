import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Tactic

open Set Finset
open scoped BigOperators Topology

namespace Uniform5

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A zero centroid of a finite spanning family lies in the interior of its convex hull. -/
theorem zero_mem_interior_convexHull_of_sum_zero {ι : Type*} [Fintype ι]
    (p : ι → E) (hsum : ∑ i, p i = 0)
    (hne : (interior (convexHull ℝ (range p))).Nonempty) :
    (0 : E) ∈ interior (convexHull ℝ (range p)) := by
  by_contra hzero
  let C := convexHull ℝ (range p)
  have hc : Convex ℝ C := convex_convexHull ℝ _
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hc.interior isOpen_interior hzero
  have hle : ∀ x ∈ C, f x ≤ 0 := by
    intro x hx
    have hclosed : IsClosed {x : E | f x ≤ 0} := isClosed_le f.continuous continuous_const
    have hsub : interior C ⊆ {x : E | f x ≤ 0} := by
      intro y hy
      simpa using (hf y hy).le
    have hclosure : closure (interior C) = closure C :=
      hc.closure_interior_eq_closure_of_nonempty_interior hne
    exact (closure_minimal hsub hclosed) (hclosure ▸ subset_closure hx)
  have hvertex : ∀ i, f (p i) = 0 := by
    have heq : ∑ i, f (p i) = 0 := by rw [← map_sum, hsum, map_zero]
    exact fun i => (Finset.sum_eq_zero_iff_of_nonpos
      (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
        hle (p j) (subset_convexHull ℝ _ (mem_range_self j)))).mp heq i (mem_univ i)
  have hker : C ⊆ {x : E | f x = 0} := by
    apply convexHull_min
    · rintro _ ⟨i, rfl⟩
      exact hvertex i
    · exact (LinearMap.ker f.toLinearMap).convex
  obtain ⟨y, hy⟩ := hne
  have hyzero := hker (interior_subset hy)
  change f y = 0 at hyzero
  have hyneg := hf y hy
  simp [hyzero] at hyneg

/-- The zero centroid of any nonempty finite family is relatively interior to its convex hull.
No affine-independence or full-dimensionality assumption is needed. -/
theorem zero_mem_intrinsicInterior_convexHull_of_sum_zero [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → E) (hsum : ∑ i, p i = 0) :
    (0 : E) ∈ intrinsicInterior ℝ (convexHull ℝ (range p)) := by
  classical
  let S := Submodule.span ℝ (range p)
  let q : ι → S := fun i => ⟨p i, Submodule.subset_span (mem_range_self i)⟩
  have hsumq : ∑ i, q i = 0 := by
    apply Subtype.ext
    simpa [q] using hsum
  have hzero : (0 : S) ∈ convexHull ℝ (range q) := by
    have h := (Finset.univ : Finset ι).centerMass_mem_convexHull
      (w := fun _ => (1 : ℝ)) (z := q) (fun _ _ => zero_le_one)
      (by simpa using (Nat.cast_pos.mpr (Fintype.card_pos : 0 < Fintype.card ι) :
        (0 : ℝ) < Fintype.card ι)) (fun i _ => mem_range_self i)
    simpa [Finset.centerMass, hsumq] using h
  have hspan : Submodule.span ℝ (range q) = ⊤ := by
    apply Submodule.map_injective_of_injective S.injective_subtype
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
    rfl
  have haffine : affineSpan ℝ (range q) = ⊤ := by
    apply SetLike.coe_injective
    rw [← affineSpan_insert_eq_affineSpan ℝ
      ((affineSpan_convexHull (𝕜 := ℝ) (range q)) ▸ subset_affineSpan ℝ _ hzero),
      affineSpan_insert_zero, hspan]
    rfl
  have hint : (0 : S) ∈ interior (convexHull ℝ (range q)) :=
    zero_mem_interior_convexHull_of_sum_zero q hsumq
      (interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr haffine)
  have hrel := interior_subset_intrinsicInterior (𝕜 := ℝ) hint
  have hmap := Set.mem_image_of_mem S.subtypeₗᵢ.toAffineIsometry hrel
  rw [← S.subtypeₗᵢ.toAffineIsometry.image_intrinsicInterior] at hmap
  have himage : S.subtypeₗᵢ.toAffineIsometry '' convexHull ℝ (range q) =
      convexHull ℝ (range p) := by
    change S.subtype '' convexHull ℝ (range q) = _
    rw [S.subtype.image_convexHull, ← Set.range_comp]
    rfl
  change (0 : E) ∈ intrinsicInterior ℝ
    (S.subtypeₗᵢ.toAffineIsometry '' convexHull ℝ (range q)) at hmap
  rwa [himage] at hmap

/-- A finite arithmetic mean is relatively interior in the convex hull of the family. -/
theorem mean_mem_intrinsicInterior_convexHull [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → E) (c : E)
    (hsum : ∑ i, p i = (Fintype.card ι : ℝ) • c) :
    c ∈ intrinsicInterior ℝ (convexHull ℝ (range p)) := by
  let q : ι → E := fun i => p i - c
  have hsumq : ∑ i, q i = 0 := by
    simp [q, Finset.sum_sub_distrib, hsum, ← Nat.cast_smul_eq_nsmul ℝ]
  have hzero := zero_mem_intrinsicInterior_convexHull_of_sum_zero q hsumq
  let f := (AffineIsometryEquiv.constVAdd ℝ E c).toAffineIsometry
  have hmap := Set.mem_image_of_mem f hzero
  rw [← f.image_intrinsicInterior] at hmap
  have himage : f '' convexHull ℝ (range q) = convexHull ℝ (range p) := by
    rw [← f.coe_toAffineMap, f.toAffineMap.image_convexHull, ← Set.range_comp]
    congr 1
    ext i
    simp [f, q, vadd_eq_add]
  have hf0 : f 0 = c := by simp [f, vadd_eq_add]
  rw [hf0] at hmap
  rwa [himage] at hmap

/-- Finset version of the relative-interior mean theorem. -/
theorem finset_mean_mem_intrinsicInterior_convexHull [FiniteDimensional ℝ E]
    (V : Finset E) (hV : V.Nonempty) (c : E)
    (hsum : ∑ x ∈ V, x = (V.card : ℝ) • c) :
    c ∈ intrinsicInterior ℝ (convexHull ℝ (V : Set E)) := by
  letI : Nonempty V := hV.to_subtype
  have h := mean_mem_intrinsicInterior_convexHull (fun x : V => (x : E)) c
    (by simpa [Finset.sum_attach V (fun x => x)] using hsum)
  simpa using h

/-- Any ambient interior point in an affine section is relatively interior in the section. -/
theorem interior_mem_intrinsicInterior_section {C : Set E} (A : AffineSubspace ℝ E)
    {x : E} (hx : x ∈ interior C) (hA : x ∈ A) :
    x ∈ intrinsicInterior ℝ (C ∩ (A : Set E)) := by
  let S := affineSpan ℝ (C ∩ (A : Set E))
  have hxS : x ∈ S := subset_affineSpan ℝ _ ⟨interior_subset hx, hA⟩
  refine ⟨⟨x, hxS⟩, ?_, rfl⟩
  have hSA : S ≤ A := affineSpan_le.mpr fun y hy => hy.2
  have heq : ((↑) ⁻¹' (C ∩ (A : Set E)) : Set S) = (↑) ⁻¹' C := by
    ext y
    exact and_iff_left (hSA y.property)
  rw [heq]
  apply mem_interior_iff_mem_nhds.mpr
  exact (continuous_subtype_val.tendsto _).eventually
    (mem_interior_iff_mem_nhds.mp hx)

/-- The entire open axial interval between a negative vertex average and a vertex is interior,
provided zero is interior. This includes negative values of `t`. -/
theorem axial_point_mem_interior {C : Set E} (hc : Convex ℝ C)
    (hzero : (0 : E) ∈ interior C) {v : E} (hv : v ∈ C)
    {a t : ℝ} (ha : a < 0) (hq : a • v ∈ C) (hat : a < t) (ht : t < 1) :
    t • v ∈ interior C := by
  by_cases htn : 0 ≤ t
  · have := hc.combo_interior_self_mem_interior hzero hv
      (sub_pos.mpr ht) htn (sub_add_cancel 1 t)
    simpa using this
  · have htneg : t < 0 := lt_of_not_ge htn
    have hratio0 : 0 ≤ t / a := le_of_lt (div_pos_of_neg_of_neg htneg ha)
    have hratio1 : t / a < 1 := (div_lt_one_of_neg ha).mpr hat
    have := hc.combo_interior_self_mem_interior hzero hq
      (sub_pos.mpr hratio1) hratio0 (sub_add_cancel 1 (t / a))
    simpa [smul_smul, div_mul_cancel₀ t ha.ne] using this

end Uniform5
