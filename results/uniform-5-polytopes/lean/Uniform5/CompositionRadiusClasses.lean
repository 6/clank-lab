import Uniform5.CompositionCycleFilter
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Finset.Max

/-!
# Radius classes are actual overlap components

Intervals meeting at an endpoint are joined, as in the paper. A common
actual radius forces all associated intervals into one class. Its finite
hull contains every interval in that component.
-/
noncomputable section
namespace Uniform5.Composition
open Set

/-- A nonempty closed real interval, including exact point intervals. -/
structure ClosedRadiusInterval where
  lo : ℝ
  hi : ℝ
  ordered : lo ≤ hi

noncomputable def ClosedRadiusInterval.carrier (I : ClosedRadiusInterval) : Set ℝ := Icc I.lo I.hi

/-- The graph in the paper's definition of radius classes. -/
noncomputable def radiusOverlapGraph {ι : Type*} (I : ι → ClosedRadiusInterval) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ ((I i).carrier ∩ (I j).carrier).Nonempty
  symm := by rintro i j ⟨hne, x, hi, hj⟩; exact ⟨hne.symm, x, hj, hi⟩
  loopless := by intro i h; exact h.1 rfl

/-- Two actual interval witnesses for the same radius lie in the same class. -/
theorem radius_class_eq_of_common_point {ι : Type*} (I : ι → ClosedRadiusInterval)
    {i j : ι} {R : ℝ} (hi : R ∈ (I i).carrier) (hj : R ∈ (I j).carrier) :
    (radiusOverlapGraph I).connectedComponentMk i = (radiusOverlapGraph I).connectedComponentMk j := by
  by_cases hij : i = j
  · rw [hij]
  · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj ⟨hij, R, hi, hj⟩

/-- The interval assignment need not be injective; all occurrences share
one class whenever their intervals contain the actual common radius. -/
theorem radius_classes_of_common_radius {ι κ : Type*} (I : ι → ClosedRadiusInterval)
    (intervalOf : κ → ι) (R : ℝ) (hR : ∀ c, R ∈ (I (intervalOf c)).carrier) (c₀ : κ) :
    ∀ c, (radiusOverlapGraph I).connectedComponentMk (intervalOf c) =
      (radiusOverlapGraph I).connectedComponentMk (intervalOf c₀) := by
  intro c
  exact radius_class_eq_of_common_point I (hR c) (hR c₀)

variable {ι : Type*} [Fintype ι]

noncomputable def radiusClassMembers (I : ι → ClosedRadiusInterval)
    (c : (radiusOverlapGraph I).ConnectedComponent) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => (radiusOverlapGraph I).connectedComponentMk i = c)

@[simp] theorem mem_radiusClassMembers (I : ι → ClosedRadiusInterval)
    (c : (radiusOverlapGraph I).ConnectedComponent) (i : ι) :
    i ∈ radiusClassMembers I c ↔ (radiusOverlapGraph I).connectedComponentMk i = c := by
  classical
  simp [radiusClassMembers]

theorem radiusClassMembers_nonempty (I : ι → ClosedRadiusInterval)
    (c : (radiusOverlapGraph I).ConnectedComponent) : (radiusClassMembers I c).Nonempty := by
  obtain ⟨i, hi⟩ := c.exists_rep
  exact ⟨i, (mem_radiusClassMembers I c i).mpr hi⟩

/-- Literal endpoint hull of a finite overlap component. -/
noncomputable def radiusClassHull (I : ι → ClosedRadiusInterval)
    (c : (radiusOverlapGraph I).ConnectedComponent) : ClosedRadiusInterval := by
  classical
  let M := radiusClassMembers I c
  have hM := radiusClassMembers_nonempty I c
  let lows := M.image (fun i => (I i).lo)
  let highs := M.image (fun i => (I i).hi)
  have hlo : lows.Nonempty := hM.image _
  have hhi : highs.Nonempty := hM.image _
  refine ⟨lows.min' hlo, highs.max' hhi, ?_⟩
  obtain ⟨i, hi⟩ := hM
  exact (Finset.min'_le _ _ (Finset.mem_image_of_mem (fun j => (I j).lo) hi)).trans
    ((I i).ordered.trans (Finset.le_max' _ _ (Finset.mem_image_of_mem (fun j => (I j).hi) hi)))

/-- No root witness leaves the hull when intervals are collected into classes. -/
theorem radius_interval_subset_class_hull (I : ι → ClosedRadiusInterval)
    (c : (radiusOverlapGraph I).ConnectedComponent) {i : ι}
    (hi : (radiusOverlapGraph I).connectedComponentMk i = c) :
    (I i).carrier ⊆ (radiusClassHull I c).carrier := by
  classical
  intro R hR
  have hm := (mem_radiusClassMembers I c i).mpr hi
  constructor
  · exact (Finset.min'_le _ _ (Finset.mem_image_of_mem (fun j => (I j).lo) hm)).trans hR.1
  · exact hR.2.trans (Finset.le_max' _ _ (Finset.mem_image_of_mem (fun j => (I j).hi) hm))

/-- Endpoint contact counts as overlap; open-interval semantics would fail
this sanity example. -/
theorem radius_endpoint_contact :
    let I : Bool → ClosedRadiusInterval := fun b =>
      if b then ⟨2, 3, by norm_num⟩ else ⟨1, 2, by norm_num⟩
    (radiusOverlapGraph I).connectedComponentMk false =
      (radiusOverlapGraph I).connectedComponentMk true := by
  dsimp only
  apply radius_class_eq_of_common_point (R := 2)
  · norm_num [ClosedRadiusInterval.carrier]
  · norm_num [ClosedRadiusInterval.carrier]

end Uniform5.Composition
