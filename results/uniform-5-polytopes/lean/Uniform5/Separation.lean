import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Max
import Mathlib.Tactic
import Mathlib.Logic.Relation

open Set
open scoped RealInnerProductSpace

namespace Uniform5

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An edge is a nondegenerate segment exposed in the convex hull. -/
def IsEdge (V : Finset E) (v w : E) : Prop :=
  v ∈ V ∧ w ∈ V ∧ v ≠ w ∧ IsExposed ℝ (convexHull ℝ (V : Set E)) (segment ℝ v w)

/-- A linear functional attaining its maximum at exactly two generators
exposes precisely their segment in the convex hull. -/
theorem exposes_segment {S : Set E} {v w : E} (hv : v ∈ S) (hw : w ∈ S)
    (L : E →L[ℝ] ℝ) (b : ℝ) (hvL : L v = b) (hwL : L w = b)
    (hL : ∀ x ∈ S, L x ≤ b)
    (hstrict : ∀ x ∈ S, L x = b → x = v ∨ x = w) :
    IsExposed ℝ (convexHull ℝ S) (segment ℝ v w) := by
  have hconv : Convex ℝ {x : E | L x ≤ b ∧ (L x = b → x ∈ segment ℝ v w)} := by
    intro x hx y hy a d ha hd had
    dsimp only [Set.mem_setOf_eq] at hx hy ⊢
    simp only [map_add, map_smul, smul_eq_mul]
    have hle : a * L x + d * L y ≤ b := by
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hx.1),
        mul_nonneg hd (sub_nonneg.mpr hy.1), congrArg (fun t : ℝ => t * b) had]
    refine ⟨hle, ?_⟩
    intro heq
    by_cases ha0 : a = 0
    · have hd1 : d = 1 := by linarith
      simpa [ha0, hd1] using hy.2 (by simpa [ha0, hd1] using heq)
    by_cases hd0 : d = 0
    · have ha1 : a = 1 := by linarith
      simpa [hd0, ha1] using hx.2 (by simpa [hd0, ha1] using heq)
    have hab : a * b + d * b = b := by nlinarith [congrArg (fun t : ℝ => t * b) had]
    have hxEq : L x = b := by
      by_contra hn
      have hlt : L x < b := lt_of_le_of_ne hx.1 hn
      have hp := mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) (sub_pos.mpr hlt)
      nlinarith [mul_nonneg hd (sub_nonneg.mpr hy.1)]
    have hyEq : L y = b := by
      have : d * (L y - b) = 0 := by nlinarith
      have := (mul_eq_zero.mp this).resolve_left hd0
      linarith
    exact (convex_segment v w) (hx.2 hxEq) (hy.2 hyEq) ha hd had
  have hHull : ∀ x ∈ convexHull ℝ S, L x ≤ b ∧ (L x = b → x ∈ segment ℝ v w) :=
    convexHull_min (by
      intro x hx
      refine ⟨hL x hx, fun heq => ?_⟩
      rcases hstrict x hx heq with h | h
      · simpa [h] using (left_mem_segment ℝ v w)
      · simpa [h] using (right_mem_segment ℝ v w)) hconv
  have hseg : ∀ x ∈ segment ℝ v w, L x = b := by
    intro x hx
    rcases hx with ⟨a, d, ha, hd, had, rfl⟩
    simp only [map_add, map_smul, smul_eq_mul, hvL, hwL]
    nlinarith [congrArg (fun t : ℝ => t * b) had]
  intro _
  refine ⟨L, ?_⟩
  ext x
  constructor
  · intro hx
    exact ⟨segment_subset_convexHull hv hw hx, fun y hy => by
      rw [hseg x hx]
      exact (hHull y hy).1⟩
  · rintro ⟨hx, hmax⟩
    apply (hHull x hx).2
    have := hmax v (subset_convexHull ℝ S hv)
    rw [hvL] at this
    exact le_antisymm (hHull x hx).1 this

/-- The nearest-vertex separation lemma, with arbitrary sphere centre.
No full-dimensionality or vertex transitivity is needed. -/
theorem nearest_isEdge (V : Finset E) {c v w : E} {R : ℝ}
    (hsphere : ∀ x ∈ V, ‖x - c‖ ^ 2 = R ^ 2)
    (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hnearest : ∀ x ∈ V, x ≠ v → dist v w ≤ dist v x) :
    IsEdge V v w := by
  let L : E →L[ℝ] ℝ := innerSL ℝ (v + w - (2 : ℝ) • c)
  have identity (x : E) (hx : x ∈ V) :
      2 * (L v - L x) = dist v x ^ 2 + dist w x ^ 2 - dist v w ^ 2 := by
    have hvS := hsphere v hv
    have hwS := hsphere w hw
    have hxS := hsphere x hx
    simp only [norm_sub_sq_real] at hvS hwS hxS
    simp only [L, innerSL_apply, inner_sub_left, inner_add_left,
      real_inner_smul_left, dist_eq_norm, norm_sub_sq_real,
      real_inner_self_eq_norm_sq]
    rw [real_inner_comm v c, real_inner_comm x c, real_inner_comm v w]
    nlinarith
  have hwL : L w = L v := by
    have := identity w hw
    simp only [dist_self, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      sub_self, add_zero] at this
    linarith
  have hstrict (x : E) (hx : x ∈ V) (hxv : x ≠ v) (hxw : x ≠ w) : L x < L v := by
    have hn := hnearest x hx hxv
    have hp : 0 < dist w x := dist_pos.mpr hxw.symm
    have hid := identity x hx
    nlinarith [sq_nonneg (dist v x - dist v w), dist_nonneg (x := v) (y := w)]
  refine ⟨hv, hw, hvw, exposes_segment hv hw L (L v) rfl hwL ?_ ?_⟩
  · intro x hx
    by_cases hxv : x = v
    · simp [hxv]
    by_cases hxw : x = w
    · simp [hxw, hwL]
    exact le_of_lt (hstrict x hx hxv hxw)
  · intro x hx heq
    by_cases hxv : x = v
    · exact Or.inl hxv
    by_cases hxw : x = w
    · exact Or.inr hxw
    exact False.elim ((ne_of_lt (hstrict x hx hxv hxw)) heq)

/-- A closest pair across a cut of a cospherical finite set is an exposed
edge: each other point is at least as far from one of the endpoints as the
endpoints are from each other. This supplies a geometric connectivity proof. -/
theorem pair_min_isEdge (V : Finset E) {c v w : E} {R : ℝ}
    (hsphere : ∀ x ∈ V, ‖x - c‖ ^ 2 = R ^ 2)
    (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hnearest : ∀ x ∈ V, x ≠ v → x ≠ w →
      dist v w ≤ dist v x ∨ dist v w ≤ dist w x) :
    IsEdge V v w := by
  let L : E →L[ℝ] ℝ := innerSL ℝ (v + w - (2 : ℝ) • c)
  have identity (x : E) (hx : x ∈ V) :
      2 * (L v - L x) = dist v x ^ 2 + dist w x ^ 2 - dist v w ^ 2 := by
    have hvS := hsphere v hv
    have hwS := hsphere w hw
    have hxS := hsphere x hx
    simp only [norm_sub_sq_real] at hvS hwS hxS
    simp only [L, innerSL_apply, inner_sub_left, inner_add_left,
      real_inner_smul_left, dist_eq_norm, norm_sub_sq_real,
      real_inner_self_eq_norm_sq]
    rw [real_inner_comm v c, real_inner_comm x c, real_inner_comm v w]
    nlinarith
  have hwL : L w = L v := by
    have := identity w hw
    simp only [dist_self, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      sub_self, add_zero] at this
    linarith
  have hstrict (x : E) (hx : x ∈ V) (hxv : x ≠ v) (hxw : x ≠ w) : L x < L v := by
    have hn := hnearest x hx hxv hxw
    have hp : 0 < dist w x := dist_pos.mpr hxw.symm
    have hp' : 0 < dist v x := dist_pos.mpr hxv.symm
    have hid := identity x hx
    rcases hn with hn | hn
    · nlinarith [sq_nonneg (dist v x - dist v w), dist_nonneg (x := v) (y := w)]
    · nlinarith [sq_nonneg (dist w x - dist v w), dist_nonneg (x := v) (y := w)]
  refine ⟨hv, hw, hvw, exposes_segment hv hw L (L v) rfl hwL ?_ ?_⟩
  · intro x hx
    by_cases hxv : x = v
    · simp [hxv]
    by_cases hxw : x = w
    · simp [hxw, hwL]
    exact le_of_lt (hstrict x hx hxv hxw)
  · intro x hx heq
    by_cases hxv : x = v
    · exact Or.inl hxv
    by_cases hxw : x = w
    · exact Or.inr hxw
    exact False.elim ((ne_of_lt (hstrict x hx hxv hxw)) heq)

/-- Unit edges force separation of all distinct generators. -/
theorem unit_edges_separated (V : Finset E) {c : E} {R : ℝ}
    (hsphere : ∀ x ∈ V, ‖x - c‖ ^ 2 = R ^ 2)
    (hunit : ∀ v w, IsEdge V v w → dist v w = 1)
    {v x : E} (hv : v ∈ V) (hx : x ∈ V) (hvx : v ≠ x) :
    1 ≤ dist v x := by
  classical
  have hne : (V.erase v).Nonempty := ⟨x, Finset.mem_erase.mpr ⟨hvx.symm, hx⟩⟩
  obtain ⟨w, hw, hmin⟩ := (V.erase v).exists_min_image (fun y => dist v y) hne
  have hwV := (Finset.mem_erase.mp hw).2
  have hwv := (Finset.mem_erase.mp hw).1
  have hedge := nearest_isEdge V hsphere hv hwV hwv.symm (by
    intro y hy hyv
    exact hmin y (Finset.mem_erase.mpr ⟨hyv, hy⟩))
  rw [← hunit v w hedge]
  exact hmin x (Finset.mem_erase.mpr ⟨hvx.symm, hx⟩)

/-- In the unit-edge case, distance one is equivalent to adjacency. -/
theorem isEdge_iff_dist_eq_one (V : Finset E) {c : E} {R : ℝ}
    (hsphere : ∀ x ∈ V, ‖x - c‖ ^ 2 = R ^ 2)
    (hunit : ∀ v w, IsEdge V v w → dist v w = 1)
    {v w : E} (hv : v ∈ V) (hw : w ∈ V) :
    IsEdge V v w ↔ dist v w = 1 := by
  refine ⟨hunit v w, fun h => ?_⟩
  have hvw : v ≠ w := by intro heq; simp [heq] at h
  apply nearest_isEdge V hsphere hv hw hvw
  intro x hx hxv
  rw [h]
  exact unit_edges_separated V hsphere hunit hv hx hxv.symm

/-- The actual exposed-edge graph of a finite cospherical set is connected.
A disconnected reachability cut would have a closest cross pair, whose
exposed segment is an edge crossing that cut. -/
theorem cospherical_edge_graph_connected (V : Finset E) {c : E} {R : ℝ}
    (hsphere : ∀ x ∈ V, ‖x - c‖ ^ 2 = R ^ 2)
    {r s : E} (hr : r ∈ V) (hs : s ∈ V) :
    Relation.ReflTransGen (IsEdge V) r s := by
  classical
  by_contra hnot
  let reachable := fun x => Relation.ReflTransGen (IsEdge V) r x
  let pairs := (V ×ˢ V).filter (fun p => reachable p.1 ∧ ¬reachable p.2)
  have hpairs : pairs.Nonempty := ⟨(r, s), by
    simp only [pairs, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hr, hs⟩, Relation.ReflTransGen.refl, hnot⟩⟩
  obtain ⟨p, hp, hmin⟩ := pairs.exists_min_image (fun p => dist p.1 p.2) hpairs
  have hmem : p.1 ∈ V ∧ p.2 ∈ V := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1)
  have hreach : reachable p.1 ∧ ¬reachable p.2 := (Finset.mem_filter.mp hp).2
  have hpne : p.1 ≠ p.2 := by intro he; exact hreach.2 (he ▸ hreach.1)
  have hedge := pair_min_isEdge V hsphere hmem.1 hmem.2 hpne (by
    intro x hx _ _
    by_cases hxr : reachable x
    · right
      have hpair : (x, p.2) ∈ pairs := by
        simp only [pairs, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hx, hmem.2⟩, hxr, hreach.2⟩
      simpa only [dist_comm x p.2] using hmin (x, p.2) hpair
    · left
      have hpair : (p.1, x) ∈ pairs := by
        simp only [pairs, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hmem.1, hx⟩, hreach.1, hxr⟩
      exact hmin (p.1, x) hpair)
  exact hreach.2 (hreach.1.tail hedge)

end Uniform5
