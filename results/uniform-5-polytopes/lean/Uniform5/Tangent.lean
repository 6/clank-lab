import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic

/-!
# The tangent-foot uniqueness in Lemma D(2)

These are Euclidean plane facts, independent of polytopes. An orthonormal
frame has its first axis along the line joining the projected ridge point to
the origin. At a fixed distance from the origin, a tangent foot is uniquely
determined by its strict side of that line. The convex-polytope projection
and open-wedge arguments supplying the plane and strict side remain separate
geometric inputs to the congruence theorem.
-/

noncomputable section
namespace Uniform5
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Orthogonality of the radius and the tangent gives the dot product with
the external point. This identity also excludes the radius-zero ambiguity
once the strict-side hypothesis is supplied. -/
theorem tangent_foot_dot {p t : E} {d : ℝ}
    (hradius : ‖t‖ = d) (htangent : ⟪p - t, t⟫ = 0) :
    ⟪p, t⟫ = d ^ 2 := by
  rw [inner_sub_left, real_inner_self_eq_norm_sq, hradius] at htangent
  linarith

/-- The squared transverse coordinate and the radial coordinate are fixed;
requiring the two transverse coordinates to have the same strict sign
selects one of the two tangent feet. -/
theorem tangent_coordinates_unique {r d a b a' b' : ℝ}
    (hr : r ≠ 0) (ha : r * a = d ^ 2) (ha' : r * a' = d ^ 2)
    (hcircle : a ^ 2 + b ^ 2 = d ^ 2)
    (hcircle' : a' ^ 2 + b' ^ 2 = d ^ 2)
    (hside : 0 < b * b') : a = a' ∧ b = b' := by
  have haa : a = a' := mul_left_cancel₀ hr (ha.trans ha'.symm)
  have hbb : b ^ 2 = b' ^ 2 := by rw [haa] at hcircle; linarith
  refine ⟨haa, ?_⟩
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hbb with h | h
  · exact h
  · rw [h] at hside
    nlinarith [sq_nonneg b']

/-- Coordinates and squared length in an orthonormal two-dimensional frame. -/
theorem orthonormal_pair_coordinates {u v : E}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫ = 0)
    (a b : ℝ) :
    ⟪u, a • u + b • v⟫ = a ∧ ⟪v, a • u + b • v⟫ = b ∧
      ‖a • u + b • v‖ ^ 2 = a ^ 2 + b ^ 2 := by
  have hvu : ⟪v, u⟫ = 0 := by rw [real_inner_comm]; exact huv
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hvv : ⟪v, v⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  constructor
  · simp [inner_add_right, real_inner_smul_right, huu, huv]
  constructor
  · simp [inner_add_right, real_inner_smul_right, hvu, hvv]
  · rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, huu, huv, hvu, hvv]
    ring

/-- Tangent-foot uniqueness on a specified strict side of the line `pO`.
Here the projected ridge point is `p = r • u`, with `r ≠ 0`; the plane is
the span of the orthonormal axes `u,v`. The product condition says precisely
that the two feet lie on the same strict side of the first axis. -/
theorem tangent_foot_unique_on_strict_side {u v t t' : E} {r d : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫ = 0) (hr : r ≠ 0)
    (ht : t ∈ Submodule.span ℝ ({u, v} : Set E))
    (ht' : t' ∈ Submodule.span ℝ ({u, v} : Set E))
    (hradius : ‖t‖ = d) (hradius' : ‖t'‖ = d)
    (htangent : ⟪r • u - t, t⟫ = 0)
    (htangent' : ⟪r • u - t', t'⟫ = 0)
    (hside : 0 < ⟪v, t⟫ * ⟪v, t'⟫) : t = t' := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp ht
  obtain ⟨a', b', hab'⟩ := Submodule.mem_span_pair.mp ht'
  have hc := orthonormal_pair_coordinates hu hv huv a b
  have hc' := orthonormal_pair_coordinates hu hv huv a' b'
  rw [hab] at hc
  rw [hab'] at hc'
  have ha := tangent_foot_dot hradius htangent
  have ha' := tangent_foot_dot hradius' htangent'
  rw [real_inner_smul_left, hc.1] at ha
  rw [real_inner_smul_left, hc'.1] at ha'
  have hcircle : a ^ 2 + b ^ 2 = d ^ 2 := by rw [← hc.2.2, hradius]
  have hcircle' : a' ^ 2 + b' ^ 2 = d ^ 2 := by rw [← hc'.2.2, hradius']
  rw [hc.2.1, hc'.2.1] at hside
  obtain ⟨haa, hbb⟩ := tangent_coordinates_unique hr ha ha' hcircle hcircle' hside
  rw [← hab, ← hab', haa, hbb]

/-- Two nonzero transverse coordinates opposite to one common coordinate
have the same strict sign. -/
theorem same_strict_side_of_opposite {x y z : ℝ}
    (hxy : x * y < 0) (hxz : x * z < 0) : 0 < y * z := by
  rcases mul_neg_iff.mp hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rcases mul_neg_iff.mp hxz with ⟨_, hz⟩ | ⟨hx', _⟩
    · exact mul_pos_of_neg_of_neg hy hz
    · linarith
  · rcases mul_neg_iff.mp hxz with ⟨hx', _⟩ | ⟨_, hz⟩
    · linarith
    · exact mul_pos hy hz

/-- The version used by Lemma D(2): two candidate tangent feet at the same
radius, both strictly opposite the existing facet's foot `q`, are equal.
No tangency property of `q` is needed for this uniqueness implication. -/
theorem tangent_foot_unique_opposite_existing {u v q t t' : E} {r d : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫ = 0) (hr : r ≠ 0)
    (ht : t ∈ Submodule.span ℝ ({u, v} : Set E))
    (ht' : t' ∈ Submodule.span ℝ ({u, v} : Set E))
    (hradius : ‖t‖ = d) (hradius' : ‖t'‖ = d)
    (htangent : ⟪r • u - t, t⟫ = 0)
    (htangent' : ⟪r • u - t', t'⟫ = 0)
    (hopposite : ⟪v, q⟫ * ⟪v, t⟫ < 0)
    (hopposite' : ⟪v, q⟫ * ⟪v, t'⟫ < 0) : t = t' :=
  tangent_foot_unique_on_strict_side hu hv huv hr ht ht' hradius hradius'
    htangent htangent' (same_strict_side_of_opposite hopposite hopposite')

/-- Elementary projected-plane data sufficient to identify two candidate
facet centres. Constructing these data from a convex polytope requires the
ridge projection and open-wedge arguments; equality of the centres is a
conclusion of the record, not a field. -/
structure OppositeTangentData (t t' : E) where
  p : E
  u : E
  v : E
  existingFoot : E
  r : ℝ
  d : ℝ
  unit_u : ‖u‖ = 1
  unit_v : ‖v‖ = 1
  orthogonal : ⟪u, v⟫ = 0
  p_eq : p = r • u
  r_ne_zero : r ≠ 0
  mem_plane : t ∈ Submodule.span ℝ ({u, v} : Set E)
  mem_plane' : t' ∈ Submodule.span ℝ ({u, v} : Set E)
  radius : ‖t‖ = d
  radius' : ‖t'‖ = d
  tangent : ⟪p - t, t⟫ = 0
  tangent' : ⟪p - t', t'⟫ = 0
  opposite : ⟪v, existingFoot⟫ * ⟪v, t⟫ < 0
  opposite' : ⟪v, existingFoot⟫ * ⟪v, t'⟫ < 0

theorem OppositeTangentData.eq {t t' : E} (D : OppositeTangentData t t') : t = t' :=
  tangent_foot_unique_opposite_existing D.unit_u D.unit_v D.orthogonal D.r_ne_zero
    D.mem_plane D.mem_plane' D.radius D.radius'
    (by simpa only [D.p_eq] using D.tangent)
    (by simpa only [D.p_eq] using D.tangent') D.opposite D.opposite'

end Uniform5
