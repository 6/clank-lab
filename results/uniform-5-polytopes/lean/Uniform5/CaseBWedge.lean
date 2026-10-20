import Uniform5.CaseBInputs
import Mathlib.Analysis.InnerProductSpace.Convex

/-! The exposed-face crossing argument and the use of Computation W.
Fan construction and cyclic order supply the crossing witnesses; the
logical exclusion of a crossing diagonal is proved here, not assumed. -/

noncomputable section
open Set

namespace Uniform5.CaseB

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A third point of a sphere cannot lie on a chord's segment. -/
theorem sphere_segment_endpoints {a b x o : E} {r : ℝ}
    (ha : dist a o = r) (hb : dist b o = r) (hx : dist x o = r)
    (hseg : x ∈ segment ℝ a b) : x = a ∨ x = b := by
  by_cases hab : a = b
  · subst b
    simpa using hseg
  by_contra h
  have hxa : x ≠ a := fun hxa => h (Or.inl hxa)
  have hxb : x ≠ b := fun hxb => h (Or.inr hxb)
  have hopen := mem_openSegment_of_ne_left_right hxa.symm hxb.symm hseg
  have hin := openSegment_subset_ball_of_ne
    (show a ∈ Metric.closedBall o r by simpa [Metric.mem_closedBall] using ha.le)
    (show b ∈ Metric.closedBall o r by simpa [Metric.mem_closedBall] using hb.le) hab hopen
  have hl : dist x o < r := hin
  linarith

/-- An open crossing with another chord rules out an exposed edge of a
cospherical hull. This supplies the face-containing-four-ends step of Wuse. -/
theorem crossing_chords_not_edge {V : Finset E} {a b x y t o : E} {r : ℝ}
    (hsphere : ∀ z ∈ V, dist z o = r) (hx : x ∈ V) (hy : y ∈ V)
    (hxa : x ≠ a) (hxb : x ≠ b)
    (htab : t ∈ segment ℝ a b) (htxy : t ∈ openSegment ℝ x y) :
    ¬ IsEdge V a b := by
  intro hab
  have hxseg := (hab.2.2.2.isExtreme.2
    (subset_convexHull ℝ (V : Set E) hx)
    (subset_convexHull ℝ (V : Set E) hy) htab htxy).1
  rcases sphere_segment_endpoints (hsphere a hab.1) (hsphere b hab.2.1)
    (hsphere x hx) hxseg with h | h
  · exact hxa h
  · exact hxb h

/-- Paper `lem:Wuse`. Protected edges are e and, in a paired fan, its
partner. Their endpoints are precisely the vertices omitted by the
producer. Every putative diagonal comes with an actual crossing chord.
No diagonal-length bound is assumed. -/
theorem wedge_only_protected_edges
    (p1 : P1) (chart : PolygonParameter → WFan → WFanGeometry E) (hW : W p1 chart)
    {n : PolygonParameter} {f : WFan} (hn : LargeParameter n) (hf : WListed p1 n f)
    {V : Finset E} {o : E} {r : ℝ} (hsphere : ∀ z ∈ V, dist z o = r)
    (hr : r ≤ 1) (hsep : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → 1 ≤ dist x y)
    (protectedEdge diagonal : E → E → Prop)
    (hprotected_symm : ∀ {x y}, protectedEdge x y → protectedEdge y x)
    (hends : ∀ x ∈ (chart n f).ends, ∃ y ∈ V, protectedEdge x y ∧ chord 17 ≤ dist x y)
    (hcover : ∀ x ∈ V, x ∈ (chart n f).vertices ∨ (chart n f).Admissible x)
    (hspecial : ∀ x y, (chart n f).specialPair x y → protectedEdge x y ∨ diagonal x y)
    (hcross : ∀ x y, diagonal x y → ∃ a ∈ V, ∃ b ∈ V, ∃ t,
      a ≠ x ∧ a ≠ y ∧ t ∈ segment ℝ x y ∧ t ∈ openSegment ℝ a b)
    {p q : E} (hpq : IsEdge V p q) (hlong : chord 17 ≤ dist p q) :
    protectedEdge p q := by
  by_contra hnot
  have hpends : p ∉ (chart n f).ends := by
    intro hp
    obtain ⟨z, hz, hpz, hlz⟩ := hends p hp
    have heq := long_edges_same_endpoint (hsphere p hpq.1) (hsphere q hpq.2.1)
      (hsphere z hz) hr hlong hlz (hsep q hpq.2.1 z hz)
    exact hnot (heq ▸ hpz)
  have hqends : q ∉ (chart n f).ends := by
    intro hq
    obtain ⟨z, hz, hqz, hlz⟩ := hends q hq
    have heq := long_edges_same_endpoint (hsphere q hpq.2.1) (hsphere p hpq.1)
      (hsphere z hz) hr (by simpa [dist_comm] using hlong) hlz (hsep p hpq.1 z hz)
    exact hnot (hprotected_symm (heq ▸ hqz))
  have heligible : ∀ x ∈ V, x ∉ (chart n f).ends →
      (chart n f).Admissible x ∨ (chart n f).Allowed x := by
    intro x hx he
    rcases hcover x hx with hfan | ha
    · exact Or.inr ⟨hfan, he⟩
    · exact Or.inl ha
  have hfan := hW.no_long_pair n f hn hf p q
    (heligible p hpq.1 hpends) (heligible q hpq.2.1 hqends) hlong
  have hsp : (chart n f).specialPair p q := by
    by_contra hnsp
    exact (not_lt_of_ge hlong) (hW.fan_distances n f hn hf p hfan.1 q hfan.2 hnsp)
  rcases hspecial p q hsp with hpr | hd
  · exact hnot hpr
  · obtain ⟨a, ha, b, hb, t, hap, haq, htpq, htab⟩ := hcross p q hd
    exact crossing_chords_not_edge hsphere ha hb hap haq htpq htab hpq

end Uniform5.CaseB
