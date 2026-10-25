import Steinberg.DrawingRows

namespace Steinberg

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Canonical orientations of actual adjacent vertices are exactly listed edges. -/
theorem graph_canonical_edge {u v : Fin 82} (h : graph.Adj u v) (huv : u < v) :
    (u.val, v.val) ∈ edgeList := by
  rcases h.2 with he | he
  · exact he
  · have hc := edgeList_canonical _ he
    have hlt : u.val < v.val := huv
    omega

namespace Drawing

def drawing (v : Fin 82) : RationalPoint := rational (points v.val)

theorem row_vertex {e : Nat × Nat} (he : e ∈ drawingEdges) (v : Nat)
    (hv : v < 82) (h1 : v ≠ e.1) (h2 : v ≠ e.2) :
    vertexCheck (points e.1) (points e.2) (points v) = true := by
  have hr := List.all_eq_true.mp rows_checked e he
  simp only [edgeRow, Bool.and_eq_true] at hr
  have hv' := List.all_eq_true.mp hr.1 v (List.mem_range.mpr hv)
  simpa [h1, h2] using hv'

theorem row_pair {e f : Nat × Nat} (he : e ∈ drawingEdges) (hf : f ∈ drawingEdges) :
    pairCheck points e f = true := by
  have hr := List.all_eq_true.mp rows_checked e he
  simp only [edgeRow, Bool.and_eq_true] at hr
  exact List.all_eq_true.mp hr.2 f hf

/-- The existing rational figure itself witnesses the geometric definition.
All real-segment reasoning follows from the generic separation soundness proofs;
only the integer certificate comparisons use kernel reduction. -/
theorem drawing_crossing_free : CrossingFreeDrawing graph drawing := by
  constructor
  · intro u v he
    apply Fin.ext
    exact distinct_sound points_distinct u.val v.val u.isLt v.isLt
      (rational_injective he)
  · intro u v w hadj huv hwu hwv
    have he : (u.val, v.val) ∈ drawingEdges :=
      drawingEdges_eq.symm ▸ graph_canonical_edge hadj huv
    have h1 : w.val ≠ u.val := fun h => hwu (Fin.ext h)
    have h2 : w.val ≠ v.val := fun h => hwv (Fin.ext h)
    exact vertex_sound (row_vertex he w.val w.isLt h1 h2)
  · intro u v s t huv hlt hst hlt' hne p hp hq
    have he : (u.val, v.val) ∈ drawingEdges :=
      drawingEdges_eq.symm ▸ graph_canonical_edge huv hlt
    have hf : (s.val, t.val) ∈ drawingEdges :=
      drawingEdges_eq.symm ▸ graph_canonical_edge hst hlt'
    have hne' : (u.val, v.val) ≠ (s.val, t.val) := by
      intro h
      apply hne
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    obtain ⟨w, hw, hw', hpw⟩ := pair_sound (row_pair he hf) hne' p hp hq
    have hwb : w < 82 := by
      rcases hw with hw | hw
      · simpa only [hw] using u.isLt
      · simpa only [hw] using v.isLt
    refine ⟨⟨w, hwb⟩, ?_, ?_, hpw⟩
    · exact hw.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
    · exact hw'.imp (fun h => Fin.ext h) (fun h => Fin.ext h)

end Drawing

theorem rational_planar : RationalPlanar graph :=
  ⟨Drawing.drawing, Drawing.drawing_crossing_free⟩

/-- info: 'Steinberg.rational_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rational_planar

end Steinberg
