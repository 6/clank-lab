import MeasureTransfer


noncomputable section
open Set
namespace Geneson

def HorizontalSegment (c : ℝ) : Set Plane := Icc 0 c ×ˢ {0}

def OpenHorizontalStrip (a c : ℝ) : Set Plane := Ioo a (a+c) ×ˢ univ

lemma openHorizontalStrip_isOpen (a c : ℝ) : IsOpen (OpenHorizontalStrip a c) :=
  isOpen_Ioo.prod isOpen_univ

/-- An ambient-open strip of width c excludes the two endpoints of a c-segment. -/
theorem horizontal_segment_avoids_open_strip {c : ℝ} (hc : 0 < c) (a : ℝ) :
    ¬ Contains (HorizontalSegment c) (OpenHorizontalStrip a c) := by
  intro h
  obtain ⟨w,hw⟩ := contains_iff_hasCopy.1 h
  have h0 : (0,0) ∈ HorizontalSegment c := by simp [HorizontalSegment, hc.le]
  have hc' : (c,0) ∈ HorizontalSegment c := by simp [HorizontalSegment, hc.le]
  have hzero := (hw.2.2 ⟨(0,0),h0⟩).1
  have hend := (hw.2.2 ⟨(c,0),hc'⟩).1
  have hexpand := hw.1 ⟨0,⟨(0,0),h0,rfl⟩⟩ ⟨c,⟨(c,0),hc',rfl⟩⟩ hc.le
  change a < w.1 _ ∧ w.1 _ < a+c at hzero hend
  change c - 0 ≤ w.1 _ - w.1 _ at hexpand
  linarith [hzero.1,hend.2]

/-- Inclusive endpoints permit an exact translation of the closed segment. -/
theorem horizontal_segment_contains_translate (c a b : ℝ) :
    Contains (HorizontalSegment c) (Icc a (a+c) ×ˢ {b}) := by
  apply contains_iff_hasCopy.2
  let w : Maps (HorizontalSegment c) :=
    (fun x => (x : ℝ) + a, fun y => (y : ℝ) + b)
  refine ⟨w,?_,?_,?_⟩
  · intro x y hxy
    dsimp [w]
    linarith
  · intro x y hxy
    dsimp [w]
    linarith
  · intro p
    have hp : 0 ≤ p.1.1 ∧ p.1.1 ≤ c := p.property.1
    have hy : p.1.2 = 0 := p.property.2
    change (p.1.1+a ∈ Icc a (a+c)) ∧ p.1.2+b ∈ ({b} : Set ℝ)
    constructor
    · constructor <;> linarith [hp.1,hp.2]
    · simp [hy]

lemma singleton_contains_of_nonempty (p : Plane) {S : Set Plane} (hS : S.Nonempty) :
    Contains {p} S := by
  obtain ⟨z,hz⟩ := hS
  apply contains_iff_hasCopy.2
  refine ⟨(fun _ => z.1, fun _ => z.2),?_,?_,?_⟩
  · intro x y hxy
    have hx : (x : ℝ) = p.1 := by simpa [X] using x.property
    have hy : (y : ℝ) = p.1 := by simpa [X] using y.property
    simp [hx,hy]
  · intro x y hxy
    have hx : (x : ℝ) = p.2 := by simpa [Y] using x.property
    have hy : (y : ℝ) = p.2 := by simpa [Y] using y.property
    simp [hx,hy]
  · intro q
    exact hz

/-- The exact real supremum assigns zero to every singleton pattern. -/
theorem opx_singleton_zero (n : ℝ) (p : Plane) : opx n {p} = 0 := by
  apply le_antisymm
  · apply opx_le_of_open_bounds (singleton_nonempty p)
    intro S hSo hSq havoid
    have hS : S = ∅ := Set.not_nonempty_iff_eq_empty.mp
      (fun h => havoid (singleton_contains_of_nonempty p h))
    simp [hS,Area]
  · exact opx_nonneg n (singleton_nonempty p)

/-- The strict-inequality mutation of the endpoint is false already for singletons. -/
theorem not_strict_singleton_bound (n : ℝ) (p : Plane) :
    ¬ (opx n ({p} ∪ {p}) < opx n {p} + opx n {p}) := by
  simp only [union_self, opx_singleton_zero, zero_add, lt_self_iff_false, not_false_eq_true]

end Geneson
