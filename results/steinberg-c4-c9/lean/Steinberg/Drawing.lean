import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic

namespace Steinberg

abbrev RationalPoint := ℚ × ℚ
abbrev RealPoint := ℝ × ℝ

/-- A geometric closed straight segment in the real plane. Rational coordinates
are interpreted in ℝ, and the affine parameter ranges over all real numbers. -/
def OnSegment (a b : RationalPoint) (p : RealPoint) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
    p.1 = (1 - t) * (a.1 : ℝ) + t * (b.1 : ℝ) ∧
    p.2 = (1 - t) * (a.2 : ℝ) + t * (b.2 : ℝ)

def realPoint (a : RationalPoint) : RealPoint := ((a.1 : ℝ), (a.2 : ℝ))

/-- Canonical edge orientations avoid checking the same undirected edge twice.
Different edges may meet only at the image of a common endpoint; this includes
adjacent edges, so overlapping adjacent interiors are excluded as well. -/
structure CrossingFreeDrawing {n : Nat} (G : SimpleGraph (Fin n))
    (draw : Fin n → RationalPoint) : Prop where
  injective : Function.Injective draw
  vertex_not_on_edge : ∀ u v w, G.Adj u v → u < v → w ≠ u → w ≠ v →
    ¬ OnSegment (draw u) (draw v) (realPoint (draw w))
  edges_meet_only_at_common_endpoints : ∀ u v s t,
    G.Adj u v → u < v → G.Adj s t → s < t → (u, v) ≠ (s, t) →
    ∀ p, OnSegment (draw u) (draw v) p → OnSegment (draw s) (draw t) p →
      ∃ w, (w = u ∨ w = v) ∧ (w = s ∨ w = t) ∧ p = realPoint (draw w)

/-- Planarity here means existence of a crossing-free straight-line drawing
with rational vertex coordinates, with segments taken in the real plane. -/
def RationalPlanar {n : Nat} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ draw : Fin n → RationalPoint, CrossingFreeDrawing G draw

namespace Drawing

abbrev IPoint := ℤ × ℤ

/-- Published decimal coordinates, stored exactly as integer millionths. -/
def rational (a : IPoint) : RationalPoint :=
  ((a.1 : ℚ) / 1000000, (a.2 : ℚ) / 1000000)

def dot (normal point : IPoint) : ℤ :=
  normal.1 * point.1 + normal.2 * point.2

def eval (normal : IPoint) (point : RealPoint) : ℝ :=
  (normal.1 : ℝ) * point.1 + (normal.2 : ℝ) * point.2

def sub (a b : IPoint) : IPoint := (a.1 - b.1, a.2 - b.2)
def neg (a : IPoint) : IPoint := (-a.1, -a.2)
def perp (a : IPoint) : IPoint := (-a.2, a.1)

def normals (a b c d : IPoint) : List IPoint :=
  [perp (sub b a), neg (perp (sub b a)),
   perp (sub d c), neg (perp (sub d c)),
   (1, 0), (-1, 0), (0, 1), (0, -1)]

/-- A strict separating linear functional; all four endpoint comparisons are
integer arithmetic. -/
def strictCheck (normal a b c d : IPoint) : Bool :=
  decide (dot normal a < dot normal c ∧ dot normal a < dot normal d ∧
    dot normal b < dot normal c ∧ dot normal b < dot normal d)

def disjointCheck (a b c d : IPoint) : Bool :=
  (normals a b c d).any fun normal => strictCheck normal a b c d

/-- A supporting linear functional excludes one point from a closed segment. -/
def vertexCheck (a b c : IPoint) : Bool :=
  disjointCheck a b c c

/-- At the shared endpoint the functional is zero; it is nonpositive on one
ray and strictly positive on the other. This also handles opposite collinear
rays without assuming general position. -/
def rayCheck (u v w : IPoint) : Bool :=
  let a := sub v u
  let b := sub w u
  [perp a, neg (perp a), a, neg a].any fun normal =>
    decide (dot normal a ≤ 0 ∧ 0 < dot normal b)

theorem eval_rational (normal a : IPoint) :
    eval normal (realPoint (rational a)) = (dot normal a : ℝ) / 1000000 := by
  simp only [eval, realPoint, rational, dot, Rat.cast_div, Rat.cast_intCast,
    Rat.cast_ofNat]
  push_cast
  ring

theorem eval_segment (normal : IPoint) {a b : RationalPoint} {p : RealPoint}
    (h : OnSegment a b p) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      eval normal p = (1 - t) * eval normal (realPoint a) +
        t * eval normal (realPoint b) := by
  rcases h with ⟨t, ht, ht', hx, hy⟩
  refine ⟨t, ht, ht', ?_⟩
  simp only [eval, realPoint]
  rw [hx, hy]
  ring

theorem blend_lt {a b c t : ℝ} (ha : a < c) (hb : b < c)
    (ht : 0 ≤ t) (ht' : t ≤ 1) : (1-t)*a+t*b < c := by
  by_cases h : t = 0
  · simpa [h] using ha
  · have hp : 0 < t := lt_of_le_of_ne ht (Ne.symm h)
    nlinarith [mul_nonneg (sub_nonneg.mpr ht') (sub_nonneg.mpr (le_of_lt ha)),
      mul_pos hp (sub_pos.mpr hb)]

theorem convex_lt {a b c d x y t s : ℝ}
    (ha : a < c) (hb : a < d) (hc : b < c) (hd : b < d)
    (ht : 0 ≤ t) (ht' : t ≤ 1) (hs : 0 ≤ s) (hs' : s ≤ 1)
    (hx : x = (1-t)*a+t*b) (hy : y = (1-s)*c+s*d) : x < y := by
  have hxc : x < c := hx ▸ blend_lt ha hc ht ht'
  have hxd : x < d := hx ▸ blend_lt hb hd ht ht'
  by_cases h : s = 0
  · have he : y = c := by simpa [h] using hy
    simpa [he] using hxc
  · have hp : 0 < s := lt_of_le_of_ne hs (Ne.symm h)
    nlinarith [mul_nonneg (sub_nonneg.mpr hs') (sub_nonneg.mpr (le_of_lt hxc)),
      mul_pos hp (sub_pos.mpr hxd)]

theorem cast_div_lt {a b : ℤ} (h : a < b) :
    (a : ℝ) / 1000000 < (b : ℝ) / 1000000 := by
  have h' : (a : ℝ) < (b : ℝ) := by exact_mod_cast h
  exact div_lt_div_of_pos_right h' (by norm_num)

theorem strict_sound {normal a b c d : IPoint}
    (h : strictCheck normal a b c d = true) :
    ∀ p, OnSegment (rational a) (rational b) p →
      ¬ OnSegment (rational c) (rational d) p := by
  simp only [strictCheck, decide_eq_true_eq] at h
  intro p hp hq
  obtain ⟨t, ht, ht', he⟩ := eval_segment normal hp
  obtain ⟨s, hs, hs', hf⟩ := eval_segment normal hq
  rw [eval_rational, eval_rational] at he hf
  have h1 : (dot normal a : ℝ) / 1000000 < (dot normal c : ℝ) / 1000000 := cast_div_lt h.1
  have h2 : (dot normal a : ℝ) / 1000000 < (dot normal d : ℝ) / 1000000 := cast_div_lt h.2.1
  have h3 : (dot normal b : ℝ) / 1000000 < (dot normal c : ℝ) / 1000000 := cast_div_lt h.2.2.1
  have h4 : (dot normal b : ℝ) / 1000000 < (dot normal d : ℝ) / 1000000 := cast_div_lt h.2.2.2
  exact (lt_irrefl _) (convex_lt h1 h2 h3 h4 ht ht' hs hs' he hf)

theorem disjoint_sound {a b c d : IPoint} (h : disjointCheck a b c d = true) :
    ∀ p, OnSegment (rational a) (rational b) p →
      ¬ OnSegment (rational c) (rational d) p := by
  obtain ⟨normal, _, hn⟩ := List.any_eq_true.mp h
  exact strict_sound hn

theorem point_on_self (a : RationalPoint) : OnSegment a a (realPoint a) := by
  refine ⟨0, le_rfl, by norm_num, ?_, ?_⟩ <;> simp [realPoint]

theorem vertex_sound {a b c : IPoint} (h : vertexCheck a b c = true) :
    ¬ OnSegment (rational a) (rational b) (realPoint (rational c)) := by
  intro hc
  exact disjoint_sound h _ hc (point_on_self _)

theorem ray_sound {u v w : IPoint} (h : rayCheck u v w = true) :
    ∀ p, OnSegment (rational u) (rational v) p →
      OnSegment (rational u) (rational w) p → p = realPoint (rational u) := by
  obtain ⟨normal, _, hn⟩ := List.any_eq_true.mp h
  simp only [decide_eq_true_eq] at hn
  have hd : dot normal (sub v u) = dot normal v - dot normal u := by
    dsimp [dot, sub]; ring
  have hd' : dot normal (sub w u) = dot normal w - dot normal u := by
    dsimp [dot, sub]; ring
  rw [hd, hd'] at hn
  have hv : eval normal (realPoint (rational v)) ≤
      eval normal (realPoint (rational u)) := by
    rw [eval_rational, eval_rational]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact_mod_cast (show dot normal v ≤ dot normal u by omega)
  have hw : eval normal (realPoint (rational u)) <
      eval normal (realPoint (rational w)) := by
    rw [eval_rational, eval_rational]
    exact cast_div_lt (by omega)
  intro p hp hq
  obtain ⟨t, ht, ht', he⟩ := eval_segment normal hp
  obtain ⟨s, hs, hs', hx, hy⟩ := hq
  have hf : eval normal p = (1-s)*eval normal (realPoint (rational u)) +
      s*eval normal (realPoint (rational w)) := by
    dsimp [eval, realPoint]
    rw [hx, hy]
    ring
  have hle : eval normal p ≤ eval normal (realPoint (rational u)) := by
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hv)]
  have hz : s = 0 := by
    by_contra hne
    have hpos : 0 < s := lt_of_le_of_ne hs (Ne.symm hne)
    nlinarith [mul_pos hpos (sub_pos.mpr hw)]
  apply Prod.ext
  · simpa only [hz, sub_zero, one_mul, zero_mul, add_zero, realPoint] using hx
  · simpa only [hz, sub_zero, one_mul, zero_mul, add_zero, realPoint] using hy

theorem segment_symm {a b : RationalPoint} {p : RealPoint}
    (h : OnSegment a b p) : OnSegment b a p := by
  obtain ⟨t, ht, ht', hx, hy⟩ := h
  refine ⟨1-t, by linarith, by linarith, ?_, ?_⟩ <;> nlinarith

theorem rational_injective : Function.Injective rational := by
  intro a b h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [rational] at hx hy
  have hx' : (a.1 : ℚ) = (b.1 : ℚ) := (div_left_inj' (by norm_num)).mp hx
  have hy' : (a.2 : ℚ) = (b.2 : ℚ) := (div_left_inj' (by norm_num)).mp hy
  apply Prod.ext
  · exact_mod_cast hx'
  · exact_mod_cast hy'

/-- Each pair of different listed edges gets either strict separation, or a
supporting line at its common endpoint. The equal-edge case is exempt. -/
def pairCheck (points : Nat → IPoint) (e f : Nat × Nat) : Bool :=
  if e == f then true
  else if e.1 == f.1 then rayCheck (points e.1) (points e.2) (points f.2)
  else if e.1 == f.2 then rayCheck (points e.1) (points e.2) (points f.1)
  else if e.2 == f.1 then rayCheck (points e.2) (points e.1) (points f.2)
  else if e.2 == f.2 then rayCheck (points e.2) (points e.1) (points f.1)
  else disjointCheck (points e.1) (points e.2) (points f.1) (points f.2)

theorem pair_sound {points : Nat → IPoint} {e f : Nat × Nat}
    (h : pairCheck points e f = true) (hne : e ≠ f) :
    ∀ p, OnSegment (rational (points e.1)) (rational (points e.2)) p →
      OnSegment (rational (points f.1)) (rational (points f.2)) p →
      ∃ w, (w = e.1 ∨ w = e.2) ∧ (w = f.1 ∨ w = f.2) ∧
        p = realPoint (rational (points w)) := by
  simp only [pairCheck, beq_iff_eq] at h
  split_ifs at h with h0 h1 h2 h3 h4
  · exact False.elim (hne h0)
  · intro p hp hq
    rw [← h1] at hq
    exact ⟨e.1, Or.inl rfl, Or.inl h1, ray_sound h p hp hq⟩
  · intro p hp hq
    have hq' := segment_symm hq
    rw [← h2] at hq'
    exact ⟨e.1, Or.inl rfl, Or.inr h2, ray_sound h p hp hq'⟩
  · intro p hp hq
    rw [← h3] at hq
    exact ⟨e.2, Or.inr rfl, Or.inl h3, ray_sound h p (segment_symm hp) hq⟩
  · intro p hp hq
    have hq' := segment_symm hq
    rw [← h4] at hq'
    exact ⟨e.2, Or.inr rfl, Or.inr h4, ray_sound h p (segment_symm hp) hq'⟩
  · intro p hp hq
    exact False.elim (disjoint_sound h p hp hq)

end Drawing
end Steinberg
