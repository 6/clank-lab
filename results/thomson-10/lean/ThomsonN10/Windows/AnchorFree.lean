/- Adapted from aravindkarthigeyan/thomson-n9-lean,
   proof/lean/ClaudeWindow/AnchorFree.lean, MIT,
   commit 168ff0c98cab4dfda0460ba55f8d169070ac385e.
   N10 uses five vertices and retains the genuine antipodal window. -/
import ThomsonN10.Windows.WindowBoxes
import ThomsonN10.Windows.FormulaSound
import ThomsonN10.Windows.Geometry

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonN10.Windows

open Iv

def smallTri (x y z : ℕ) : Bool :=
  decide ((d3Iv (box x) (box y) (box z)).lo ≤ thetaQ) &&
    decide (0 ≤ (d3Iv (box x) (box y) (box z)).hi)

/-- Exactly the permutations of OPM, PPB, and MMB. -/
def smallType (x y z : ℕ) : Bool :=
  decide ((x,y,z) ∈ ([(0,1,2), (0,2,1), (1,0,2), (1,2,0), (2,0,1), (2,1,0),
    (1,1,4), (1,4,1), (4,1,1), (2,2,4), (2,4,2), (4,2,2)] : List Tri))

theorem smallTri_cover : ∀ x, x < 7 → ∀ y, y < 7 → ∀ z, z < 7 →
    smallTri x y z = true → smallType x y z = true := by decide +kernel

def flatCheck : Bool :=
  (List.range 7).all fun a => (List.range 7).all fun b => (List.range 7).all fun c =>
    !(smallType a b c) ||
    (List.range 7).all fun d => (List.range 7).all fun e => (List.range 7).all fun f =>
      !(smallType a d e && smallType b d f && smallType c e f) ||
      (List.range 7).all fun g => (List.range 7).all fun h =>
        (List.range 7).all fun i => (List.range 7).all fun j =>
        !(smallType a g h && smallType b g i && smallType c h i &&
          smallType d g j && smallType e h j && smallType f i j)

theorem flatCheck_ok : flatCheck = true := by decide +kernel

theorem not_flat_five (a b c d e f g h i j : ℕ)
    (ha : a < 7) (hb : b < 7) (hc : c < 7) (hd : d < 7) (he : e < 7)
    (hf : f < 7) (hg : g < 7) (hh : h < 7) (hi : i < 7) (hj : j < 7)
    (s012 : smallType a b c = true) (s013 : smallType a d e = true)
    (s023 : smallType b d f = true) (s123 : smallType c e f = true)
    (s014 : smallType a g h = true) (s024 : smallType b g i = true)
    (s124 : smallType c h i = true) (s034 : smallType d g j = true)
    (s134 : smallType e h j = true) (s234 : smallType f i j = true) : False := by
  have H := flatCheck_ok
  unfold flatCheck at H
  have H1 := List.all_eq_true.mp H a (List.mem_range.mpr ha)
  have H2 := List.all_eq_true.mp H1 b (List.mem_range.mpr hb)
  have H3 := List.all_eq_true.mp H2 c (List.mem_range.mpr hc)
  simp only [s012, Bool.not_true, Bool.false_or] at H3
  have H4 := List.all_eq_true.mp H3 d (List.mem_range.mpr hd)
  have H5 := List.all_eq_true.mp H4 e (List.mem_range.mpr he)
  have H6 := List.all_eq_true.mp H5 f (List.mem_range.mpr hf)
  simp only [s013, s023, s123, Bool.and_self, Bool.not_true, Bool.false_or] at H6
  have H7 := List.all_eq_true.mp H6 g (List.mem_range.mpr hg)
  have H8 := List.all_eq_true.mp H7 h (List.mem_range.mpr hh)
  have H9 := List.all_eq_true.mp H8 i (List.mem_range.mpr hi)
  have H10 := List.all_eq_true.mp H9 j (List.mem_range.mpr hj)
  simp only [s014, s024, s124, s034, s134, s234, Bool.and_self,
    Bool.not_true, Bool.false_eq_true] at H10

theorem smallType_of {x y z : ℕ} (hx : x < 7) (hy : y < 7) (hz : z < 7)
    {a b c : ℝ} (ha : (box x).Mem a) (hb : (box y).Mem b) (hc : (box z).Mem c)
    (h0 : 0 ≤ d3R a b c) (h1 : d3R a b c ≤ (thetaQ : ℝ)) : smallType x y z = true := by
  apply smallTri_cover x hx y hy z hz
  have hm := mem_d3 ha hb hc
  unfold smallTri
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  constructor
  · have : ((d3Iv (box x) (box y) (box z)).lo : ℝ) ≤ (thetaQ : ℝ) := hm.1.trans h1
    exact_mod_cast this
  · have : (0 : ℝ) ≤ ((d3Iv (box x) (box y) (box z)).hi : ℝ) := h0.trans hm.2
    exact_mod_cast this

/-- Some triangle among the first five vertices has determinant greater than 10^-5.
The cover includes all antipodal and small-determinant color cases. -/
theorem exists_anchor (x : Fin 10 → E3) (hx : ∀ i, ‖x i‖ = 1)
    (col : Fin 10 → Fin 10 → ℕ) (hlt : ∀ i j, col i j < 7)
    (hmem : ∀ i j, i ≠ j → (box (col i j)).Mem (inner ℝ (x i) (x j))) :
    ∃ a b c : Fin 10, (thetaQ : ℝ) <
      d3R (inner ℝ (x a) (x b)) (inner ℝ (x a) (x c)) (inner ℝ (x b) (x c)) := by
  by_contra H
  push_neg at H
  have hs (i j k : Fin 10) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      smallType (col i j) (col i k) (col j k) = true :=
    smallType_of (hlt i j) (hlt i k) (hlt j k) (hmem i j hij) (hmem i k hik) (hmem j k hjk)
      (gram3_nonneg _ _ _ (hx i) (hx j) (hx k)) (H i j k)
  exact not_flat_five (col 0 1) (col 0 2) (col 1 2) (col 0 3) (col 1 3) (col 2 3)
    (col 0 4) (col 1 4) (col 2 4) (col 3 4)
    (hlt 0 1) (hlt 0 2) (hlt 1 2) (hlt 0 3) (hlt 1 3) (hlt 2 3)
    (hlt 0 4) (hlt 1 4) (hlt 2 4) (hlt 3 4)
    (hs 0 1 2 (by decide) (by decide) (by decide))
    (hs 0 1 3 (by decide) (by decide) (by decide))
    (hs 0 2 3 (by decide) (by decide) (by decide))
    (hs 1 2 3 (by decide) (by decide) (by decide))
    (hs 0 1 4 (by decide) (by decide) (by decide))
    (hs 0 2 4 (by decide) (by decide) (by decide))
    (hs 1 2 4 (by decide) (by decide) (by decide))
    (hs 0 3 4 (by decide) (by decide) (by decide))
    (hs 1 3 4 (by decide) (by decide) (by decide))
    (hs 2 3 4 (by decide) (by decide) (by decide))

end ThomsonN10.Windows
