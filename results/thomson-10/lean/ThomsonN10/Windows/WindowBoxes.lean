/- Adapted from aravindkarthigeyan/thomson-n9-lean,
   proof/lean/ClaudeWindow/WindowBoxes.lean, MIT,
   commit 168ff0c98cab4dfda0460ba55f8d169070ac385e. -/
import ThomsonN10.Data
import ThomsonN10.Windows.WindowData
import Mathlib.Tactic

namespace ThomsonN10.Windows

open Iv

def hBox : Iv := ⟨42268742404398 / 10^14, 42268742404400 / 10^14⟩
def sBox : Iv := ⟨141421356237309 / 10^14, 141421356237310 / 10^14⟩

noncomputable def palette (h : ℝ) : ℕ → ℝ
  | 0 => -1
  | 1 => h
  | 2 => -h
  | 3 => h^2
  | 4 => 2*h^2-1
  | 5 => (1-h^2)*Real.sqrt 2*(1/2)-h^2
  | 6 => -(1-h^2)*Real.sqrt 2*(1/2)-h^2
  | _ => 0

def paletteBox : ℕ → Iv
  | 0 => const (-1)
  | 1 => hBox
  | 2 => sub (const 0) hBox
  | 3 => sq hBox
  | 4 => sub (mul (const 2) (sq hBox)) (const 1)
  | 5 => sub (mul (mul (sub (const 1) (sq hBox)) sBox) (const (1/2))) (sq hBox)
  | 6 => sub (mul (mul (sub (const 0) (sub (const 1) (sq hBox))) sBox)
      (const (1/2))) (sq hBox)
  | _ => const 0

theorem parameter_mem (h : CandidateParameter) : hBox.Mem (h : ℝ) := by
  have hl : (hBox.lo : ℝ) ≤ (heightLower : ℝ) := by norm_num [hBox, heightLower]
  have hu : (heightUpper : ℝ) ≤ (hBox.hi : ℝ) := by norm_num [hBox, heightUpper]
  exact ⟨hl.trans h.property.1, h.property.2.1.trans hu⟩

theorem sqrt_mem : sBox.Mem (Real.sqrt 2) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  constructor <;> norm_num [sBox] <;> nlinarith

theorem palette_mem {h : ℝ} (hh : hBox.Mem h) {c : ℕ} (hc : c < 7) :
    (paletteBox c).Mem (palette h c) := by
  have hsq := mem_sq hh
  have hz := mem_const 0
  have ho := mem_const 1
  have ht := mem_const 2
  have hf := mem_const (1/2)
  interval_cases c
  · convert mem_const (-1) using 1 <;> norm_num [paletteBox, palette]
  · exact hh
  · convert mem_sub hz hh using 1 <;> simp [paletteBox, palette]
  · exact hsq
  · convert mem_sub (mem_mul ht hsq) ho using 1 <;> simp [paletteBox, palette]
  · convert mem_sub (mem_mul (mem_mul (mem_sub ho hsq) sqrt_mem) hf) hsq using 1 <;>
      norm_num [paletteBox, palette]
  · convert mem_sub (mem_mul (mem_mul (mem_sub hz (mem_sub ho hsq)) sqrt_mem) hf) hsq using 1 <;>
      norm_num [paletteBox, palette]

theorem boxes_cover : ∀ c, c < 7 →
    (box c).lo ≤ (paletteBox c).lo - windowRadius ∧
      (paletteBox c).hi + windowRadius ≤ (box c).hi := by decide +kernel

theorem boxes_disjoint : ∀ c, c < 7 → ∀ d, d < 7 → c ≠ d →
    (box c).hi < (box d).lo ∨ (box d).hi < (box c).lo := by decide +kernel

theorem window_mem_box {h : ℝ} (hh : hBox.Mem h) {c : ℕ} (hc : c < 7)
    {t : ℝ} (ht : |t - palette h c| ≤ (windowRadius : ℝ)) : (box c).Mem t := by
  obtain ⟨hp1, hp2⟩ := palette_mem hh hc
  obtain ⟨hb1, hb2⟩ := boxes_cover c hc
  have hb1' : ((box c).lo : ℝ) ≤ ((paletteBox c).lo : ℝ) - (windowRadius : ℝ) := by
    exact_mod_cast hb1
  have hb2' : ((paletteBox c).hi : ℝ) + (windowRadius : ℝ) ≤ ((box c).hi : ℝ) := by
    exact_mod_cast hb2
  rw [abs_le] at ht
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem box_unique {c d : ℕ} (hc : c < 7) (hd : d < 7) {t : ℝ}
    (h1 : (box c).Mem t) (h2 : (box d).Mem t) : c = d := by
  by_contra hne
  rcases boxes_disjoint c hc d hd hne with h | h
  · have : ((box c).hi : ℝ) < (box d).lo := by exact_mod_cast h
    linarith [h1.2, h2.1]
  · have : ((box d).hi : ℝ) < (box c).lo := by exact_mod_cast h
    linarith [h1.1, h2.2]

theorem window_unique {h : ℝ} (hh : hBox.Mem h) {c d : ℕ} (hc : c < 7) (hd : d < 7)
    {t : ℝ} (h1 : |t - palette h c| ≤ (windowRadius : ℝ))
    (h2 : |t - palette h d| ≤ (windowRadius : ℝ)) : c = d :=
  box_unique hc hd (window_mem_box hh hc h1) (window_mem_box hh hd h2)

theorem palette_contact (h : ℝ) (c : Fin 7) : palette h c = contact h c := by
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hs2 : Real.sqrt (2 : ℝ)^2 = 2 := Real.sq_sqrt (by norm_num)
  have he : (1 : ℝ)/Real.sqrt 2 = Real.sqrt 2*(1/2) := by
    apply (div_eq_iff hs).mpr
    nlinarith
  simp only [one_div] at he
  fin_cases c <;> simp [palette, contact, div_eq_mul_inv, he] <;> ring

end ThomsonN10.Windows
