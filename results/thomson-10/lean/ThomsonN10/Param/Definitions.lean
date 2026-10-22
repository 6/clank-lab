/- Ported from root-parameter/project/N10Root/Definitions.lean (our earlier N10 root proof, Lean 4.33). -/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

namespace ThomsonN10.Param
noncomputable section

def left : ℝ := 513213568640798381215999065069135718731748351905698829816800875926548421101580455514066781 / 1214168057641080669324663691764699316651504274407587200782382756086815178253255311360000000
def right : ℝ := 1026427137281596762431998130138271437463496703811397659633601751853096842203160911028133563 / 2428336115282161338649327383529398633303008548815174401564765512173630356506510622720000000
def coarseLeft : ℝ := 42268742404398 / 100000000000000
def coarseRight : ℝ := 42268742404400 / 100000000000000
def r : ℝ := Real.sqrt 2
def z (h : ℝ) : ℝ := 1-h^2
def dc (h : ℝ) : ℝ := 2-r+(2+r)*h^2
def dd (h : ℝ) : ℝ := 2+r+(2-r)*h^2
def capMinus (h : ℝ) : ℝ := 2-2*h
def capPlus (h : ℝ) : ℝ := 2+2*h

/-- Explicit N10 formula from authenticated parameter.py; geometry is separate. -/
def energy (h : ℝ) : ℝ :=
  1/2 + (4*r+2)/Real.sqrt (z h) + 8/Real.sqrt (dc h) +
  8/Real.sqrt (dd h) + 8/Real.sqrt (capMinus h) + 8/Real.sqrt (capPlus h)

def first (h : ℝ) : ℝ :=
  (4*r+2)*h/(z h*Real.sqrt (z h)) -
  8*(2+r)*h/(dc h*Real.sqrt (dc h)) -
  8*(2-r)*h/(dd h*Real.sqrt (dd h)) +
  8/(capMinus h*Real.sqrt (capMinus h)) -
  8/(capPlus h*Real.sqrt (capPlus h))

def second (h : ℝ) : ℝ :=
  (4*r+2)*(1+2*h^2)/((z h)^2*Real.sqrt (z h)) -
  8*(2+r)*(2-r-2*(2+r)*h^2)/((dc h)^2*Real.sqrt (dc h)) -
  8*(2-r)*(2+r-2*(2-r)*h^2)/((dd h)^2*Real.sqrt (dd h)) +
  24/((capMinus h)^2*Real.sqrt (capMinus h)) +
  24/((capPlus h)^2*Real.sqrt (capPlus h))

theorem box_bounds : 0 < left ∧ left < right ∧ right < 1 := by
  norm_num [left,right]
theorem box_width : right-left < (1 : ℝ)/2^300 := by
  norm_num [left,right,pow_succ]
theorem box_inside_coarse : coarseLeft ≤ left ∧ right ≤ coarseRight := by
  norm_num [coarseLeft,coarseRight,left,right]
theorem coarse_bounds : 0 < coarseLeft ∧ coarseLeft < coarseRight ∧ coarseRight < 1 := by
  norm_num [coarseLeft,coarseRight]
theorem r_bounds : 0 < r ∧ r < 2 := by
  constructor
  · exact Real.sqrt_pos.2 (by norm_num)
  · have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    dsimp [r]
    nlinarith

theorem domains {h : ℝ} (hh : h ∈ Set.Icc left right) :
    0 < z h ∧ 0 < dc h ∧ 0 < dd h ∧ 0 < capMinus h ∧ 0 < capPlus h := by
  have h0 : 0 < h := lt_of_lt_of_le box_bounds.1 hh.1
  have h1 : h < 1 := lt_of_le_of_lt hh.2 box_bounds.2.2
  obtain ⟨hr,hr2⟩ := r_bounds
  have hm : 0 < 2-r := by linarith
  have hp : 0 < 2+r := by linarith
  have hh2 := sq_nonneg h
  dsimp [z,dc,dd,capMinus,capPlus]
  exact ⟨by nlinarith,by positivity,by positivity,by linarith,by linarith⟩

theorem denominator_domains {h : ℝ} (hh : h ∈ Set.Icc left right) :
    0 < Real.sqrt (z h) ∧ 0 < Real.sqrt (dc h) ∧ 0 < Real.sqrt (dd h) ∧
    0 < Real.sqrt (capMinus h) ∧ 0 < Real.sqrt (capPlus h) ∧
    0 < z h*Real.sqrt (z h) ∧ 0 < dc h*Real.sqrt (dc h) ∧
    0 < dd h*Real.sqrt (dd h) ∧ 0 < capMinus h*Real.sqrt (capMinus h) ∧
    0 < capPlus h*Real.sqrt (capPlus h) ∧
    0 < (z h)^2*Real.sqrt (z h) ∧ 0 < (dc h)^2*Real.sqrt (dc h) ∧
    0 < (dd h)^2*Real.sqrt (dd h) ∧
    0 < (capMinus h)^2*Real.sqrt (capMinus h) ∧
    0 < (capPlus h)^2*Real.sqrt (capPlus h) := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := domains hh
  have s0 := Real.sqrt_pos.2 h0
  have s1 := Real.sqrt_pos.2 h1
  have s2 := Real.sqrt_pos.2 h2
  have s3 := Real.sqrt_pos.2 h3
  have s4 := Real.sqrt_pos.2 h4
  exact ⟨s0,s1,s2,s3,s4,by positivity,by positivity,by positivity,by positivity,
    by positivity,by positivity,by positivity,by positivity,by positivity,by positivity⟩
end
end ThomsonN10.Param
