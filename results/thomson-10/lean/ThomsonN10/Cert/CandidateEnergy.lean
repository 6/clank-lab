/- Adapted from candidate-energy/parameterized/project/Mechanism.lean and Alphabet/TargetDefs.lean (supplied accepted N10 proof). N9 design: proof/lean/ThomsonN9/CandidateEnergy.lean, aravindkarthigeyan/thomson-n9-lean, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e, MIT. -/
import ThomsonN10.Interfaces
import ThomsonN10.Cert.LP.Geometry

namespace ThomsonN10.Cert.CE
open scoped BigOperators InnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
abbrev cand := candidateAt
abbrev rho := ThomsonN10.rho
abbrev q := ThomsonN10.q
def dc (h : ℝ) := 2-Real.sqrt 2+(2+Real.sqrt 2)*h^2
def dd (h : ℝ) := 2+Real.sqrt 2+(2-Real.sqrt 2)*h^2
def capPlus (h : ℝ) := 2+2*h
def capMinus (h : ℝ) := 2-2*h
abbrev energy := familyEnergy
def coulombPotential (t : ℝ) := (Real.sqrt (2-2*t))⁻¹

theorem pair_energy_eq_potential (x y : R3) (hx : ‖x‖=1) (hy : ‖y‖=1) :
    (‖x-y‖)⁻¹ = coulombPotential (inner ℝ x y) := by
  unfold coulombPotential
  rw [← LP.distance_sq x y hx hy, Real.sqrt_sq (norm_nonneg _)]

def label (h s : ℝ) (i : Fin 8) : ℝ := match i.val with
  | 0 => h^2 | 1 => 2*h^2-1 | 2 => (1-h^2)*s/2-h^2 | 3 => -(1-h^2)*s/2-h^2
  | 4 => -h | 5 => -1 | 6 => h | _ => 1

def gramCode (i j : Fin 10) : Fin 8 :=
  if i = j then 7 else
  if i.val < 2 ∧ j.val < 2 then 5 else
  if i.val < 2 then (if (i.val = 0 ∧ j.val < 6) ∨ (i.val = 1 ∧ 6 ≤ j.val) then 6 else 4) else
  if j.val < 2 then (if (j.val = 0 ∧ i.val < 6) ∨ (j.val = 1 ∧ 6 ≤ i.val) then 6 else 4) else
  if (i.val-2)/4 = (j.val-2)/4 then (if (i.val+4-j.val)%4 = 2 then 1 else 0) else
  if ((max i.val j.val-2)%4+4-(min i.val j.val-2)%4)%4 = 0 ∨
     ((max i.val j.val-2)%4+4-(min i.val j.val-2)%4)%4 = 3 then 2 else 3

def gramPoly (h s : ℝ) (i j : Fin 10) : ℝ := label h s (gramCode i j)
def gram (h : ℝ) (i j : Fin 10) : ℝ := gramPoly h (Real.sqrt 2) i j

theorem sqrt_two_sq : (Real.sqrt (2 : ℝ))^2 = 2 := by
  exact Real.sq_sqrt (by norm_num)

theorem parameter_sq_lt_one {h : ℝ} (hh : 0 < h ∧ h < 1) : h^2 < 1 := by
  nlinarith

theorem rho_sq {h : ℝ} (hh : 0 < h ∧ h < 1) : (rho h)^2 = 1-h^2 :=
  Real.sq_sqrt (by have := parameter_sq_lt_one hh; linarith)

theorem rho_pos {h : ℝ} (hh : 0 < h ∧ h < 1) : 0 < rho h :=
  Real.sqrt_pos.2 (by have := parameter_sq_lt_one hh; linarith)

theorem q_sq {h : ℝ} (hh : 0 < h ∧ h < 1) : (q h)^2 = (1-h^2)/2 := by
  rw [q,ThomsonN10.q,div_pow,mul_pow,sqrt_two_sq,rho_sq hh]
  ring

theorem rho_mul_q {h : ℝ} (hh : 0 < h ∧ h < 1) :
    rho h*q h = (1-h^2)*Real.sqrt 2/2 := by
  rw [q,ThomsonN10.q]
  calc
    _ = (rho h)^2*Real.sqrt 2/2 := by ring
    _ = _ := by rw [rho_sq hh]

theorem indexed_gram {h : ℝ} (hh : 0 < h ∧ h < 1) (i j : Fin 10) :
    inner ℝ (cand h i) (cand h j) = gram h i j := by
  have hρ := rho_sq hh
  have hq := q_sq hh
  have hρq := rho_mul_q hh
  rw [← LP.coordDot_eq_inner]
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,LP.coordDot,cand,
      gram,gramPoly,
      label,gramCode,
      PiLp.inner_apply,Fin.sum_univ_succ, candidateAt, vec] <;> nlinarith

theorem unit_norm {h : ℝ} (hh : 0 < h ∧ h < 1) (i : Fin 10) : ‖cand h i‖ = 1 := by
  have hg := indexed_gram hh i i
  have hd : gram h i i = 1 := by
    simp [gram,gramPoly,
      gramCode,label]
  rw [hd,real_inner_self_eq_norm_sq] at hg
  have hn := norm_nonneg (cand h i)
  nlinarith

theorem off_diagonal_gram_lt_one {h : ℝ} (hh : 0 < h ∧ h < 1)
    (i j : Fin 10) (hij : i ≠ j) : gram h i j < 1 := by
  have habs : |h| = h := abs_of_pos hh.1
  have hr := Real.sqrt_nonneg (2 : ℝ)
  have hsq := sqrt_two_sq
  have hr1 : Real.sqrt (2 : ℝ) < 2 := by nlinarith
  have hz : 0 < 1-h^2 := by have := parameter_sq_lt_one hh; linarith
  have hc : (1-h^2)*Real.sqrt 2/2-h^2 < 1 := by
    nlinarith [mul_pos hz (by linarith : 0 < 2-Real.sqrt (2 : ℝ))]
  have hd : -(1-h^2)*Real.sqrt 2/2-h^2 < 1 := by
    have := mul_nonneg hz.le hr
    nlinarith [sq_nonneg h]
  fin_cases i <;> fin_cases j <;> try (exact (hij rfl).elim)
  all_goals norm_num [gram,gramPoly,
      label,gramCode,habs] <;>
      first | exact hc | exact hd | nlinarith

theorem cand_injective {h : ℝ} (hh : 0 < h ∧ h < 1) : Function.Injective (cand h) := by
  intro i j heq
  by_contra hij
  have hg := off_diagonal_gram_lt_one hh i j hij
  rw [← indexed_gram hh,heq,real_inner_self_eq_norm_sq,unit_norm hh] at hg
  norm_num at hg

theorem sphere {h : ℝ} (hh : 0 < h ∧ h < 1) :
    IsSphereConfiguration (cand h) := ⟨unit_norm hh,cand_injective hh⟩

theorem pair_class_sum (f : Fin 8 → ℝ) :
    Interfaces.pairSum (fun i j => f (gramCode i j)) =
      8*f 0+4*f 1+8*f 2+8*f 3+8*f 4+f 5+8*f 6 := by
  classical
  have hi (i : Fin 10) : Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by
    ext j
    simp
  simp only [Interfaces.pairSum,hi,Finset.sum_filter]
  simp only [Fin.sum_univ_succ]
  norm_num [gramCode,Fin.ext_iff,Fin.lt_def]
  ring

theorem potential_label {h : ℝ} (hh : 0 < h ∧ h < 1) (k : Fin 8) :
    coulombPotential
      (label h (Real.sqrt 2) k) =
      (match k.val with
        | 0 => 1/(Real.sqrt 2*rho h)
        | 1 => 1/(2*rho h)
        | 2 => 1/Real.sqrt (dc h)
        | 3 => 1/Real.sqrt (dd h)
        | 4 => 1/Real.sqrt (capPlus h)
        | 5 => 1/2
        | 6 => 1/Real.sqrt (capMinus h)
        | _ => 0) := by
  have hr : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hρ := rho_pos hh
  have hρsq := rho_sq hh
  have hsq := sqrt_two_sq
  have hA : Real.sqrt (2-2*h^2) = Real.sqrt 2*rho h := by
    apply (Real.sqrt_eq_iff_eq_sq (by nlinarith [parameter_sq_lt_one hh]) (by positivity)).2
    rw [mul_pow,sqrt_two_sq,hρsq]
    ring
  have hB : Real.sqrt (2-2*(2*h^2-1)) = 2*rho h := by
    apply (Real.sqrt_eq_iff_eq_sq (by nlinarith [parameter_sq_lt_one hh]) (by positivity)).2
    rw [mul_pow,hρsq]
    ring
  have hC : 2-2*((1-h^2)*Real.sqrt 2/2-h^2) = dc h := by
    dsimp [dc]; ring
  have hD : 2-2*(-(1-h^2)*Real.sqrt 2/2-h^2) = dd h := by
    dsimp [dd]; ring
  fin_cases k <;>
    simp only [label,coulombPotential,
      Fin.reduceFinMk, hA,hB,hC,hD,capPlus,capMinus]
  all_goals norm_num [one_div]

theorem gram_energy {h : ℝ} (hh : 0 < h ∧ h < 1) :
    Interfaces.pairSum (fun i j =>
      coulombPotential (gram h i j)) =
      energy h := by
  change Interfaces.pairSum (fun i j =>
    coulombPotential
      (label h (Real.sqrt 2) (gramCode i j))) = _
  rw [pair_class_sum (fun k => coulombPotential (label h (Real.sqrt 2) k))]
  simp only [potential_label hh]
  change 8*(1/(Real.sqrt 2*rho h))+4*(1/(2*rho h))+
    8*(1/Real.sqrt (dc h))+8*(1/Real.sqrt (dd h))+
    8*(1/Real.sqrt (capPlus h))+1/2+
    8*(1/Real.sqrt (capMinus h)) = energy h
  have hr : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hρ := rho_pos hh
  have hsq := sqrt_two_sq
  have hlead : 8*(1/(Real.sqrt 2*rho h))+4*(1/(2*rho h)) =
      (4*Real.sqrt 2+2)/rho h := by
    field_simp [hr.ne',hρ.ne']
    nlinarith
  rw [hlead]
  dsimp [energy,familyEnergy,rho,ThomsonN10.rho,dc,dd,capPlus,capMinus]
  ring

theorem coulomb_eq_gram (x : Configuration) (hx : ∀ i, ‖x i‖ = 1) :
    coulombEnergy x =
      Interfaces.pairSum (fun i j =>
        coulombPotential (inner ℝ (x i) (x j))) := by
  unfold coulombEnergy Interfaces.pairSum
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact pair_energy_eq_potential (x i) (x j) (hx i) (hx j)

theorem energy_eq {h : ℝ} (hh : 0 < h ∧ h < 1) :
    coulombEnergy (cand h) = energy h := by
  rw [coulomb_eq_gram _ (unit_norm hh)]
  simp_rw [indexed_gram hh]
  exact gram_energy hh


end
end ThomsonN10.Cert.CE
