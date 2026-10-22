/- Adapted from proof/lean/ThomsonN9/LocalTarget.lean and Endgame.lean,
 aravindkarthigeyan/thomson-n9-lean @
 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Interfaces
import ThomsonN10.Local.CandidateAlignment
import ThomsonN10.Local.LocalCoercivity
import ThomsonN10.Local.Endgame

namespace ThomsonN10.Local

namespace Endgame

theorem sublevel_congruent_of_localization (h : CandidateParameter)
    (x : Configuration) (hx : IsSphereConfiguration x)
    (hg : ∃ p : Equiv.Perm (Fin 10), ∀ i j,
      |inner ℝ (x (p i)) (x (p j))-inner ℝ (candidate h i) (candidate h j)| ≤
        (windowRadius : ℝ))
    (he : coulombEnergy x ≤ coulombEnergy (candidate h))
    (hpositive : (constrainedHessian (candidate h)+
      rotationColumns (candidate h)*(rotationColumns (candidate h)).transpose-
      (1/20 : ℝ) • (1 : Matrix (Fin 10 × Fin 3) (Fin 10 × Fin 3) ℝ)).PosSemidef) :
    Congruent x (candidate h) := by
  obtain ⟨p,hp⟩ := hg
  obtain ⟨Q,hmin,hbound⟩ := candidate_gram_close_minimal_alignment h
    (fun i => hx.1 (p i)) (by norm_num [windowRadius]) (by norm_num [windowRadius]) hp
  let y : Configuration := fun i => Q (x (p i))
  have hy : ∀ i, ‖y i‖ = 1 := fun i => by
    simpa only [y,Q.norm_map] using hx.1 (p i)
  have henergy : coulombEnergy y = coulombEnergy x :=
    congruent_energy ⟨Q,p,fun _ => rfl⟩
  let rho : ℝ := Real.sqrt (∑ i, ‖y i-candidate h i‖^2)
  have hr : 0 ≤ rho := Real.sqrt_nonneg _
  have hs : ∑ i, ‖y i-candidate h i‖^2 = rho^2 :=
    (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm
  have hr1 : rho ≤ (1/1000 : ℝ) := by
    change (∑ i, ‖y i-candidate h i‖^2) ≤ (10000*(windowRadius : ℝ))^2 at hbound
    norm_num [windowRadius] at hbound
    nlinarith
  have hskew : ∀ a c : Fin 3,
      (∑ i, ((y i-candidate h i) a*candidate h i c-
        (y i-candidate h i) c*candidate h i a)) = 0 := by
    intro a c
    simpa only [y,PiLp.sub_apply] using
      minimal_alignment_displacement_skew_zero hmin a c
  have hyle : coulombEnergy y ≤ coulombEnergy (candidate h) := by
    rw [henergy]
    exact he
  have hyexact := candidate_local_equality h y hy hr hr1 hs hskew
    hpositive hyle
  refine ⟨Q.symm,p.symm,?_⟩
  intro i
  have hi := congrArg Q.symm (congr_fun hyexact (p.symm i))
  simpa only [y,Equiv.apply_symm_apply,Q.symm_apply_apply] using hi

end Endgame

#print axioms Endgame.sublevel_congruent_of_localization

end ThomsonN10.Local
