/- Adapted from proof/lean/ThomsonN9/LocalTarget.lean and Endgame.lean,
 aravindkarthigeyan/thomson-n9-lean @
 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.LocalReduction
import ThomsonN10.Local.Certificates.AmbientHessian

namespace ThomsonN10.Local

theorem LocalTarget_holds : ThomsonN10.Interfaces.LocalTarget := by
  intro h x hx hg he
  exact Endgame.sublevel_congruent_of_localization h x hx hg he
    (Certificates.AmbientKernel.candidate_augmented_hessian_posSemidef h)

#print axioms LocalTarget_holds

end ThomsonN10.Local
