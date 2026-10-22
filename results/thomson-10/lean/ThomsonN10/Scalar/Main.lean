/- Scalar package entry point. The Bernstein checker and proof bridges are
   adapted from proof/lean/ThomsonN9/Bernstein/{Checker,Minorant}.lean and
   proof/lean/ClaudeL2b/RefinedWindows.lean, aravindkarthigeyan/thomson-n9-lean
   (MIT), commit 168ff0c98cab4dfda0460ba55f8d169070ac385e. -/
import ThomsonN10.Scalar.Minorant
import ThomsonN10.Scalar.Exterior

example : ThomsonN10.Interfaces.MinorantBound := ThomsonN10.Scalar.MinorantBound_holds
example : ThomsonN10.Interfaces.ExteriorGap := ThomsonN10.Scalar.ExteriorGap_holds

#print axioms ThomsonN10.Scalar.MinorantBound_holds
#print axioms ThomsonN10.Scalar.ExteriorGap_holds
