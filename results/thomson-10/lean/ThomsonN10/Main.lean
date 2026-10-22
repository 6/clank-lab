import ThomsonN10.Assembly.FromInterfaces
import ThomsonN10.Param.Final
import ThomsonN10.Cert.LPSeparation
import ThomsonN10.Cert.PairBound
import ThomsonN10.Cert.CandidateUpper
import ThomsonN10.Scalar.Main
import ThomsonN10.Windows.Bridge
import ThomsonN10.Local.LocalTarget
import ThomsonN10.Admissible

/-! The complete N=10 theorem: existence and uniqueness of the stationary height,
global optimality of the D4d bicapped square antiprism, and uniqueness up to O(3)
and relabelling. -/

namespace ThomsonN10.Main

theorem complete : Challenge.CompleteTarget :=
  Assembly.complete_of_interfaces
    Param.ParameterExistsUnique_holds
    Cert.LPSeparation_holds
    Cert.PairBound_holds
    Cert.CandidateUpper_holds
    Scalar.MinorantBound_holds
    Scalar.ExteriorGap_holds
    Windows.WindowClassification_holds
    Local.LocalTarget_holds

#print axioms complete

end ThomsonN10.Main
