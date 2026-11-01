import Analytic
import FixedGraphPolynomial

namespace BBPSplitStar

theorem endpoint : Endpoint :=
  endpoint_of_coefficients candidate_coefficients comparator_coefficients

end BBPSplitStar
