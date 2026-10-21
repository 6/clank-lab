import R3P10.CertCmd

/-! # The base formula Lean reasons about is the formula file -/

namespace R3P10

/- `encode 18 9`, the formula of the encoding proof, equals the clauses of
`data/cnf/k18p10.cnf` (natively evaluated comparison). -/
native_decide_thm encode_k18 : encode 18 9 = k18Base

end R3P10
