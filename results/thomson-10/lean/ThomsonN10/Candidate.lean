import ThomsonN10.Basic

/-! The D4d bicapped square antiprism: poles 0,1; upper square 2-5 at height h;
lower square 6-9 at height -h, rotated by pi/4. The height is the unique zero of
the derivative of the family energy in an exact rational box of width < 2^-300
(the box of our earlier N10 root proof). Adapted from the MIT N=9 Candidate.lean
(aravindkarthigeyan/thomson-n9-lean @ 168ff0c). -/

namespace ThomsonN10

def heightLower : ℚ := 513213568640798381215999065069135718731748351905698829816800875926548421101580455514066781 / 1214168057641080669324663691764699316651504274407587200782382756086815178253255311360000000
def heightUpper : ℚ := 1026427137281596762431998130138271437463496703811397659633601751853096842203160911028133563 / 2428336115282161338649327383529398633303008548815174401564765512173630356506510622720000000

noncomputable def rho (h : ℝ) : ℝ := Real.sqrt (1 - h ^ 2)
noncomputable def q (h : ℝ) : ℝ := rho h * Real.sqrt 2 / 2

/-- Coulomb energy of the family, 45 pairs by class. -/
noncomputable def familyEnergy (h : ℝ) : ℝ :=
  1 / 2 + (4 * Real.sqrt 2 + 2) / Real.sqrt (1 - h ^ 2)
    + 8 / Real.sqrt (2 - Real.sqrt 2 + (2 + Real.sqrt 2) * h ^ 2)
    + 8 / Real.sqrt (2 + Real.sqrt 2 + (2 - Real.sqrt 2) * h ^ 2)
    + 8 / Real.sqrt (2 - 2 * h) + 8 / Real.sqrt (2 + 2 * h)

/-- Derivative of familyEnergy in h (the stationarity equation). -/
noncomputable def stationarity (h : ℝ) : ℝ :=
  (4 * Real.sqrt 2 + 2) * h / ((1 - h ^ 2) * Real.sqrt (1 - h ^ 2))
    - 8 * (2 + Real.sqrt 2) * h /
        ((2 - Real.sqrt 2 + (2 + Real.sqrt 2) * h ^ 2) *
          Real.sqrt (2 - Real.sqrt 2 + (2 + Real.sqrt 2) * h ^ 2))
    - 8 * (2 - Real.sqrt 2) * h /
        ((2 + Real.sqrt 2 + (2 - Real.sqrt 2) * h ^ 2) *
          Real.sqrt (2 + Real.sqrt 2 + (2 - Real.sqrt 2) * h ^ 2))
    + 8 / ((2 - 2 * h) * Real.sqrt (2 - 2 * h))
    - 8 / ((2 + 2 * h) * Real.sqrt (2 + 2 * h))

abbrev CandidateParameter :=
  {h : ℝ // (heightLower : ℝ) ≤ h ∧ h ≤ (heightUpper : ℝ) ∧ stationarity h = 0}

noncomputable def candidateAt (h : ℝ) : Configuration :=
  ![vec 0 0 1, vec 0 0 (-1),
    vec (rho h) 0 h, vec 0 (rho h) h, vec (-rho h) 0 h, vec 0 (-rho h) h,
    vec (q h) (q h) (-h), vec (-q h) (q h) (-h), vec (-q h) (-q h) (-h), vec (q h) (-q h) (-h)]

noncomputable def candidate (h : CandidateParameter) : Configuration := candidateAt h

end ThomsonN10
