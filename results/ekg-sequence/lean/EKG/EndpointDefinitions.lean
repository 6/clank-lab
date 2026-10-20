import EKG.Canonical

namespace EKG.CanonicalEndpoint

-- One-based canonical sequence. Index zero is an unused total extension.
noncomputable def a (n : ℕ) : ℕ := EKG.canonical.a (n - 1)

-- Only odd primes and three times odd primes are smoothed; 2 and 6 stay fixed.
def smoothValue (m : ℕ) : ℕ :=
  if m.Prime ∧ m ≠ 2 then 2 * m
  else if (m / 3).Prime ∧ m / 3 ≠ 2 ∧ m = 3 * (m / 3) then
    2 * (m / 3)
  else m

noncomputable def b (n : ℕ) : ℕ := smoothValue (a n)

end EKG.CanonicalEndpoint
