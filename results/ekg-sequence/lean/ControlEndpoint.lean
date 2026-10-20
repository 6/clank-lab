import EKG.EndpointDefinitions
import EKG.FiniteBase

open EKG.CanonicalEndpoint

-- Actual canonical prefix, with ordinary kernel evaluation of finite primality.
theorem ekg_endpoint_control :
    a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 4 ∧ a 4 = 6 ∧ a 5 = 3 ∧ a 6 = 9 ∧
    b 1 = 1 ∧ b 2 = 2 ∧ b 3 = 4 ∧ b 4 = 6 ∧ b 5 = 6 ∧ b 6 = 6 ∧
    smoothValue 2 = 2 ∧ smoothValue 6 = 6 ∧ smoothValue 15 = 10 := by
  have h (n : ℕ) (hn : n < 13) : a (n + 1) = EKG.FiniteBase.value n := by
    simpa only [a, Nat.add_sub_cancel] using EKG.FiniteBase.first_thirteen EKG.canonical hn
  have h1 : a 1 = 1 := h 0 (by decide)
  have h2 : a 2 = 2 := h 1 (by decide)
  have h3 : a 3 = 4 := h 2 (by decide)
  have h4 : a 4 = 6 := h 3 (by decide)
  have h5 : a 5 = 3 := h 4 (by decide)
  have h6 : a 6 = 9 := h 5 (by decide)
  simp only [b, h1, h2, h3, h4, h5, h6]
  decide

#print axioms ekg_endpoint_control
