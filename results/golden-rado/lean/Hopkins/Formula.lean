import Hopkins.Upper
import Hopkins.Lower

namespace Hopkins

theorem formula_isLeast (a ell : ℕ) (ha : 2 ≤ a) (hell : 1 ≤ ell) :
    IsLeast (ForcingSet a (a * ell)) (a ^ 2 * (ell + 1) ^ 2) := by
  have hpos : 1 ≤ a^2*(ell+1)^2 := by
    have h : 0 < a^2*(ell+1)^2 := by positivity
    omega
  refine ⟨⟨hpos, upper a ell (by omega) hell⟩, ?_⟩
  intro M hM
  by_contra h
  have hlt : M < a^2*(ell+1)^2 := by omega
  obtain ⟨hv,hn⟩ := lower a ell M ha hell hM.1 hlt
  exact hn (hM.2 _ hv)

theorem formula (a ell : ℕ) (ha : 2 ≤ a) (hell : 1 ≤ ell) :
    R0phi a (a * ell) = a ^ 2 * (ell + 1) ^ 2 := by
  exact (formula_isLeast a ell ha hell).csInf_eq

end Hopkins
