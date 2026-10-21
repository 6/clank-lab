import Mathlib.Order.Lattice.Nat
import R3P10.Main
import R3P10.Lower

/-! # R(P_10, P_10, P_10) = 18

The 3-colour Ramsey number of the path is defined from the main theorem's own
notions (`Col`, `HasMonoPath`), and the two bounds combine: the upper bound
`K18_P10_of_certs` (from the certified UNSAT facts, carried as hypotheses here;
`R3_P10_eq_18` in `R3P10Final.lean` supplies them as theorems checked by Lean's
LRAT checker) and the lower
bound `K17_no_mono_P10` (no hypotheses; kernel-checked by `decide +kernel`).
-/

namespace R3P10

/-- The 3-colour Ramsey number of the path on `m` vertices: the least `n` such
that every 3-colouring of the edges of `K_n` has a monochromatic `P_m`. -/
noncomputable def ramsey3Path (m : ℕ) : ℕ := sInf {n | ∀ X : Col n, HasMonoPath n m X}

/-- If every 3-colouring of `K_N` has a monochromatic `P_m` and some colouring
of `K_(N-1)` has none, the Ramsey number is `N`. -/
theorem ramsey3Path_eq {m N : ℕ} (hN : 0 < N) (hup : ∀ X : Col N, HasMonoPath N m X)
    (hlow : ∃ X : Col (N - 1), ¬ HasMonoPath (N - 1) m X) : ramsey3Path m = N := by
  apply le_antisymm (Nat.sInf_le (show N ∈ {n | ∀ X : Col n, HasMonoPath n m X} from hup))
  apply le_csInf ⟨N, show N ∈ {n | ∀ X : Col n, HasMonoPath n m X} from hup⟩
  intro n hn
  by_contra hlt
  obtain ⟨X, hX⟩ := hlow
  exact hX (mono_restrict (n := N - 1) (by omega) hn X)

/-- `R(P_10, P_10, P_10) = 18`, from the certified facts of the upper bound given
as explicit hypotheses, exactly those of `K18_P10_of_certs` (no axioms beyond
Lean's standard ones). -/
theorem R3_P10_eq_18_of_certs
    (h5 : UnsatWithPaths 5 3 (encode 5 0)) (h6 : UnsatWithPaths 6 4 (encode 6 3))
    (h9 : UnsatWithPaths 9 5 (encode 9 4)) (h10 : UnsatWithPaths 10 6 (encode 10 5))
    (h13 : UnsatWithPaths 13 7 (encode 13 6)) (h14 : UnsatWithPaths 14 8 (encode 14 7))
    (h17 : UnsatWithPaths 17 9 (encode 17 8))
    (hcover : UnsatWithPaths 18 10 (encode 18 9 ++ finalCubes.map negCube))
    (hcubes : ∀ c ∈ finalCubes, UnsatWithPaths 18 10 (encode 18 9 ++ cubeUnits c)) :
    ramsey3Path 10 = 18 :=
  ramsey3Path_eq (by norm_num)
    (K18_P10_of_certs h5 h6 h9 h10 h13 h14 h17 hcover hcubes) ⟨k17Col, K17_no_mono_P10⟩

end R3P10
