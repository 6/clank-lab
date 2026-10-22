import StanleySnf.Defs

/-!
# Internal definitions for the proof

Everything is in the variable `y = x - 1`, where `x` is the variable of `hookPoly ∘ (-X)`.
Indices `i, s` run over `0 .. n-1`; `N = n - 1`.
-/

open Polynomial

namespace StanleySnf

/-- `H_s(y) = ∏_i ((1+y)^{s_i} - 1)`. -/
noncomputable def HM (s : Multiset ℕ) : ℤ[X] := (s.map fun m => (1 + X) ^ m - 1).prod

/-- `Φ_s = H_s / z_s`, over `ℚ`. -/
noncomputable def PhiM (s : Multiset ℕ) : ℚ[X] :=
  C ((zeeM s : ℚ)⁻¹) * (HM s).map (Int.castRingHom ℚ)

/-- `η_μ(i) = [y^{i+1}] H_μ`. -/
noncomputable def eta {n : ℕ} (μ : n.Partition) (i : ℕ) : ℤ := (HM μ.parts).coeff (i + 1)

/-- `ε_μ = (-1)^{ℓ(μ)-1}`. -/
def eps {n : ℕ} (μ : n.Partition) : ℤ := (-1) ^ (μ.parts.card - 1)

/-- `e_s = s! gcd(n, s+1)`. -/
def ee (n s : ℕ) : ℕ := s.factorial * Nat.gcd n (s + 1)

/-- The form in the `y`-basis: `Q(i,s) = (-1)^{i+s} s! (N-s)! C(N-i, s)`
(`= (-1)^{i+s} (N-i)!(N-s)!/(N-i-s)!`, and `0` when `i + s > N`, for `i, s ≤ N`). -/
def Qf (N i s : ℕ) : ℤ := (-1) ^ (i + s) * ((s.factorial * (N - s).factorial * (N - i).choose s : ℕ) : ℤ)

/-- `a_0 = n`; `a_r = 2` if `r ≡ n (mod 2)`, else `1`. -/
def aa (n r : ℕ) : ℕ := if r = 0 then n else if r % 2 = n % 2 then 2 else 1

/-- `δ_r = a_r r! / gcd(n, r)`. -/
def delta (n r : ℕ) : ℕ := aa n r * r.factorial / Nat.gcd n r

/-- `α(ν)_s = ε_ν e_s [y^{s+1}] Φ_ν`. -/
noncomputable def alphaQ (n : ℕ) : Matrix (Fin n) n.Partition ℚ :=
  fun s ν => (eps ν : ℚ) * (ee n s : ℚ) * (PhiM ν.parts).coeff (s + 1)

/-- `Γ(μ,s) = (1/e_s) ∑_i η_μ(i) Q(i,s)`. -/
noncomputable def GamQ (n : ℕ) : Matrix n.Partition (Fin n) ℚ :=
  fun μ s => (∑ i : Fin n, ((eta μ i * Qf (n - 1) i s : ℤ) : ℚ)) / (ee n s : ℚ)

end StanleySnf
