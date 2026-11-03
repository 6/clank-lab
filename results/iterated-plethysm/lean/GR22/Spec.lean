import GR22.Endpoint

/-!
# Interface statements between proof units

The specialization at the virtual alphabet `A = 1 - x - y`: `p_k ↦ 1 - x^k - y^k`, into
`ℚ[x, y]`. Each `Prop` below is a proof obligation of one unit; no unit assumes another's
statement except through the explicit hypotheses of `fullEndpoint_of` (unit C) and
`question1_of` (unit E), which the final assembly discharges.
-/

noncomputable section
namespace GR22

open MvPolynomial

abbrev XY := MvPolynomial (Fin 2) ℚ
def x : XY := X 0
def y : XY := X 1
def Q : XY := (1 - x) * (1 - y)

/-- The plethystic specialization `f ↦ f[1 - x - y]`. -/
def atA : SF →ₐ[ℚ] XY := aeval (fun i : ℕ => 1 - x ^ (i + 1) - y ^ (i + 1))

/-- `x ↦ x^k`, `y ↦ y^k`. -/
def frob (k : ℕ) : XY →ₐ[ℚ] XY := aeval (fun j : Fin 2 => X j ^ k)

/-- `h_γ(x, y) = ∑_{k=0}^γ x^k y^(γ-k)`. -/
def twoComplete (γ : ℕ) : XY := ∑ k ∈ Finset.range (γ + 1), x ^ k * y ^ (γ - k)

/-- `x ↦ 1`. -/
def atXOne : XY →ₐ[ℚ] XY := aeval (fun j : Fin 2 => if j = 0 then 1 else y)

/-- Unit A: `h_n[1 - x - y]`. -/
def AtAComplete : Prop :=
  atA (complete 0) = 1 ∧ atA (complete 1) = 1 - x - y ∧ ∀ n, 2 ≤ n → atA (complete n) = Q

/-- Unit A: specializing a plethysm. -/
def AtAPlethysm : Prop :=
  ∀ f g : SF, atA (plethysm f g) = eval₂ C (fun i : ℕ => frob (i + 1) (atA g)) f

/-- Unit B: Schur functions at `1 - x - y` (Jacobi–Trudi computation, all partitions). -/
def SchurAtA : Prop :=
  (∀ α β γ : ℕ, 2 ≤ α →
    atA (schur (α :: (List.replicate β 2 ++ List.replicate γ 1))) =
      (-1) ^ γ * Q * (x * y) ^ β * twoComplete γ) ∧
  (∀ (N : ℕ) (μ : List ℕ), IsPartitionOf N μ → 3 ≤ μ.getD 1 0 → atA (schur μ) = 0) ∧
  (∀ N : ℕ, atXOne (atA (schur (List.replicate N 1))) = (-y) ^ N)

end GR22
