import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Endpoint statement (the paper)

`V = (ZMod 2)^7`, the dot product is Mathlib's `dotProduct` (`⬝ᵥ`), and for a
connection set `S` the eigenvalue of the character `a` is
`λ_a = Σ_{s∈S} (-1)^{a·s}`. `K S` is the set of `g` with `a·g = b·g` whenever
`λ_a = λ_b`; by R1 (the paper) it is the set of vertices strongly
cospectral with `0` in `Cay(Z_2^7, S)`.
-/

namespace CubelikeSC

/-- The vertex set `Z_2^7`. -/
abbrev V := Fin 7 → ZMod 2

/-- `λ_a = Σ_{s∈S} (-1)^{a·s}`. -/
def lam (S : Finset V) (a : V) : ℤ := ∑ s ∈ S, (-1) ^ (a ⬝ᵥ s).val

/-- `K(S) = {g : ∀ a b, λ_a = λ_b → a·g = b·g}`. -/
def K (S : Finset V) : Finset V :=
  Finset.univ.filter fun g => ∀ a b : V, lam S a = lam S b → a ⬝ᵥ g = b ⬝ᵥ g

/-- The endpoint: for every connection set `S ⊆ Z_2^7 \ {0}`, `|K(S)| ≤ 4`. -/
def Endpoint : Prop := ∀ S : Finset V, (0 : V) ∉ S → (K S).card ≤ 4

/-! ## Strong cospectrality (Árnadóttir–Godsil §2, Godsil–Smith) -/

/-- The adjacency matrix of `Cay(Z_2^7, S)`: `A x y = 1` iff `x - y ∈ S`. -/
def adj (S : Finset V) : Matrix V V ℝ := fun x y => if x - y ∈ S then 1 else 0

/-- `u` and `v` are strongly cospectral in `Cay(Z_2^7, S)`: for every eigenvalue `θ`
of `A`, the orthogonal projection `E_θ` onto the `θ`-eigenspace (acting on
`ℝ^V` with the standard inner product) has `E_θ e_u = E_θ e_v` or
`E_θ e_u = -E_θ e_v`. -/
def StronglyCospectral (S : Finset V) (u v : V) : Prop :=
  ∀ θ : ℝ, Module.End.HasEigenvalue (Matrix.toEuclideanLin (adj S)) θ →
    let E := Module.End.eigenspace (Matrix.toEuclideanLin (adj S)) θ
    E.starProjection (EuclideanSpace.single u 1) = E.starProjection (EuclideanSpace.single v 1) ∨
      E.starProjection (EuclideanSpace.single u 1) = -E.starProjection (EuclideanSpace.single v 1)

/-- The theorem of the paper: every set of pairwise strongly cospectral vertices of
a cubelike graph on 128 vertices has at most 4 elements. -/
def EndpointSC : Prop :=
  ∀ S : Finset V, (0 : V) ∉ S → ∀ P : Finset V,
    (∀ u ∈ P, ∀ v ∈ P, StronglyCospectral S u v) → P.card ≤ 4

end CubelikeSC
