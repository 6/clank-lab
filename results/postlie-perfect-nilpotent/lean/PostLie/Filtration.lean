import PostLie.Translation
import PostLie.ExponentialRemainder

namespace PostLie

open LieAlgebra

variable {k g n : Type*} [Field k]
  [LieRing g] [LieAlgebra k g] [LieRing n] [LieAlgebra k n]

/-- The lower central series, indexed with the whole algebra at zero. -/
abbrev centralTerm (k n : Type*) [Field k] [LieRing n] [LieAlgebra k n] (i : ℕ) :
    LieIdeal k n := LieModule.lowerCentralSeries k n n i

lemma bracket_mem_next (i : ℕ) (x y : n) (hy : y ∈ centralTerm k n i) :
    ⁅x, y⁆ ∈ centralTerm k n (i + 1) := by
  rw [centralTerm, LieModule.lowerCentralSeries_succ]
  exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) hy

lemma bracket_mem_next_left (i : ℕ) (x y : n) (hx : x ∈ centralTerm k n i) :
    ⁅x, y⁆ ∈ centralTerm k n (i + 1) := by
  rw [← lie_skew x y]
  exact (centralTerm k n (i + 1)).neg_mem (bracket_mem_next i y x hx)

/-- Derivations preserve every term of the lower central series. -/
lemma derivation_mem_centralTerm (D : LieDerivation k n n) (i : ℕ) (x : n)
    (hx : x ∈ centralTerm k n i) : D x ∈ centralTerm k n i := by
  induction i generalizing x with
  | zero => exact LieSubmodule.mem_top _
  | succ i ih =>
    have hx' : x ∈ (centralTerm k n (i + 1)).toSubmodule := hx
    rw [centralTerm, LieModule.lowerCentralSeries_succ,
      LieSubmodule.lieIdeal_oper_eq_linear_span] at hx'
    have hs : Submodule.span k { ⁅(a : n), (b : n)⁆ |
        (a : (⊤ : LieIdeal k n)) (b : centralTerm k n i) } ≤
        (centralTerm k n (i + 1)).toSubmodule.comap D.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a, b, rfl⟩
      change D ⁅(a : n), (b : n)⁆ ∈ centralTerm k n (i + 1)
      rw [D.apply_lie_eq_add]
      exact (centralTerm k n (i + 1)).add_mem
        (bracket_mem_next i (a : n) (D b) (ih b b.property))
        (bracket_mem_next i (D a) (b : n) b.property)
    exact hs hx'

section Translation

variable [CharZero k] [LieRing.IsNilpotent n]

local instance rationalFiltration (L : g →ₗ⁅k⁆ LieDerivation k n n) :
    Module ℚ (SemiDirectSum n g L) := Module.compHom _ (Rat.castHom k)

/-- Translation by a vector in a central-series term is affine modulo the next term. -/
lemma translated_mod_next
    (L : g →ₗ⁅k⁆ LieDerivation k n n) (P : g →ₗ[k] n) (hP : IsCocycle L P)
    (i : ℕ) (z : n) (hz : z ∈ centralTerm k n i) (x : g) :
    (centralTerm k n (i + 1)).toSubmodule.mkQ (translated L P hP z x) =
      (centralTerm k n (i + 1)).toSubmodule.mkQ (P x + L x z) := by
  let J := (centralTerm k n (i + 1)).toSubmodule
  let : Module ℚ (n ⧸ J) := Module.compHom _ (Rat.castHom k)
  let q := J.mkQ
  let D := (translationDerivation L z).toLinearMap
  let F := q.comp (SemiDirectSum.projl L)
  have hb (v : n) : q ⁅z, v⁆ = 0 := by
    exact (Submodule.Quotient.mk_eq_zero J).mpr (bracket_mem_next_left i z v hz)
  have hFD (h : SemiDirectSum n g L) : F (D h) = q (L h.right z) := by
    change q (translationDerivation L z h).left = _
    rw [translationDerivation_apply]
    simp only [map_add, map_neg, hb, neg_zero, zero_add]
  have hF : F.comp (D ^ 2) = 0 := by
    apply LinearMap.ext
    intro h
    change F ((D ^ 2) h) = 0
    rw [pow_two, Module.End.mul_apply, hFD]
    change q (L (translationDerivation L z h).right z) = 0
    simp
  have hh := projected_exp_eq D (translationDerivation_nilpotent L z) F hF
    (graph L P hP x)
  rw [hFD] at hh
  change q (translated L P hP z x) = q (P x) + q (L x z) at hh
  simpa only [map_add] using hh

end Translation

end PostLie
