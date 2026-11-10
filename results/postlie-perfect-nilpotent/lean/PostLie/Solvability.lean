import PostLie.TranslationPolynomial
import PostLie.WhiteheadStep

namespace PostLie

open LieAlgebra

variable {k g n : Type*} [Field k] [CharZero k]
  [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]
  [LieRing n] [LieAlgebra k n] [FiniteDimensional k n]
  [LieRing.IsNilpotent n]

/-- Successive translations move a semisimple subalgebra into each lower-central-series
term while keeping the first component invertible. -/
theorem cocycle_into_centralTerm
    (L : g →ₗ⁅k⁆ LieDerivation k n n) (e : g ≃ₗ[k] n)
    (he : IsCocycle L e.toLinearMap)
    (htrace : ∀ a, LinearMap.trace k n (L a).toLinearMap =
      LinearMap.trace k g (LieAlgebra.ad k g a))
    (s : LieSubalgebra k g) [LieAlgebra.IsSemisimple k s] (i : ℕ) :
    ∃ P : g ≃ₗ[k] n, IsCocycle L P.toLinearMap ∧
      ∀ x : s, P (x : g) ∈ centralTerm k n i := by
  induction i with
  | zero => exact ⟨e, he, fun _ => LieSubmodule.mem_top _⟩
  | succ i ih =>
    obtain ⟨P, hP, hc⟩ := ih
    let Ls := L.comp s.incl
    let c := P.toLinearMap.comp s.incl.toLinearMap
    have hC : IsCocycle Ls c := by
      intro x y
      exact hP (x : g) (y : g)
    obtain ⟨z, hz, hcorr⟩ := whitehead_correction Ls c hC i hc
    let T := translated L P.toLinearMap hP z
    let Q := LinearEquiv.ofBijective T (translated_bijective L P hP z htrace)
    refine ⟨Q, translated_isCocycle L P.toLinearMap hP z, ?_⟩
    intro x
    have hh := translated_mod_next L P.toLinearMap hP i z hz (x : g)
    have hh0 : (centralTerm k n (i + 1)).toSubmodule.mkQ
        (P (x : g) + L (x : g) z) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (hcorr x)
    exact (Submodule.Quotient.mk_eq_zero _).mp (hh.trans hh0)

/-- An invertible nonlinear cocycle into a nilpotent Lie algebra, with the trace condition,
forces the source Lie algebra to be solvable. -/
theorem solvable_of_invertible_cocycle
    (L : g →ₗ⁅k⁆ LieDerivation k n n) (e : g ≃ₗ[k] n)
    (he : IsCocycle L e.toLinearMap)
    (htrace : ∀ a, LinearMap.trace k n (L a).toLinearMap =
      LinearMap.trace k g (LieAlgebra.ad k g a)) :
    LieAlgebra.IsSolvable g := by
  by_contra h
  obtain ⟨s, hs, hsemi⟩ := levi_nonzero_semisimple k g h
  let : Nontrivial s := hs
  let : LieAlgebra.IsSemisimple k s := hsemi
  obtain ⟨r, hr⟩ := LieModule.IsNilpotent.nilpotent k n n
  obtain ⟨P, _, hPr⟩ := cocycle_into_centralTerm L e he htrace s r
  obtain ⟨x, hx⟩ := exists_ne (0 : s)
  have hzero := hPr x
  change P (x : g) ∈ LieModule.lowerCentralSeries k n n r at hzero
  rw [hr] at hzero
  have hPx : P (x : g) = 0 := by simpa only [LieSubmodule.mem_bot] using hzero
  have hxg : (x : g) = 0 := P.injective (hPx.trans P.map_zero.symm)
  exact hx (Subtype.ext hxg)

end PostLie
