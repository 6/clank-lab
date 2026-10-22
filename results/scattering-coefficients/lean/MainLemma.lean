import ErsConj13.Binomial

/-!
# The Main Lemma: the diagonal wall of `T⁵`

`T` is the ring automorphism of `A = ℚ⟦u,w⟧` with `T(u) = u(1+u+w)/(1+u)` and
`T(w) = w/(1+u)`, and `θ` is the diagonal wall `u ↦ u F(uw)`, `w ↦ w / F(uw)` (both written
without division, since `1 + u` and `F(uw)` are units). `gl` and `gr` are `g_<` and `g_>`:
automorphisms commuting with the Poisson bracket, with `g_>(z^m) ∈ z^m (1 + 𝒪_{h≥1})` and
`g_<⁻¹(z^m) ∈ z^m (1 + 𝒪_{h≤−1})` for every monomial `z^m`. If `T⁵ = g_< ∘ θ ∘ g_>`, then
`F = S⁵`, where `S` is the series of `ErsConj13.Defs`. The pieces are in `ErsConj13.Pieces`
and `ErsConj13.Binomial`.
-/

namespace ErsConj13

open MvPowerSeries

theorem main_lemma (T θ gl gr : A ≃+* A) (F : PowerSeries ℚ)
    (hTu : T u * (1 + u) = u * (1 + u + w))
    (hTw : T w * (1 + u) = w)
    (hF : PowerSeries.constantCoeff F = 1)
    (hθu : θ u = u * diag F)
    (hθw : θ w * diag F = w)
    (hgl : ∀ f g, gl (bracket f g) = bracket (gl f) (gl g))
    (hgr : ∀ f g, gr (bracket f g) = bracket (gr f) (gr g))
    (hgr_filt : ∀ m : Fin 2 →₀ ℕ, ∃ a ∈ OGe 1, gr (monomial m 1) = monomial m 1 * (1 + a))
    (hgl_filt : ∀ m : Fin 2 →₀ ℕ, ∃ a ∈ OLe (-1),
      gl.symm (monomial m 1) = monomial m 1 * (1 + a))
    (hfac : ∀ f, (⇑T)^[5] f = gl (θ (gr f))) :
    F = S ^ 5 := by
  -- the filtration data on the generators (`X i = monomial (single i 1) 1`)
  obtain ⟨a₁, ha₁, hgl_u⟩ := hgl_filt (Finsupp.single (0 : Fin 2) 1)
  obtain ⟨a₂, ha₂, hgl_w⟩ := hgl_filt (Finsupp.single (1 : Fin 2) 1)
  obtain ⟨b₁, hb₁, hgr_u⟩ := hgr_filt (Finsupp.single (0 : Fin 2) 1)
  obtain ⟨b₂, hb₂, hgr_w⟩ := hgr_filt (Finsupp.single (1 : Fin 2) 1)
  change gl.symm u = u * (1 + a₁) at hgl_u
  change gl.symm w = w * (1 + a₂) at hgl_w
  change gr u = u * (1 + b₁) at hgr_u
  change gr w = w * (1 + b₂) at hgr_w
  -- V1
  obtain ⟨β, hβ0, hP⟩ := V1 T θ gl gr F hTu hTw hF hθu hθw a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂
    hgl_u hgl_w hgr_u hgr_w hfac
  -- Lemma E: the factorization of 1 + P and the cocycle
  obtain ⟨ρ, δ, hρ0, hρδ, hρβ⟩ := quad_root F β hF hβ0
  have hfac1 := one_add_P_factor F β ρ δ hρδ hρβ
  have hcoc := cocycle T θ gl gr F hTu hTw hθu hθw a₁ a₂ b₁ b₂ hgl_u hgl_w hgr_u hgr_w hfac
  rw [hP, hfac1] at hcoc
  obtain ⟨hF2, hE⟩ := lemma_E θ F ρ δ hF hρ0 hθu hθw a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ hcoc
  -- Lemma SE and the ODE
  have hSE := lemma_SE gl.symm (isPoisson_symm gl hgl) a₁ a₂ δ ha₁ hgl_u hgl_w hE
  have hPform : gl.symm (u + w) = (diag ρ + w) * (1 + u * diag δ) - 1 := by
    rw [← hfac1, hP]; ring
  rw [hPform] at hSE
  have hΦ := ode_of_SE ρ δ hSE
  have hδ0 : PowerSeries.constantCoeff δ = 1 := by
    have h := congrArg PowerSeries.constantCoeff hρδ
    rwa [map_mul, hρ0, hF, one_mul] at h
  have hsq : δ ^ 2 = ρ ^ 3 := by
    have hρne : ρ ^ 2 ≠ 0 := pow_ne_zero _ (fun h => by simp [h] at hρ0)
    refine mul_left_cancel₀ hρne ?_
    rw [← mul_pow, hρδ, hF2]; ring
  -- c = 5 and the binomial series; uniqueness
  have hS2 : PowerSeries.constantCoeff (S ^ 2) = 1 := by simp [S_const]
  have hS3 : PowerSeries.constantCoeff (S ^ 3) = 1 := by simp [S_const]
  obtain ⟨h1, h2⟩ := ode_unique ρ δ (S ^ 2) (S ^ 3) hρ0 hδ0 hS2 hS3 hΦ
    (c5_identity S S_cubic) hsq (by ring)
  rw [← hρδ, h1, h2]; ring

end ErsConj13
