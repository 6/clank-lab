import ErsConj13.R1Pieces
import MainLemma

/-!
# Realization: the ray-(2,1) function of `D₅` is `S⁵`

`D₅ = D((1+x)⁵, 1+y)` has a consistent family, and for every consistent family the function on
the ray `(2,1)` (slope `1/2`), a series in `t = x²y`, equals `S⁵`. The proof factors `T⁵`
(ordered factorization), transports the factorization to `D₅` by `u = x`, `w = xy`, builds `g_<`
and `g_>` from the factors, and applies `main_lemma`.
-/

namespace ErsConj13

open Scat

theorem ray21_eq_S5 :
    (∃ f, IsConsistentFamily ((1 + PowerSeries.X) ^ 5) (1 + PowerSeries.X) f) ∧
    ∀ f, IsConsistentFamily ((1 + PowerSeries.X) ^ 5) (1 + PowerSeries.X) f →
      f ((1 / 2 : ℚ≥0) : Slope) = S ^ 5 := by
  obtain ⟨φ, hφ⟩ := factor_exists T5 T5_isPoisson T5_unipotent.1 T5_unipotent.2
  refine ⟨⟨transportFam φ, transport_consistent φ hφ⟩, fun f hf => ?_⟩
  have hfe : f = transportFam φ := factor_unique _ f (transportFam φ)
    ((isConsistentFamily_iff _ _ _).mp hf)
    ((isConsistentFamily_iff _ _ _).mp (transport_consistent φ hφ))
  rw [hfe, transportFam_half]
  obtain ⟨gl, gr, hgl, hgr, hgr_filt, hgl_filt, hfac⟩ := realization φ hφ
  exact main_lemma Tmap (thetaMap _ (hφ.1 _)) gl gr (φ ((1 : ℚ≥0) : Slope)) Tmap_u Tmap_w
    (hφ.1 _) (thetaMap_u _ _) (thetaMap_w _ _) hgl hgr hgr_filt hgl_filt hfac

end ErsConj13
