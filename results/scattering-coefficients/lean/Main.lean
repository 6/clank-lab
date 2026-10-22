import ErsConj13.R2Pieces
import Realization
import ErsConj13.Extraction

/-!
# Elgin–Reading–Stella Conjecture 13

Burcroff, Lee, Mou, Musiker and Reineke (arXiv 2511.14672, §2) define `D_{(b,c)} =
D(1 + x^b, 1 + y^c)`, the scattering diagram of Gross, Pandharipande and Siebert, and
`τ^{(b,c)}(kd, ke)` as the coefficient of `x^{kdb} y^{kec}` in its function on the ray
`ℝ_{≤0}(db, ec)` (their eq. (2.2)). This is the convention of the table and code of Elgin,
Reading and Stella (arXiv 2404.11381). Burcroff et al. draw rays with the sign convention of
Gross–Hacking–Keel–Kontsevich; in the convention of Gross–Pandharipande–Siebert §1.3
(`ErsConj13/ScatDefs.lean`), where `z^m` propagates in the direction `m`, the same wall is the
ray `ℝ_{≥0}(db, ec)` with the same function. For `(b,c) = (1,5)` and `(d,e) = (2,1)`,
`τ^{1,5}(2j, j)` is the `t^j` coefficient, `t = x²y⁵`, of the function of `D(1+x, 1+y⁵)` on the
ray `(2,5)` (slope `5/2`). Elgin–Reading–Stella Conjecture 13 states
`τ^{1,5}(2j, j) = (1/j) Σ_ℓ C(ℓ, j−ℓ+1)·C(j+ℓ−1, ℓ)` (`ersCoeff j`, `ErsConj13/Defs.lean`)
for `j ≥ 1`. The first conjunct says that a consistent family exists, so the second is not
vacuous; uniqueness of the family is proved along the way (`factor_unique`).
-/

namespace ErsConj13

open Scat

theorem ers_conjecture_13 :
    (∃ f, IsConsistentFamily (1 + PowerSeries.X) (1 + PowerSeries.X ^ 5) f) ∧
    ∀ f, IsConsistentFamily (1 + PowerSeries.X) (1 + PowerSeries.X ^ 5) f →
      ∀ j, 1 ≤ j → PowerSeries.coeff j (f ((5 / 2 : ℚ≥0) : Slope)) = ersCoeff j := by
  obtain ⟨⟨φ, hφ⟩, h21⟩ := ray21_eq_S5
  have hc := transport5_consistent φ hφ
  refine ⟨⟨fam5 φ, hc⟩, fun f hf j hj => ?_⟩
  have hfe : f = fam5 φ := factor_unique _ f (fam5 φ)
    ((isConsistentFamily_iff _ _ _).mp hf) ((isConsistentFamily_iff _ _ _).mp hc)
  have hroot := root5_pow (φ ((1 / 2 : ℚ≥0) : Slope)) (hφ.1 _)
  have hS : root5 (φ ((1 / 2 : ℚ≥0) : Slope)) = S :=
    pow5_injective hroot.1 S_const (hroot.2.trans (h21 φ hφ))
  rw [hfe, fam5_52, hS, S, PowerSeries.coeff_mk, if_neg (by omega)]

end ErsConj13
