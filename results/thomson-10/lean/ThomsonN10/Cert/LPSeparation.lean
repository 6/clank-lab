import ThomsonN10.Interfaces
import ThomsonN10.Cert.LP.Proof

namespace ThomsonN10.Cert

theorem LPSeparation_holds : ThomsonN10.Interfaces.LPSeparation := by
  intro x hx he i j hij
  have he' : LP.energy x ≤ (32717/1000 : ℝ) := by
    simpa only [LP.energy, coulombEnergy, energyCap, Rat.cast_div, Rat.cast_ofNat,
    show ∀ i : Fin 10, Finset.univ.filter (fun j : Fin 10 => i < j) = Finset.Ioi i by
        intro i; ext j; simp] using he

  simpa [pairCap] using LP.lp_separation x hx.1 hx.2 he' i j hij

end ThomsonN10.Cert
#print axioms ThomsonN10.Cert.LPSeparation_holds
