import Containment
import NormalForm
import Specialization
import Independence

namespace Makonzi
open scoped BigOperators
set_option synthInstance.maxHeartbeats 200000
noncomputable section

/-- All field-coefficient conventions in the two uniform bridges agree. -/
lemma coeffToRational_eq_C (p : Fin 3 → ℕ) (r : CoeffRing p) :
    coeffToRational p r =
      RatFunc.C (algebraMap (CoeffRing p) (CoeffField p) r) := by
  simp [coeffToRational, RatFunc.algebraMap_eq_C]

/-- The actual rational specialization detects zero normal forms over C[v]. -/
lemma normalForm_specialization_zero (p : Fin 3 → ℕ) (hp : ∀ i, 2 ≤ p i)
    (N : ℕ) (r : CoeffRing p) (a b c : Fin N → CoeffRing p)
    (h : ((psi p hp).comp (phi p)) (normalForm p N r a b c) = 0) :
    normalForm p N r a b c = 0 := by
  let ι := algebraMap (CoeffRing p) (CoeffField p)
  have hA : ι (armCoeff p 0) ≠ 0 :=
    (map_ne_zero_iff ι (coeffToField_injective p)).mpr (armCoeff_ne_zero p 0)
  have hB : ι (armCoeff p 1) ≠ 0 :=
    (map_ne_zero_iff ι (coeffToField_injective p)).mpr (armCoeff_ne_zero p 1)
  have hC : ι (armCoeff p 2) ≠ 0 :=
    (map_ne_zero_iff ι (coeffToField_injective p)).mpr (armCoeff_ne_zero p 2)
  have h' : RatFunc.C (ι r) +
      (∑ k : Fin N, RatFunc.C (ι (a k)) *
        (RatFunc.C (ι (armCoeff p 1)) *
          (RatFunc.X + RatFunc.C (ι (armCoeff p 2))) / RatFunc.X)^(k.val+1)) +
      (∑ k : Fin N, RatFunc.C (ι (b k)) *
        (RatFunc.C (ι (armCoeff p 0)) * RatFunc.X /
          (RatFunc.X + RatFunc.C (ι (armCoeff p 2))))^(k.val+1)) +
      (∑ k : Fin N, RatFunc.C (ι (c k)) * RatFunc.X^(k.val+1)) = 0 := by
    simpa only [normalForm, map_add, map_sum, map_mul, map_pow,
      psi_comp_phi_coeff_apply, psi_comp_phi_W0, psi_comp_phi_W1, psi_comp_phi_W2,
      armRational, coeffToRational_eq_C, T, RatFunc.algebraMap_X] using h
  obtain ⟨hr, ha, hb, hc⟩ := pure_powers_independent
    (ι (armCoeff p 0)) (ι (armCoeff p 1)) (ι (armCoeff p 2)) hA hB hC
    N (ι r) (fun k => ι (a k)) (fun k => ι (b k)) (fun k => ι (c k)) h'
  have hr0 : r = 0 := (coeffToField_injective p) (hr.trans (map_zero ι).symm)
  have ha0 : ∀ k, a k = 0 := fun k => (coeffToField_injective p) ((ha k).trans (map_zero ι).symm)
  have hb0 : ∀ k, b k = 0 := fun k => (coeffToField_injective p) ((hb k).trans (map_zero ι).symm)
  have hc0 : ∀ k, c k = 0 := fun k => (coeffToField_injective p) ((hc k).trans (map_zero ι).symm)
  simp [normalForm, hr0, ha0, hb0, hc0]

/-- The reverse containment uses uniform division and a genuine arrow map;
it imposes no localization hypothesis on the theorem's source ring. -/
theorem ker_le_minorIdeal (p : Fin 3 → ℕ) (hp : ∀ i, 2 ≤ p i) :
    RingHom.ker (phi p) ≤ minorIdeal p := by
  intro f hf
  obtain ⟨N, r, a, b, c, hNF⟩ := normalForm_exists p f
  have hdiff : phi p (f - normalForm p N r a b c) = 0 :=
    minorIdeal_le_ker p hNF
  have hf0 : phi p f = 0 := hf
  have hnf : phi p (normalForm p N r a b c) = 0 := by
    simpa only [map_sub, hf0, zero_sub, neg_eq_zero] using hdiff
  have hs : ((psi p hp).comp (phi p)) (normalForm p N r a b c) = 0 := by
    change psi p hp (phi p _) = 0
    rw [hnf, map_zero]
  have hz := normalForm_specialization_zero p hp N r a b c hs
  simpa only [hz, sub_zero] using hNF

/-- Corrected Conjecture 5.2, for every source-family arm triple over C. -/
theorem kernel_equality (p : Fin 3 → ℕ) (hp : ∀ i, 2 ≤ p i) :
    RingHom.ker (phi p) = minorIdeal p :=
  le_antisymm (ker_le_minorIdeal p hp) (minorIdeal_le_ker p)

/-- The frozen endpoint, with no additional hypotheses. -/
theorem endpoint : Endpoint := kernel_equality

#print axioms endpoint
#print axioms kernel_equality
end
end Makonzi
