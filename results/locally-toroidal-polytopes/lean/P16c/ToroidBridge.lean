import P16c.Toroid
import P16c.CoreProof

namespace P16c

/-- A faithful toroid realization, recording the actual generator map and its range. -/
def ToroidRealization {H : Type*} [Group H] (n : ℕ) (f : Fin 3 → H) : Prop :=
  ∃ φ : Toroid.G n →* H, (∀ i, φ (Toroid.r n i) = f i) ∧ Function.Injective φ ∧
    φ.range = Subgroup.closure ({f 0, f 1, f 2} : Set H)

/-- The core's exact cardinalities identify both local matrix groups with the toroid presentations. -/
lemma toroid_realizations {K : Type*} [Field K] [CharP K 2]
    (g : Fin 4 → (Mat K)ˣ) (s u : ℕ)
    (hs : 0 < s) (hu : 0 < u) (hcore : CoreConclusion g s u) :
    ToroidRealization s (fun i => g i.castSucc) ∧
      ToroidRealization u (fun i => g i.succ) := by
  obtain ⟨hi, h01, h12, h23, h02, _, h13, ht, hv, cf, cv, _⟩ := hcore
  have h01' : (g 0 * g 1) ^ 4 = 1 := by simpa only [h01] using pow_orderOf_eq_one (g 0 * g 1)
  have h12' : (g 1 * g 2) ^ 4 = 1 := by simpa only [h12] using pow_orderOf_eq_one (g 1 * g 2)
  have h23' : (g 2 * g 3) ^ 4 = 1 := by simpa only [h23] using pow_orderOf_eq_one (g 2 * g 3)
  have ht' : (g 0 * g 1 * g 2 * g 1) ^ s = 1 := by rw [← ht]; exact pow_orderOf_eq_one _
  have hv' : (g 1 * g 2 * g 3 * g 2) ^ u = 1 := by rw [← hv]; exact pow_orderOf_eq_one _
  constructor
  · let φ := Toroid.toGroup s (fun i : Fin 3 => g i.castSucc)
      (fun i => hi i.castSucc) h01' h12' h02 ht'
    have hφ (i : Fin 3) : φ (Toroid.r s i) = g i.castSucc := Toroid.toGroup_r ..
    refine ⟨φ, hφ, Toroid.injective_of_card s hs φ ?_, ?_⟩
    · simpa [hφ] using cf
    · simpa [hφ] using Toroid.range_eq s φ
  · let φ := Toroid.toGroup u (fun i : Fin 3 => g i.succ)
      (fun i => hi i.succ) h12' h23' h13 hv'
    have hφ (i : Fin 3) : φ (Toroid.r u i) = g i.succ := Toroid.toGroup_r ..
    refine ⟨φ, hφ, Toroid.injective_of_card u hu φ ?_, ?_⟩
    · simpa [hφ] using cv
    · simpa [hφ] using Toroid.range_eq u φ

/-- The facet and vertex-figure maps under precisely the existing core's hypotheses. -/
theorem p16c_toroid_bridge {K : Type*} [Field K] [CharP K 2]
    (s u : ℕ) (hs : Odd s) (hu : Odd u)
    (hs3 : 3 ≤ s) (hu3 : 3 ≤ u) (hsu : s ≠ u)
    (l m : K) (hl : orderOf l = s) (hm : orderOf m = u) :
    let g := generators (aParam l m) (bParam l m)
      (parameters s u hs3 hu3 hsu l m hl hm).2.2.1
    ToroidRealization s (fun i => g i.castSucc) ∧
      ToroidRealization u (fun i => g i.succ) :=
  toroid_realizations _ s u (by omega) (by omega)
    (core_for_parameters s u hs hu hs3 hu3 hsu l m hl hm)
end P16c
