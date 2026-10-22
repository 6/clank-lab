import Statement
import P16c.Fields
import P16c.StringC
import P16c.Presentation
import P16c.GroupStringC
import P16c.LocalStringC

namespace P16c

/-- The core construction exists for every pair of distinct odd periods at least three. -/
theorem p16c_all (s u : ℕ) (hs : Odd s) (hu : Odd u)
    (hs3 : 3 ≤ s) (hu3 : 3 ≤ u) (hsu : s ≠ u) :
    ∃ (k : ℕ) (l m : GaloisField 2 k)
      (hl : orderOf l = s) (hm : orderOf m = u),
      CoreConclusion (generators (aParam l m) (bParam l m)
        (parameters s u hs3 hu3 hsu l m hl hm).2.2.1) s u := by
  obtain ⟨k, l, m, hl, hm⟩ := fields_exist s u hs hu
  exact ⟨k, l, m, hl, hm, p16c_core s u hs hu hs3 hu3 hsu l m hl hm⟩

/-- The four matrix generators satisfy the intersection property for all index subsets. -/
theorem p16c_matrix_stringC {K : Type*} [Field K] [CharP K 2]
    (s u : ℕ) (hs : Odd s) (hu : Odd u)
    (hs3 : 3 ≤ s) (hu3 : 3 ≤ u) (hsu : s ≠ u)
    (l m : K) (hl : orderOf l = s) (hm : orderOf m = u) :
    let g := generators (aParam l m) (bParam l m)
      (parameters s u hs3 hu3 hsu l m hl hm).2.2.1
    IsStringCGroup g := by
  have hp := parameters s u hs3 hu3 hsu l m hl hm
  obtain ⟨hf, hv⟩ := matrix_local_stringC (aParam l m) (bParam l m)
    hp.2.2.1 hp.2.2.2.1 (by rw [hp.2.2.2.2]; exact hp.1)
  exact matrix_stringC_of_locals _ s u
    (core_for_parameters s u hs hu hs3 hu3 hsu l m hl hm) hf hv

/-- The universal presentation has precisely the prescribed local toroids. -/
theorem p16c_universal_locals (s u : ℕ) (hs : Odd s) (hu : Odd u)
    (hs3 : 3 ≤ s) (hu3 : 3 ≤ u) (hsu : s ≠ u) :
    Nat.card (Subgroup.closure {Universal.r s u 0, Universal.r s u 1,
      Universal.r s u 2}) = 8 * s ^ 2 ∧
    Nat.card (Subgroup.closure {Universal.r s u 1, Universal.r s u 2,
      Universal.r s u 3}) = 8 * u ^ 2 ∧
    (∃ e : Toroid.G s ≃* Subgroup.closure {Universal.r s u 0,
        Universal.r s u 1, Universal.r s u 2},
      ∀ i : Fin 3, (e (Toroid.r s i) : Gamma s u) = Universal.r s u i.castSucc) ∧
    (∃ e : Toroid.G u ≃* Subgroup.closure {Universal.r s u 1,
        Universal.r s u 2, Universal.r s u 3},
      ∀ i : Fin 3, (e (Toroid.r u i) : Gamma s u) = Universal.r s u i.succ) := by
  obtain ⟨k, l, m, hl, hm⟩ := fields_exist s u hs hu
  let g := generators (aParam l m) (bParam l m)
    (parameters s u hs3 hu3 hsu l m hl hm).2.2.1
  have hc : CoreConclusion g s u := p16c_core s u hs hu hs3 hu3 hsu l m hl hm
  obtain ⟨hf, hv⟩ := Universal.local_maps_injective g s u (by omega) (by omega) hc
  obtain ⟨cf, cv⟩ := Universal.local_cards g s u (by omega) (by omega) hc
  exact ⟨cf, cv, ⟨Universal.facetEquiv hf, Universal.facetEquiv_r hf⟩,
    ⟨Universal.vertexEquiv hv, Universal.vertexEquiv_r hv⟩⟩

/-- The universal P16c group is a string C-group with the prescribed local toroids. -/
theorem p16c_universal_stringC (s u : ℕ) (hs : Odd s) (hu : Odd u)
    (hs3 : 3 ≤ s) (hu3 : 3 ≤ u) (hsu : s ≠ u) :
    IsStringCGroup (fun i : Fin 4 => (PresentedGroup.of i : Gamma s u)) ∧
    Nat.card (Subgroup.closure {Universal.r s u 0, Universal.r s u 1,
      Universal.r s u 2}) = 8 * s ^ 2 ∧
    Nat.card (Subgroup.closure {Universal.r s u 1, Universal.r s u 2,
      Universal.r s u 3}) = 8 * u ^ 2 ∧
    (∃ e : Toroid.G s ≃* Subgroup.closure {Universal.r s u 0,
        Universal.r s u 1, Universal.r s u 2},
      ∀ i : Fin 3, (e (Toroid.r s i) : Gamma s u) = Universal.r s u i.castSucc) ∧
    (∃ e : Toroid.G u ≃* Subgroup.closure {Universal.r s u 1,
        Universal.r s u 2, Universal.r s u 3},
      ∀ i : Fin 3, (e (Toroid.r u i) : Gamma s u) = Universal.r s u i.succ) := by
  refine ⟨?_, p16c_universal_locals s u hs hu hs3 hu3 hsu⟩
  obtain ⟨k, l, m, hl, hm⟩ := fields_exist s u hs hu
  have hp := parameters s u hs3 hu3 hsu l m hl hm
  obtain ⟨hf, hv⟩ := matrix_local_stringC (aParam l m) (bParam l m)
    hp.2.2.1 hp.2.2.2.1 (by rw [hp.2.2.2.2]; exact hp.1)
  exact Universal.stringC_of_core _ s u (by omega) (by omega)
    (core_for_parameters s u hs hu hs3 hu3 hsu l m hl hm) hf hv

end P16c
