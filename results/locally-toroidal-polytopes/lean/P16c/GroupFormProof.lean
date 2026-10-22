import P16c.Presentation
import P16c.StringCTransfer

namespace P16c.Universal
variable {K : Type*} [Field K] [CharP K 2]

/-- The universal facet and vertex subgroups meet in the middle dihedral subgroup. -/
lemma local_intersection (g : Fin 4 → (Mat K)ˣ) (s u : ℕ)
    (hs : 0 < s) (hu : 0 < u) (hc : CoreConclusion g s u) :
    Subgroup.closure {r s u 0, r s u 1, r s u 2} ⊓
        Subgroup.closure {r s u 1, r s u 2, r s u 3} =
      Subgroup.closure {r s u 1, r s u 2} := by
  apply inf_eq_of_map_inf_eq (coreMap g s u hc)
  · apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  · apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  · exact coreMap_injOn_facet g s u hs hu hc
  · simpa only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
      coreMap_r] using hc.2.2.2.2.2.2.2.2.2.2.2

/-- Faithful local matrix images reflect both local intersection properties. -/
lemma local_stringC (g : Fin 4 → (Mat K)ˣ) (s u : ℕ)
    (hs : 0 < s) (hu : 0 < u) (hc : CoreConclusion g s u)
    (hf : IsStringCGroup (fun i : Fin 3 => g i.castSucc))
    (hv : IsStringCGroup (fun i : Fin 3 => g i.succ)) :
    IsStringCGroup (fun i : Fin 3 => r s u i.castSucc) ∧
    IsStringCGroup (fun i : Fin 3 => r s u i.succ) := by
  constructor
  · apply IsStringCGroup.of_injOn _ (coreMap g s u hc)
      (Subgroup.closure {r s u 0, r s u 1, r s u 2})
    · intro i
      fin_cases i <;> exact Subgroup.subset_closure (by simp)
    · exact coreMap_injOn_facet g s u hs hu hc
    · simpa only [coreMap_r] using hf
  · apply IsStringCGroup.of_injOn _ (coreMap g s u hc)
      (Subgroup.closure {r s u 1, r s u 2, r s u 3})
    · intro i
      fin_cases i <;> exact Subgroup.subset_closure (by simp)
    · exact coreMap_injOn_vertex g s u hs hu hc
    · simpa only [coreMap_r] using hv

end P16c.Universal
