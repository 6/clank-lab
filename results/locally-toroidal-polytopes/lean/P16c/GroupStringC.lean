import P16c.GroupFormProof
import P16c.StringCTheory

namespace P16c
variable {K : Type*} [Field K] [CharP K 2]
set_option maxHeartbeats 800000

/-- Assemble the full matrix intersection property from the two local ones. -/
lemma matrix_stringC_of_locals (g : Fin 4 → (Mat K)ˣ) (s u : ℕ)
    (hc : CoreConclusion g s u)
    (hf : IsStringCGroup (fun i : Fin 3 => g i.castSucc))
    (hv : IsStringCGroup (fun i : Fin 3 => g i.succ)) : IsStringCGroup g := by
  refine stringC_rank4 g hc.1 ?_ hf hv ?_
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij
    all_goals first
      | exact hc.2.2.2.2.1
      | exact hc.2.2.2.2.2.1
      | exact hc.2.2.2.2.2.2.1
  · simpa [parabolic, Set.image_insert_eq, Set.image_singleton] using
      hc.2.2.2.2.2.2.2.2.2.2.2

/-- The same local intersection properties assemble in the universal presentation. -/
lemma Universal.stringC_of_core (g : Fin 4 → (Mat K)ˣ) (s u : ℕ)
    (hs : 0 < s) (hu : 0 < u) (hc : CoreConclusion g s u)
    (hf : IsStringCGroup (fun i : Fin 3 => g i.castSucc))
    (hv : IsStringCGroup (fun i : Fin 3 => g i.succ)) :
    IsStringCGroup (Universal.r s u) := by
  obtain ⟨hf', hv'⟩ := Universal.local_stringC g s u hs hu hc hf hv
  refine stringC_rank4 (Universal.r s u) (Universal.relations s u).1 ?_ hf' hv' ?_
  · exact (Universal.string_relations s u).2
  · simpa [parabolic, Set.image_insert_eq, Set.image_singleton] using
      Universal.local_intersection g s u hs hu hc

end P16c
