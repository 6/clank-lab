import GraphDeciders

namespace BBPSplitStar
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

def CoverTree : List (Fin n) → Finset (Fin n) → Prop
  | [], S => RankCertificate G S ∨ ShortCycleOn G S
  | u :: us, S => CoverTree us S ∧ CoverTree us (insert u S)

instance coverTreeDecidable (us : List (Fin n)) (S : Finset (Fin n)) :
    Decidable (CoverTree G us S) := by
  induction us generalizing S with
  | nil => unfold CoverTree; infer_instance
  | cons u us ih => unfold CoverTree; exact instDecidableAnd

theorem coverTree_sound {us : List (Fin n)} {S T : Finset (Fin n)}
    (h : CoverTree G us S) (hT : T ⊆ us.toFinset) :
    RankCertificate G (S ∪ T) ∨ ShortCycleOn G (S ∪ T) := by
  induction us generalizing S T with
  | nil =>
    have : T = ∅ := by simpa using hT
    simpa [this, CoverTree] using h
  | cons u us ih =>
    have ht : T.erase u ⊆ us.toFinset := by
      intro v hv
      have hvT := (Finset.mem_erase.mp hv).2
      have hvu := (Finset.mem_erase.mp hv).1
      have := hT hvT
      simpa [List.toFinset_cons, Finset.mem_insert, hvu] using this
    by_cases hu : u ∈ T
    · have he : insert u S ∪ T.erase u = S ∪ T := by
        ext v
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
        by_cases hv : v = u
        · subst v; simp [hu]
        · simp [hv]
      simpa [he] using ih h.2 ht
    · have ht' : T ⊆ us.toFinset := by
        simpa [Finset.erase_eq_of_notMem hu] using ht
      exact ih h.1 ht'

theorem fullCoverage_of_coverTree
    (h : CoverTree G (List.finRange n) ∅) : FullCoverage G := by
  intro S hS
  have ht : S ⊆ (List.finRange n).toFinset := by
    intro u hu
    simp
  simpa using coverTree_sound G h ht
end BBPSplitStar
