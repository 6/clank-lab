import GraphBridge

namespace BBPSplitStar
instance graphFromComplementDecidableAdj (n : ℕ) (E : Finset (ℕ × ℕ)) :
    DecidableRel (graphFromComplement n E).Adj := by
  unfold graphFromComplement
  infer_instance
instance candidateDecidableAdj : DecidableRel candidate.Adj :=
  graphFromComplementDecidableAdj 12 candidatePairs
instance jDecidableAdj (n : ℕ) : DecidableRel (J n).Adj :=
  graphFromComplementDecidableAdj n (complementPairs n)
end BBPSplitStar
