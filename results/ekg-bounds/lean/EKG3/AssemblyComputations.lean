import EKG3.TheoremTP3
import EKG3.LemmaFP3

namespace EKG3

/-- Conjecture 3 from the computed prefix and the certified P3/B3′/L1 cover.
Every analytic estimate is proved in the imported dependency cone. -/
theorem conj3_of_computations : Conj3OfComputationsStatement := by
  intro hfa hfb hfc hc
  have ht := P3.theoremT hfa hfb hfc hc
  have hf := P3.lemmaF ⟨ht.2.2, hfb⟩
  intro i
  by_cases hi : i+1 ≤ L
  · exact hfa i hi
  · have hiL : L < i+1 := by omega
    have hstrict : 13*(i+1) < 28*EKG.actualA i ∧ 7*EKG.actualA i < 12*(i+1) := by
      by_cases hn : i+1 < 10^156
      · exact ht.2.1 i hiL (hn.trans (by norm_num))
      · exact hf i (by omega)
    have h28 : i+1 ≠ 28 := by dsimp [L] at hiL; omega
    have h7 : i+1 ≠ 7 := by dsimp [L] at hiL; omega
    exact ⟨⟨hstrict.1.le,hstrict.2.le⟩, by omega, by omega⟩

end EKG3
