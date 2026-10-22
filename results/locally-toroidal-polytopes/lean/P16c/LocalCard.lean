import P16c.Dihedral
import P16c.Decomposition
import P16c.TranslationCard
import P16c.ProductCard

namespace P16c
variable {K : Type*} [Field K] [CharP K 2]

lemma odd_coprime_eight {n : ℕ} (h : Odd n) : n.Coprime 8 :=
  h.coprime_two_right.pow_right 3

theorem facet_card (a b l : K) (ha : a ≠ 0) (hb : b ≠ 0) (hl : l ≠ 0) (hl2 : l ^ 2 ≠ 1)
    (hs : Odd (orderOf l)) (hσ : a + b = traceParam l) :
    Nat.card (F a b ha) = 8 * orderOf l ^ 2 := by
  have haf := af_card a b l ha hl hl2 hs hσ
  have hd := d_card a b ha hb
  have hdis : Disjoint (AF a b ha) (D a b ha) := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [haf, hd]
    exact odd_coprime_eight hs.pow
  rw [facet_decomposition, normalized_sup_card _ _ (d_normalizes_af a b ha) hdis, haf, hd]
  exact Nat.mul_comm _ _

theorem vertex_card (a b m : K) (ha : a ≠ 0) (hb : b ≠ 0) (hm : m ≠ 0) (hm2 : m ^ 2 ≠ 1)
    (hu : Odd (orderOf m)) (hτ : (a + b) ^ 2 / a = traceParam m) :
    Nat.card (Ve a b ha) = 8 * orderOf m ^ 2 := by
  have hav := av_card a b m ha hm hm2 hu hτ
  have hd := d_card a b ha hb
  have hdis : Disjoint (AV a b ha) (D a b ha) := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hav, hd]
    exact odd_coprime_eight hu.pow
  rw [vertex_decomposition, normalized_sup_card _ _ (d_normalizes_av a b ha) hdis, hav, hd]
  exact Nat.mul_comm _ _
end P16c
