import P16c.LocalCard
import P16c.TranslationIntersection
import P16c.OddQuotient

namespace P16c
variable {K : Type*} [Field K] [CharP K 2]
open scoped Pointwise

lemma odd_order_in_vertex (a b m : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hm : m ≠ 0) (hm2 : m ^ 2 ≠ 1) (hu : Odd (orderOf m))
    (hτ : (a + b) ^ 2 / a = traceParam m) (x : (Mat K)ˣ)
    (hx : x ∈ Ve a b ha) (hodd : Odd (orderOf x)) : x ∈ AV a b ha := by
  have havle : AV a b ha ≤ Ve a b ha := by rw [vertex_decomposition]; exact le_sup_left
  have hnorm : Ve a b ha ≤ Subgroup.normalizer (AV a b ha) := by
    rw [vertex_decomposition]
    exact sup_le Subgroup.le_normalizer (d_normalizes_av a b ha)
  let N := (AV a b ha).subgroupOf (Ve a b ha)
  haveI : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have hN : Nat.card N = orderOf m ^ 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe havle).toEquiv).trans
      (av_card a b m ha hm hm2 hu hτ)
  have hidx : N.index = 8 := by
    apply Nat.eq_of_mul_eq_mul_right (pow_pos hu.pos 2)
    simpa [hN, vertex_card a b m ha hb hm hm2 hu hτ] using N.index_mul_card
  have hqcard : Nat.card ((Ve a b ha) ⧸ N) = 8 := by rw [← N.index_eq_card, hidx]
  have hodd' : Odd (orderOf (⟨x, hx⟩ : Ve a b ha)) := by
    simpa only [← Subgroup.orderOf_coe] using hodd
  exact odd_order_mem_of_quotient_card_eight N hqcard ⟨x, hx⟩ hodd'

/-- L5: the local groups meet exactly in their common dihedral subgroup. -/
theorem local_intersection (a b l m : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hl : l ≠ 0) (hl2 : l ^ 2 ≠ 1) (hm : m ≠ 0) (hm2 : m ^ 2 ≠ 1)
    (hs : Odd (orderOf l)) (hu : Odd (orderOf m))
    (hσ : a + b = traceParam l) (hτ : (a + b) ^ 2 / a = traceParam m) :
    F a b ha ⊓ Ve a b ha = D a b ha := by
  have hDF : D a b ha ≤ F a b ha := by rw [facet_decomposition]; exact le_sup_right
  have hDV : D a b ha ≤ Ve a b ha := by rw [vertex_decomposition]; exact le_sup_right
  apply le_antisymm
  · intro x hx
    have hxprod : x ∈ ((AF a b ha : Set (Mat K)ˣ) * (D a b ha : Set (Mat K)ˣ)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ (d_normalizes_af a b ha),
        ← facet_decomposition]
      exact hx.1
    obtain ⟨t, ht, d, hd, htd⟩ := hxprod
    change t * d = x at htd
    have htV : t ∈ Ve a b ha := by
      have h := (Ve a b ha).mul_mem hx.2 ((Ve a b ha).inv_mem (hDV hd))
      rw [← htd] at h
      simpa [mul_assoc] using h
    have hodd : Odd (orderOf t) := by
      have hdiv := (AF a b ha).orderOf_dvd_natCard ht
      rw [af_card a b l ha hl hl2 hs hσ] at hdiv
      exact Odd.of_dvd_nat hs.pow hdiv
    have htA := odd_order_in_vertex a b m ha hb hm hm2 hu hτ t htV hodd
    have ht1 : t = 1 := Subgroup.disjoint_def.mp
      (translation_intersection a b l ha hl hl2 hs hσ) ht htA
    rw [ht1, one_mul] at htd
    simpa [htd] using hd
  · exact le_inf hDF hDV
end P16c
