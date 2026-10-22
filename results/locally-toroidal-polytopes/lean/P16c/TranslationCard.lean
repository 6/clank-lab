import P16c.Actions
import P16c.FacetPowers
import P16c.VertexPowers
import P16c.PairCard

namespace P16c
variable {K : Type*} [Field K] [CharP K 2]

lemma order_conjugate_involution {G : Type*} [Group G] (q x : G) (hq : q * q = 1) :
    orderOf (q * x * q) = orderOf x := by
  have hi : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq
  simpa [MulAut.conj_apply, hi] using
    (orderOf_injective (MulAut.conj q).toMonoidHom (MulAut.conj q).injective x)

/-- L4(ii), including the exact cardinality of the facet translation subgroup. -/
theorem af_card (a b l : K) (ha : a ≠ 0) (hl : l ≠ 0) (hl2 : l ^ 2 ≠ 1)
    (hs : Odd (orderOf l)) (hσ : a + b = traceParam l) :
    Nat.card (AF a b ha) = orderOf l ^ 2 := by
  apply commuting_pair_card _ _ _ hs.pos
  · rw [← orderOf_units]
    simpa using t_order a b l hl hl2 hσ
  · rw [← orderOf_units]
    simpa using t₂_order a b l hl hl2 hσ
  · exact tGen_commute a b ha
  · intro i j h
    apply facet_power_independence a b l hl hl2 hs hσ i j
    simpa using congrArg (fun x : (Mat K)ˣ => (x : Mat K)) h

/-- L4(iii), including the exact cardinality of the vertex translation subgroup. -/
theorem av_card (a b m : K) (ha : a ≠ 0) (hm : m ≠ 0) (hm2 : m ^ 2 ≠ 1)
    (hu : Odd (orderOf m)) (hτ : (a + b) ^ 2 / a = traceParam m) :
    Nat.card (AV a b ha) = orderOf m ^ 2 := by
  have hv : orderOf (vGen a b ha) = orderOf m := by
    rw [← orderOf_units]
    simpa using v_order a b m ha hm hm2 hτ
  apply commuting_pair_card _ _ _ hu.pos hv
  · exact (order_conjugate_involution (generators a b ha 2) (vGen a b ha)
      (generators_involutive a b ha 2)).trans hv
  · exact vGen_commute a b ha
  · intro i j h
    apply vertex_power_independence a b m ha hm hm2 hτ i j
    simpa using congrArg (fun x : (Mat K)ˣ => (x : Mat K)) h
end P16c
