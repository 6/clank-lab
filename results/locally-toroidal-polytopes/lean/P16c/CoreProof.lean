import P16c.Intersection
import P16c.StringRelations

namespace P16c
variable {K : Type*} [Field K] [CharP K 2]

lemma core_of_parameters (a b l m : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hl : l ≠ 0) (hl2 : l ^ 2 ≠ 1) (hm : m ≠ 0) (hm2 : m ^ 2 ≠ 1)
    (hs : Odd (orderOf l)) (hu : Odd (orderOf m))
    (hσ : a + b = traceParam l) (hτ : (a + b) ^ 2 / a = traceParam m) :
    CoreConclusion (generators a b ha) (orderOf l) (orderOf m) := by
  obtain ⟨hi, h01, h12, h23, h02, h03, h13⟩ := string_relations a b ha hb
    (by rw [hσ]; exact traceParam_ne_zero hl hl2)
  refine ⟨hi, h01, h12, h23, h02, h03, h13, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← orderOf_units]
    exact t_order a b l hl hl2 hσ
  · rw [← orderOf_units]
    exact v_order a b m ha hm hm2 hτ
  · exact facet_card a b l ha hb hl hl2 hs hσ
  · exact vertex_card a b m ha hb hm hm2 hu hτ
  · exact local_intersection a b l m ha hb hl hl2 hm hm2 hs hu hσ hτ

lemma core_for_parameters (s u : ℕ) (hs : Odd s) (hu : Odd u)
    (hs3 : 3 ≤ s) (hu3 : 3 ≤ u) (hsu : s ≠ u)
    (l m : K) (hl : orderOf l = s) (hm : orderOf m = u) :
    CoreConclusion (generators (aParam l m) (bParam l m)
      (parameters s u hs3 hu3 hsu l m hl hm).2.2.1) s u := by
  obtain ⟨hσ, hτ, ha, hb, hab⟩ := parameters s u hs3 hu3 hsu l m hl hm
  have hh := core_of_parameters (aParam l m) (bParam l m) l m ha hb
    (nonzero_of_order_ge_three hl hs3) (sq_ne_one_of_order_ge_three hl hs3)
    (nonzero_of_order_ge_three hm hu3) (sq_ne_one_of_order_ge_three hm hu3)
    (hl ▸ hs) (hm ▸ hu) hab (parameter_tau l m hσ hτ)
  simpa only [hl, hm] using hh
end P16c
