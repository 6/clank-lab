import Mathlib

namespace P16c

lemma odd_order_mem_of_quotient_card_eight {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (hcard : Nat.card (G ⧸ N) = 8)
    (x : G) (hx : Odd (orderOf x)) : x ∈ N := by
  let y : G ⧸ N := QuotientGroup.mk' N x
  have hd : orderOf y ∣ 8 := by simpa [hcard] using orderOf_dvd_natCard y
  have ho : Odd (orderOf y) := Odd.of_dvd_nat hx (orderOf_map_dvd (QuotientGroup.mk' N) x)
  have hc : (orderOf y).Coprime 8 := ho.coprime_two_right.pow_right 3
  have heq : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes hc dvd_rfl hd
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp heq)
end P16c
