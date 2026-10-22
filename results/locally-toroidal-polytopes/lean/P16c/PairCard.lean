import Mathlib

namespace P16c

/-- Two commuting, independent elements of period n generate exactly n² elements. -/
lemma commuting_pair_card {G : Type*} [Group G] (x y : G) (n : ℕ) (hn : 0 < n)
    (hx : orderOf x = n) (hy : orderOf y = n) (hcomm : Commute x y)
    (hind : ∀ i j : ℕ, x ^ i * y ^ j = 1 → n ∣ i ∧ n ∣ j) :
    Nat.card (Subgroup.closure ({x, y} : Set G)) = n ^ 2 := by
  have hxf : IsOfFinOrder x := orderOf_pos_iff.mp (hx ▸ hn)
  have hyf : IsOfFinOrder y := orderOf_pos_iff.mp (hy ▸ hn)
  have hdis : Disjoint (Subgroup.zpowers x) (Subgroup.zpowers y) := by
    apply Subgroup.disjoint_def.mpr
    intro z hz₁ hz₂
    obtain ⟨i, hi⟩ := hxf.mem_powers_iff_mem_zpowers.mpr hz₁
    obtain ⟨j, hj⟩ := hyf.mem_powers_iff_mem_zpowers.mpr ((Subgroup.zpowers y).inv_mem hz₂)
    change x ^ i = z at hi
    change y ^ j = z⁻¹ at hj
    have hprod : x ^ i * y ^ j = 1 := by rw [hi, hj, mul_inv_cancel]
    have hd := (hind i j hprod).1
    rw [← hx] at hd
    exact hi.symm.trans (orderOf_dvd_iff_pow_eq_one.mp hd)
  have hc : ∀ (a : Subgroup.zpowers x) (b : Subgroup.zpowers y), Commute (a : G) (b : G) := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact hcomm.zpow_zpow i j
  let f : Subgroup.zpowers x × Subgroup.zpowers y →* G :=
    (Subgroup.zpowers x).subtype.noncommCoprod (Subgroup.zpowers y).subtype hc
  have hf : Function.Injective f := by
    apply MonoidHom.noncommCoprod_injective _ _ _ |>.mpr
    exact ⟨Subtype.val_injective, Subtype.val_injective, by simpa using hdis⟩
  have hr : f.range = Subgroup.closure ({x, y} : Set G) := by
    dsimp [f]
    rw [MonoidHom.noncommCoprod_range]
    simp only [Subgroup.range_subtype]
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
  rw [← hr]
  calc
    Nat.card f.range = Nat.card (Subgroup.zpowers x × Subgroup.zpowers y) :=
      Nat.card_congr (Equiv.ofInjective f hf).symm
    _ = n ^ 2 := by rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, hx, hy, pow_two]
end P16c
