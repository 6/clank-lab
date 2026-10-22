import Mathlib

namespace P16c

lemma commuting_pair_representation {G : Type*} [Group G] (x y : G)
    (hc : Commute x y) (hx : IsOfFinOrder x) (hy : IsOfFinOrder y)
    {z : G} (hz : z ∈ Subgroup.closure ({x, y} : Set G)) :
    ∃ i j : ℕ, x ^ i * y ^ j = z := by
  have hcomm : ∀ (a : Subgroup.zpowers x) (b : Subgroup.zpowers y), Commute (a : G) (b : G) := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact hc.zpow_zpow i j
  let f : Subgroup.zpowers x × Subgroup.zpowers y →* G :=
    (Subgroup.zpowers x).subtype.noncommCoprod (Subgroup.zpowers y).subtype hcomm
  have hr : f.range = Subgroup.closure ({x, y} : Set G) := by
    dsimp [f]
    rw [MonoidHom.noncommCoprod_range]
    simp only [Subgroup.range_subtype]
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
  rw [← hr] at hz
  obtain ⟨⟨a, b⟩, hab⟩ := hz
  obtain ⟨i, hi⟩ := hx.mem_powers_iff_mem_zpowers.mpr a.property
  obtain ⟨j, hj⟩ := hy.mem_powers_iff_mem_zpowers.mpr b.property
  change x ^ i = (a : G) at hi
  change y ^ j = (b : G) at hj
  change (a : G) * (b : G) = z at hab
  exact ⟨i, j, by rw [hi, hj]; exact hab⟩
end P16c
