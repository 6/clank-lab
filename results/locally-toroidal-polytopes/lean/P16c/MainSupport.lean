import StatementGroupForm

namespace P16c.Universal

/-- The adjacent products of `Γ(s,u)` have order exactly 4: they divide 4 by the
relations and map onto matrices of order 4. -/
lemma adjacent_orders (s u : ℕ) (hs : Odd s) (hu : Odd u) (hs3 : 3 ≤ s) (hu3 : 3 ≤ u)
    (hsu : s ≠ u) :
    orderOf (r s u 0 * r s u 1) = 4 ∧ orderOf (r s u 1 * r s u 2) = 4 ∧
      orderOf (r s u 2 * r s u 3) = 4 := by
  obtain ⟨k, l, m, hl, hm⟩ := fields_exist s u hs hu
  have hc := core_for_parameters s u hs hu hs3 hu3 hsu l m hl hm
  set g := generators (aParam l m) (bParam l m) (parameters s u hs3 hu3 hsu l m hl hm).2.2.1
  have hrel := relations s u
  have key : ∀ i j : Fin 4, (r s u i * r s u j) ^ 4 = 1 → orderOf (g i * g j) = 4 →
      orderOf (r s u i * r s u j) = 4 := by
    intro i j h4 hg
    apply Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one h4)
    have := orderOf_map_dvd (coreMap g s u hc) (r s u i * r s u j)
    rwa [map_mul, coreMap_r, coreMap_r, hg] at this
  exact ⟨key 0 1 hrel.2.1 hc.2.1, key 1 2 hrel.2.2.1 hc.2.2.1,
    key 2 3 hrel.2.2.2.1 hc.2.2.2.1⟩

end P16c.Universal

namespace P16c.Main

lemma commute_of_involutions {G : Type*} [Group G] {a b : G} (ha : a ^ 2 = 1)
    (hb : b ^ 2 = 1) (hab : (a * b) ^ 2 = 1) : a * b = b * a := by
  have hia : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha)
  have hib : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hb)
  have h : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hab)
  rw [mul_inv_rev, hia, hib] at h
  exact h.symm

/-- The final statement for any relator sets equal to `Universal.rels s u`,
`Toroid.rels s` and `Toroid.rels u`. -/
lemma p16c_of_rels (s u : ℕ) (hs : Odd s) (hu : Odd u) (hs3 : 3 ≤ s) (hu3 : 3 ≤ u)
    (hsu : s ≠ u) (R : Set (FreeGroup (Fin 4))) (A B : Set (FreeGroup (Fin 3)))
    (hR : R = Universal.rels s u) (hA : A = Toroid.rels s) (hB : B = Toroid.rels u) :
    let ρ : Fin 4 → PresentedGroup R := PresentedGroup.of
    (∀ i, ρ i ^ 2 = 1) ∧
    orderOf (ρ 0 * ρ 1) = 4 ∧ orderOf (ρ 1 * ρ 2) = 4 ∧ orderOf (ρ 2 * ρ 3) = 4 ∧
    (∀ i j : Fin 4, i.val + 2 ≤ j.val → ρ i * ρ j = ρ j * ρ i) ∧
    (∀ I J : Finset (Fin 4),
      Subgroup.closure (ρ '' ↑I) ⊓ Subgroup.closure (ρ '' ↑J) =
        Subgroup.closure (ρ '' ↑(I ∩ J))) ∧
    (∃ e : PresentedGroup A ≃* Subgroup.closure {ρ 0, ρ 1, ρ 2},
      ∀ i : Fin 3, (e (PresentedGroup.of i) : PresentedGroup R) = ρ i.castSucc) ∧
    Nat.card (Subgroup.closure {ρ 0, ρ 1, ρ 2}) = 8 * s ^ 2 ∧
    (∃ e : PresentedGroup B ≃* Subgroup.closure {ρ 1, ρ 2, ρ 3},
      ∀ i : Fin 3, (e (PresentedGroup.of i) : PresentedGroup R) = ρ i.succ) ∧
    Nat.card (Subgroup.closure {ρ 1, ρ 2, ρ 3}) = 8 * u ^ 2 := by
  subst hR hA hB
  obtain ⟨⟨hinv, hcomm, hint⟩, cs, cu, es, eu⟩ := p16c_universal_stringC s u hs hu hs3 hu3 hsu
  obtain ⟨o01, o12, o23⟩ := Universal.adjacent_orders s u hs hu hs3 hu3 hsu
  exact ⟨hinv, o01, o12, o23,
    fun i j hij => commute_of_involutions (hinv i) (hinv j) (hcomm i j hij),
    hint, es, cs, eu, cu⟩

end P16c.Main
