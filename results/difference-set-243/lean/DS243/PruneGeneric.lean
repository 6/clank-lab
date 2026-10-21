import DS243.Multiplier

/-!
# Pruning and leaf test for difference sets in any finite abelian group

The rule the search applies, stated for every finite abelian group and every `λ`: a partial set
with some nonzero difference occurring more than `λ` times has no difference-set completion
(`pruneA_sound`), and a `k`-set with every nonzero difference at most `λ` times, where
`k² = k + λ (v - 1)`, has every nonzero difference exactly `λ` times (`leafA_exact`).
`planted/` holds the weakened rules (pruning at `λ`, leaf bound `λ + 1`) that Lean must reject;
`planted/Refute.lean` proves them false.
-/

namespace DS243

open Finset

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

lemma diffCountA_mono {D B : Finset A} (h : D ⊆ B) (g : A) : diffCountA D g ≤ diffCountA B g :=
  card_le_card (filter_subset_filter _ (product_subset_product h h))

/-- Pruning is sound in any group: a subset of a difference set has no difference more than
`λ` times. -/
theorem pruneA_sound (lam : ℕ) {D B : Finset A} (h : D ⊆ B) {g : A} (hg : g ≠ 0)
    (hB : ∀ g : A, g ≠ 0 → diffCountA B g = lam) (hD : lam < diffCountA D g) : False := by
  have h1 := diffCountA_mono h g
  rw [hB g hg] at h1
  omega

/-- The leaf test is exact in any group. -/
theorem leafA_exact (k lam : ℕ) (D : Finset A) (hk : D.card = k)
    (hpar : k * k = k + lam * (Fintype.card A - 1))
    (hle : ∀ g : A, g ≠ 0 → diffCountA D g ≤ lam) : ∀ g : A, g ≠ 0 → diffCountA D g = lam := by
  have hsum : ∑ g : A, diffCountA D g = k * k := by
    rw [← hk, ← card_product]
    unfold diffCountA
    exact (card_eq_sum_card_fiberwise (f := fun p : A × A => p.1 - p.2) (t := univ)
      (fun _ _ => mem_univ _)).symm
  have h0 : diffCountA D 0 = k := by
    rw [← hk]
    unfold diffCountA
    refine card_bij (fun p _ => p.1) ?_ ?_ ?_
    · intro p hp; simp only [mem_filter, mem_product] at hp; exact hp.1.1
    · intro p hp q hq he
      simp only [mem_filter, mem_product, sub_eq_zero] at hp hq
      exact Prod.ext he (by rw [← hp.2, ← hq.2, he])
    · intro a ha; exact ⟨(a, a), by simp [ha], rfl⟩
  rw [← add_sum_erase _ _ (mem_univ (0 : A)), h0] at hsum
  have hrest : ∑ g ∈ univ.erase (0 : A), diffCountA D g = ∑ _g ∈ univ.erase (0 : A), lam := by
    rw [sum_const, card_erase_of_mem (mem_univ _), card_univ, smul_eq_mul]
    rw [hpar] at hsum
    linarith [mul_comm lam (Fintype.card A - 1)]
  have hall := (sum_eq_sum_iff_of_le (fun g hg => hle g (ne_of_mem_erase hg))).1 hrest
  intro g hg
  exact hall g (mem_erase.2 ⟨hg, mem_univ _⟩)

end DS243
