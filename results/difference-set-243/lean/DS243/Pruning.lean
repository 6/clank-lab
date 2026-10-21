import DS243.Basic

/-!
# Soundness of the search's pruning and leaf test

The lifting kernels add whole 61-orbits to the frozen singleton set and reject a partial set as
soon as some nonzero difference occurs more than 60 times; at a leaf they require 121 points and
every nonzero difference count equal to 60. These lemmas show that rule loses no difference set:
difference counts only grow with the set (`diffCount_mono`), so a rejected partial set has no
difference-set completion (`prune_sound`), and a 121-point set with all counts at most 60 is a
difference set (`isDiffSet_of_le`). For a multiplier-fixed set the counts are constant on the
classes `{±g, ±61g, ±61²g}` used by the compressed kernel (`diffCount_neg`, `diffCount_smul61`).
-/

namespace DS243

open Finset

lemma diffCount_mono {A B : Finset G} (h : A ⊆ B) (g : G) : diffCount A g ≤ diffCount B g := by
  exact card_le_card (filter_subset_filter _ (product_subset_product h h))

/-- Pruning is sound: a partial set with a difference occurring more than 60 times has no
difference-set completion. -/
theorem prune_sound {A B : Finset G} (h : A ⊆ B) {g : G} (hg : g ≠ 0) (hA : 60 < diffCount A g) :
    ¬ IsDiffSet B := by
  intro hB
  have h1 := diffCount_mono h g
  rw [hB.2 g hg] at h1
  omega

/-- The leaf test is exact: 121 points with every nonzero difference at most 60 times form a
difference set (all counts are then 60, since they sum to `121 · 120 = 242 · 60`). -/
theorem isDiffSet_of_le {D : Finset G} (hcard : D.card = 121)
    (hle : ∀ g : G, g ≠ 0 → diffCount D g ≤ 60) : IsDiffSet D := by
  refine ⟨hcard, ?_⟩
  have hsum : ∑ g : G, diffCount D g = 121 * 121 := by
    rw [← hcard, ← card_product]
    unfold diffCount
    exact (card_eq_sum_card_fiberwise (f := fun p : G × G => p.1 - p.2) (t := univ)
      (fun _ _ => mem_univ _)).symm
  have h0 : diffCount D 0 = 121 := by
    rw [diffCount_eq_card_filter, ← hcard]
    exact congrArg card (filter_true_of_mem (fun a ha => by simpa using ha))
  rw [← add_sum_erase _ _ (mem_univ (0 : G)), h0] at hsum
  have hrest : ∑ g ∈ univ.erase (0 : G), diffCount D g = ∑ _g ∈ univ.erase (0 : G), 60 := by
    rw [sum_const, card_erase_of_mem (mem_univ _), card_univ]
    simp only [Fintype.card_prod, ZMod.card, smul_eq_mul]
    omega
  have hall := (sum_eq_sum_iff_of_le (fun g hg => hle g (ne_of_mem_erase hg))).1 hrest
  intro g hg
  exact hall g (mem_erase.2 ⟨hg, mem_univ _⟩)

lemma diffCount_neg (D : Finset G) (g : G) : diffCount D (-g) = diffCount D g := by
  unfold diffCount
  refine card_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_
  · intro p hp
    simp only [coe_filter, mem_product, Set.mem_setOf_eq, Prod.fst_swap, Prod.snd_swap] at hp ⊢
    refine ⟨⟨hp.1.2, hp.1.1⟩, ?_⟩
    rw [← neg_sub, hp.2, neg_neg]
  · intro p hp
    simp only [coe_filter, mem_product, Set.mem_setOf_eq, Prod.fst_swap, Prod.snd_swap] at hp ⊢
    refine ⟨⟨hp.1.2, hp.1.1⟩, ?_⟩
    rw [← neg_sub, hp.2]
  · intro p _; rfl
  · intro p _; rfl

lemma smul244 (x : G) : (244 : ℕ) • x = x := by
  obtain ⟨a, b, c⟩ := x
  simp only [Prod.smul_mk, nsmul_eq_mul, Prod.mk.injEq]
  have h3 : (244 : ZMod 3) = 1 := by decide
  have h9 : (244 : ZMod 9) = 1 := by decide
  simp only [Nat.cast_ofNat, h3, h9, one_mul, and_self]

/-- Multiplication by `61` as an additive endomorphism of `G`. -/
def mul61Hom : G →+ G where
  toFun x := (61 : ℕ) • x
  map_zero' := smul_zero _
  map_add' x y := smul_add _ x y

lemma mul61Hom_bijective : Function.Bijective mul61Hom := by
  refine Finite.injective_iff_bijective.1 ?_
  intro x y h
  have h' : (4 : ℕ) • mul61Hom x = (4 : ℕ) • mul61Hom y := by rw [h]
  simp only [mul61Hom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, smul_smul] at h'
  rwa [show (4 * 61 : ℕ) = 244 from rfl, smul244, smul244] at h'

lemma diffCount_smul61 {D : Finset G} (hF : Fixed D) (g : G) :
    diffCount D ((61 : ℕ) • g) = diffCount D g := by
  let L : Legal :=
    { lin := mul61Hom
      τ := 0
      bij := mul61Hom_bijective
      hτ := smul_zero _ }
  have hL : ∀ x, L.toFun x = (61 : ℕ) • x := fun x => by simp [L, Legal.toFun, mul61Hom]
  have himg : D.image L.toFun = D := by
    have hsub : D.image L.toFun ⊆ D := fun y hy => by
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
      rw [hL]; exact hF x hx
    exact eq_of_subset_of_card_le hsub (by rw [L.image_card])
  have := L.diffCount_image D g
  rw [himg] at this
  exact this

end DS243
