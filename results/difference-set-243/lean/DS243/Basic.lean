import Mathlib

/-!
# Basic objects for the (243,121,60) difference-set question in C3 × C9 × C9

* `G` is the group `ZMod 3 × ZMod 9 × ZMod 9`.
* `diffCount D g` counts ordered pairs `(a, b) ∈ D × D` with `a - b = g`.
* `IsDiffSet D` says `D` is a (243,121,60) difference set: 121 elements, and every
  nonzero element is a difference exactly 60 times.
* `H` is the subgroup `G[3] = {x | 3 • x = 0}` and `Fixed D` says `61 • D ⊆ D`.
* `Legal` maps are `x ↦ A x + τ` with `A` an additive bijection and `τ ∈ H`.
  They preserve difference sets, multiplier-fixedness and `H`.
-/

namespace DS243

open Finset

/-- The group `C3 × C9 × C9`. -/
abbrev G := ZMod 3 × ZMod 9 × ZMod 9

/-- Number of ordered pairs `(a, b) ∈ D × D` with `a - b = g`. -/
def diffCount (D : Finset G) (g : G) : ℕ :=
  ((D ×ˢ D).filter fun p => p.1 - p.2 = g).card

/-- `D` is a (243,121,60) difference set in `G`. -/
def IsDiffSet (D : Finset G) : Prop :=
  D.card = 121 ∧ ∀ g : G, g ≠ 0 → diffCount D g = 60

/-- The subgroup `H = G[3]` of elements killed by `3`. -/
def H : Finset G := univ.filter fun x => 3 • x = 0

lemma mem_H {x : G} : x ∈ H ↔ 3 • x = 0 := by simp [H]

/-- Reduction `ZMod 9 → ZMod 3`. -/
def red (y : ZMod 9) : ZMod 3 := ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3) y

/-- The image of `x` in `Q = G / 3G ≅ (ZMod 3)³`. -/
def cell (x : G) : ZMod 3 × ZMod 3 × ZMod 3 := (x.1, red x.2.1, red x.2.2)

/-- The linear form `(x, y, z) ↦ a x + b y + c z` on `G`, with values in `ZMod 3`. -/
def form (a b c : ZMod 3) (x : G) : ZMod 3 := a * x.1 + b * red x.2.1 + c * red x.2.2

/-- `D` is fixed by the numerical multiplier `61`. -/
def Fixed (D : Finset G) : Prop := ∀ x ∈ D, (61 : ℕ) • x ∈ D

lemma diffCount_eq_card_filter (D : Finset G) (g : G) :
    diffCount D g = (D.filter fun a => a - g ∈ D).card := by
  unfold diffCount
  refine card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    simp only [mem_filter, mem_product] at hp ⊢
    refine ⟨hp.1.1, ?_⟩
    have : p.1 - g = p.2 := by rw [← hp.2]; abel
    rw [this]; exact hp.1.2
  · intro p hp q hq h
    simp only [mem_filter, mem_product] at hp hq
    have h1 : p.2 = p.1 - g := by rw [← hp.2]; abel
    have h2 : q.2 = q.1 - g := by rw [← hq.2]; abel
    exact Prod.ext h (by rw [h1, h2, h])
  · intro a ha
    simp only [mem_filter] at ha
    exact ⟨(a, a - g), by simp [mem_product, ha.1, ha.2], rfl⟩

/-- Legal normalization maps: `x ↦ lin x + τ` with `lin` bijective additive and `τ ∈ H`. -/
structure Legal where
  lin : G →+ G
  τ : G
  bij : Function.Bijective lin
  hτ : 3 • τ = 0

namespace Legal

/-- The underlying function of a legal map. -/
def toFun (L : Legal) (x : G) : G := L.lin x + L.τ

lemma injective (L : Legal) : Function.Injective L.toFun := by
  intro x y h
  exact L.bij.1 (add_right_cancel h)

/-- The identity legal map. -/
def id : Legal := ⟨AddMonoidHom.id G, 0, Function.bijective_id, by simp⟩

/-- Composition `L ∘ M` of legal maps. -/
def comp (L M : Legal) : Legal where
  lin := L.lin.comp M.lin
  τ := L.lin M.τ + L.τ
  bij := L.bij.comp M.bij
  hτ := by rw [smul_add, ← map_nsmul, M.hτ, map_zero, L.hτ, add_zero]

lemma comp_toFun (L M : Legal) (x : G) : (L.comp M).toFun x = L.toFun (M.toFun x) := by
  simp only [comp, toFun, AddMonoidHom.comp_apply, map_add]; abel

lemma id_toFun (x : G) : Legal.id.toFun x = x := by simp [Legal.id, toFun]

lemma toFun_sub (L : Legal) (a b : G) : L.toFun a - L.toFun b = L.lin (a - b) := by
  simp [toFun, map_sub]

lemma image_card (L : Legal) (D : Finset G) : (D.image L.toFun).card = D.card :=
  card_image_of_injective _ L.injective

lemma diffCount_image (L : Legal) (D : Finset G) (g : G) :
    diffCount (D.image L.toFun) (L.lin g) = diffCount D g := by
  rw [diffCount_eq_card_filter, diffCount_eq_card_filter]
  symm
  refine card_bij (fun a _ => L.toFun a) ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter] at ha ⊢
    refine ⟨mem_image_of_mem _ ha.1, ?_⟩
    have : L.toFun a - L.lin g = L.toFun (a - g) := by simp [toFun, map_sub]; abel
    rw [this]; exact mem_image_of_mem _ ha.2
  · intro a _ b _ h; exact L.injective h
  · intro y hy
    simp only [mem_filter, mem_image] at hy
    obtain ⟨⟨a, ha, rfl⟩, ⟨c, hc, hc'⟩⟩ := hy
    refine ⟨a, ?_, rfl⟩
    simp only [mem_filter]
    refine ⟨ha, ?_⟩
    have : L.toFun c = L.toFun (a - g) := by rw [hc']; simp [toFun, map_sub]; abel
    rw [← L.injective this]; exact hc

/-- Legal maps send difference sets to difference sets. -/
theorem isDiffSet_image (L : Legal) {D : Finset G} (hD : IsDiffSet D) :
    IsDiffSet (D.image L.toFun) := by
  refine ⟨by rw [L.image_card, hD.1], fun g hg => ?_⟩
  obtain ⟨g', rfl⟩ := L.bij.2 g
  have hg' : g' ≠ 0 := by rintro rfl; exact hg (map_zero _)
  rw [diffCount_image, hD.2 g' hg']

lemma smul61_toFun (L : Legal) (x : G) : (61 : ℕ) • L.toFun x = L.toFun ((61 : ℕ) • x) := by
  have h60 : (61 : ℕ) • L.τ = L.τ := by
    rw [show (61 : ℕ) = 20 * 3 + 1 by norm_num, add_nsmul, ← smul_smul, L.hτ,
      smul_zero, zero_add, one_nsmul]
  simp only [toFun, smul_add, map_nsmul, h60]

/-- Legal maps send multiplier-fixed sets to multiplier-fixed sets. -/
theorem fixed_image (L : Legal) {D : Finset G} (hD : Fixed D) : Fixed (D.image L.toFun) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
  rw [smul61_toFun]
  exact mem_image_of_mem _ (hD x hx)

lemma mem_H_toFun (L : Legal) {x : G} (hx : x ∈ H) : L.toFun x ∈ H := by
  rw [mem_H] at hx ⊢
  rw [toFun, smul_add, ← map_nsmul, hx, map_zero, L.hτ, add_zero]

/-- A legal map preserves membership in `H` in both directions. -/
lemma mem_H_iff (L : Legal) (x : G) : L.toFun x ∈ H ↔ x ∈ H := by
  constructor
  · intro h
    -- `L` maps `H` injectively into `H`, hence onto `H`.
    have hsub : H.image L.toFun ⊆ H := fun y hy => by
      obtain ⟨z, hz, rfl⟩ := mem_image.1 hy; exact mem_H_toFun L hz
    have heq : H.image L.toFun = H :=
      eq_of_subset_of_card_le hsub (by rw [L.image_card])
    rw [← heq] at h
    obtain ⟨z, hz, hzx⟩ := mem_image.1 h
    rwa [← L.injective hzx]
  · exact mem_H_toFun L

lemma image_inter_H (L : Legal) (D : Finset G) :
    (D.image L.toFun).filter (· ∈ H) = (D.filter (· ∈ H)).image L.toFun := by
  ext y
  simp only [mem_filter, mem_image]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    exact ⟨x, ⟨hx, (L.mem_H_iff x).1 hy⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hxH⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, (L.mem_H_iff x).2 hxH⟩

lemma image_comp (L M : Legal) (D : Finset G) :
    (D.image M.toFun).image L.toFun = D.image (L.comp M).toFun := by
  rw [image_image]; congr 1; funext x; simp [comp_toFun]

end Legal

end DS243
