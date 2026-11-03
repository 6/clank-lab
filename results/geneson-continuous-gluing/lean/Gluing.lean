import Representation


noncomputable section
open Set
namespace Geneson

/-- Glue expanding maps on domains lying on opposite sides of an anchor. -/
theorem glue_coordinate {D E T : Set ℝ} (a : ℝ)
    (haD : a ∈ D) (haE : a ∈ E)
    (hD : ∀ x ∈ D, x ≤ a) (hE : ∀ x ∈ E, a ≤ x)
    (hT : T = D ∪ E) (f : D → ℝ) (g : E → ℝ)
    (hf : Expands f) (hg : Expands g)
    (ha : f ⟨a, haD⟩ = g ⟨a, haE⟩) :
    ∃ h : T → ℝ, Expands h ∧
      (∀ x : D, h ⟨x, by rw [hT]; exact Or.inl x.property⟩ = f x) ∧
      (∀ x : E, h ⟨x, by rw [hT]; exact Or.inr x.property⟩ = g x) := by
  classical
  have hover : ∀ x ∈ D, x ∈ E → x = a := by
    intro x hxD hxE
    exact le_antisymm (hD x hxD) (hE x hxE)
  let h : T → ℝ := fun x => if hx : x.1 ∈ D then f ⟨x.1, hx⟩
    else g ⟨x.1, by
      have hxT : x.1 ∈ D ∪ E := by simpa only [hT] using x.property
      exact hxT.resolve_left hx⟩
  have hleft : ∀ x : D, h ⟨x, by rw [hT]; exact Or.inl x.property⟩ = f x := by
    intro x
    simp [h, x.property]
  have hright : ∀ x : E, h ⟨x, by rw [hT]; exact Or.inr x.property⟩ = g x := by
    intro x
    dsimp [h]
    split_ifs with hx
    · have hxa : x.1 = a := hover x.1 hx x.property
      have he : (⟨x.1,hx⟩ : D) = ⟨a,haD⟩ := Subtype.ext hxa
      have he' : x = (⟨a,haE⟩ : E) := Subtype.ext hxa
      rw [he, he']
      exact ha
    · rfl
  refine ⟨h, ?_, hleft, hright⟩
  intro x y hxy
  have hx : x.1 ∈ D ∨ x.1 ∈ E := by simpa [hT] using x.property
  have hy : y.1 ∈ D ∨ y.1 ∈ E := by simpa [hT] using y.property
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · have hfx := hleft ⟨x.1, hx⟩
    have hfy := hleft ⟨y.1, hy⟩
    change y.1 - x.1 ≤ h y - h x
    rw [hfx, hfy]
    exact hf ⟨x.1,hx⟩ ⟨y.1,hy⟩ hxy
  · have hfx := hleft ⟨x.1, hx⟩
    have hgy := hright ⟨y.1, hy⟩
    have hfa := hf ⟨x.1,hx⟩ ⟨a,haD⟩ (hD _ hx)
    have hga := hg ⟨a,haE⟩ ⟨y.1,hy⟩ (hE _ hy)
    change y.1 - x.1 ≤ h y - h x
    rw [hfx, hgy]
    linarith
  · have hxa : x.1 = a := by linarith [hE _ hx, hD _ hy]
    have hya : y.1 = a := by linarith [hE _ hx, hD _ hy]
    have heq : x = y := Subtype.ext (hxa.trans hya.symm)
    subst y
    simp
  · have hgx := hright ⟨x.1, hx⟩
    have hgy := hright ⟨y.1, hy⟩
    change y.1 - x.1 ≤ h y - h x
    rw [hgx, hgy]
    exact hg ⟨x.1,hx⟩ ⟨y.1,hy⟩ hxy

/-- Anchor-compatible copies glue across arbitrary projection domains. -/
theorem hasCopy_union_of_anchor {P Q K : Set Plane} {c d : ℝ}
    (hp : (c,d) ∈ P) (hq : (c,d) ∈ Q)
    (hP : ∀ p ∈ P, p.1 ≤ c ∧ p.2 ≤ d)
    (hQ : ∀ q ∈ Q, c ≤ q.1 ∧ d ≤ q.2)
    (u : Maps P) (v : Maps Q)
    (hu : IsWitness P K u) (hv : IsWitness Q K v)
    (he : ImagePoint u ⟨(c,d),hp⟩ = ImagePoint v ⟨(c,d),hq⟩) :
    HasCopy (P ∪ Q) K := by
  have hxP : c ∈ X P := ⟨(c,d),hp,rfl⟩
  have hxQ : c ∈ X Q := ⟨(c,d),hq,rfl⟩
  have hyP : d ∈ Y P := ⟨(c,d),hp,rfl⟩
  have hyQ : d ∈ Y Q := ⟨(c,d),hq,rfl⟩
  have hXP : ∀ x ∈ X P, x ≤ c := by
    rintro x ⟨p,hp',rfl⟩
    exact (hP p hp').1
  have hXQ : ∀ x ∈ X Q, c ≤ x := by
    rintro x ⟨q,hq',rfl⟩
    exact (hQ q hq').1
  have hYP : ∀ y ∈ Y P, y ≤ d := by
    rintro y ⟨p,hp',rfl⟩
    exact (hP p hp').2
  have hYQ : ∀ y ∈ Y Q, d ≤ y := by
    rintro y ⟨q,hq',rfl⟩
    exact (hQ q hq').2
  have hX : X (P ∪ Q) = X P ∪ X Q := image_union _ _ _
  have hY : Y (P ∪ Q) = Y P ∪ Y Q := image_union _ _ _
  have heX : u.1 ⟨c,hxP⟩ = v.1 ⟨c,hxQ⟩ := congrArg Prod.fst he
  have heY : u.2 ⟨d,hyP⟩ = v.2 ⟨d,hyQ⟩ := congrArg Prod.snd he
  obtain ⟨f,hf,hfP,hfQ⟩ := glue_coordinate c hxP hxQ hXP hXQ hX u.1 v.1 hu.1 hv.1 heX
  obtain ⟨g,hg,hgP,hgQ⟩ := glue_coordinate d hyP hyQ hYP hYQ hY u.2 v.2 hu.2.1 hv.2.1 heY
  refine ⟨(f,g),hf,hg,?_⟩
  intro p
  rcases p.property with h | h
  · change (f _,g _) ∈ K
    rw [hfP ⟨p.1.1,⟨p.1,h,rfl⟩⟩, hgP ⟨p.1.2,⟨p.1,h,rfl⟩⟩]
    exact hu.2.2 ⟨p.1,h⟩
  · change (f _,g _) ∈ K
    rw [hfQ ⟨p.1.1,⟨p.1,h,rfl⟩⟩, hgQ ⟨p.1.2,⟨p.1,h,rfl⟩⟩]
    exact hv.2.2 ⟨p.1,h⟩

/-- All possible images of the distinguished point under copies in K. -/
def AnchorSet (P K : Set Plane) (p : P) : Set Plane :=
  {z | ∃ w : Maps P, IsWitness P K w ∧ ImagePoint w p = z}

lemma anchorSet_subset {P K : Set Plane} (p : P) : AnchorSet P K p ⊆ K := by
  rintro z ⟨w,hw,rfl⟩
  exact hw.2.2 p

/-- The right pattern cannot occur among anchor images in a union-avoiding set. -/
theorem anchorSet_avoids_right {P Q K : Set Plane} {c d : ℝ}
    (hp : (c,d) ∈ P) (hq : (c,d) ∈ Q)
    (hP : ∀ p ∈ P, p.1 ≤ c ∧ p.2 ≤ d)
    (hQ : ∀ q ∈ Q, c ≤ q.1 ∧ d ≤ q.2)
    (hK : ¬ Contains (P ∪ Q) K) :
    ¬ Contains Q (AnchorSet P K ⟨(c,d),hp⟩) := by
  intro h
  obtain ⟨v,hv⟩ := contains_iff_hasCopy.1 h
  obtain ⟨u,hu,he⟩ := hv.2.2 ⟨(c,d),hq⟩
  have hvK : IsWitness Q K v :=
    ⟨hv.1,hv.2.1,fun q => anchorSet_subset _ (hv.2.2 q)⟩
  exact hK (contains_iff_hasCopy.2 (hasCopy_union_of_anchor hp hq hP hQ u v hu hvK he))

/-- Removing every possible anchor image removes all copies of the left pattern. -/
theorem sdiff_anchorSet_avoids_left {P K : Set Plane} (p : P) :
    ¬ Contains P (K \ AnchorSet P K p) := by
  intro h
  obtain ⟨u,hu⟩ := contains_iff_hasCopy.1 h
  have huK : IsWitness P K u := ⟨hu.1,hu.2.1,fun q => (hu.2.2 q).1⟩
  exact (hu.2.2 p).2 ⟨u,huK,rfl⟩

end Geneson
