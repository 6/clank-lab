import Endpoint


noncomputable section
open Set
namespace Geneson

lemma ratio_iff_difference {a b : ℝ} (hb : 0 < b) :
    1 ≤ a / b ↔ b ≤ a := by
  rw [le_div_iff₀ hb]
  simp

lemma expands_iff_ratio {D : Set ℝ} (f : D → ℝ) :
    Expands f ↔ ∀ x y : D, (x : ℝ) < y →
      1 ≤ (f y - f x) / ((y : ℝ) - x) := by
  constructor
  · intro h x y hxy
    exact (ratio_iff_difference (sub_pos.mpr hxy)).2 (h x y hxy.le)
  · intro h x y hxy
    rcases lt_or_eq_of_le hxy with hlt | heq
    · exact (ratio_iff_difference (sub_pos.mpr hlt)).1 (h x y hlt)
    · have : x = y := Subtype.ext heq
      subst y
      simp

lemma contains_iff_hasCopy {R S : Set Plane} : Contains R S ↔ HasCopy R S := by
  constructor
  · rintro ⟨f,g,hf,hg,hp⟩
    exact ⟨⟨fun x => (f x : ℝ), fun y => (g y : ℝ)⟩,
      (expands_iff_ratio _).2 hf, (expands_iff_ratio _).2 hg, hp⟩
  · rintro ⟨⟨f,g⟩,hf,hg,hp⟩
    have hfx : ∀ x : X R, f x ∈ X S := by
      rintro ⟨x,p,hpR,rfl⟩
      exact ⟨ImagePoint (f,g) ⟨p,hpR⟩, hp ⟨p,hpR⟩, rfl⟩
    have hgy : ∀ y : Y R, g y ∈ Y S := by
      rintro ⟨y,p,hpR,rfl⟩
      exact ⟨ImagePoint (f,g) ⟨p,hpR⟩, hp ⟨p,hpR⟩, rfl⟩
    exact ⟨fun x => ⟨f x,hfx x⟩, fun y => ⟨g y,hgy y⟩,
      (expands_iff_ratio f).1 hf, (expands_iff_ratio g).1 hg, hp⟩

lemma hasCopy_mono {R S T : Set Plane} (hST : S ⊆ T)
    (h : HasCopy R S) : HasCopy R T := by
  obtain ⟨w,hf,hg,hp⟩ := h
  exact ⟨w,hf,hg,fun p => hST (hp p)⟩

lemma contains_mono {R S T : Set Plane} (hST : S ⊆ T)
    (h : Contains R S) : Contains R T :=
  contains_iff_hasCopy.2 (hasCopy_mono hST (contains_iff_hasCopy.1 h))

lemma not_contains_empty {R : Set Plane} (hR : R.Nonempty) : ¬ Contains R ∅ := by
  intro h
  obtain ⟨w,_,_,hp⟩ := contains_iff_hasCopy.1 h
  obtain ⟨p,hpR⟩ := hR
  exact hp ⟨p,hpR⟩

end Geneson
