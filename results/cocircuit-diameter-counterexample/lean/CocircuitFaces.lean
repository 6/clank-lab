import UniformCocircuit

namespace ADKZPricing
open Finset
noncomputable section

def signSupport (X : SignVector) : Finset (Fin 80) := univ.filter (fun i => X i ≠ 0)
def signZeros (X : SignVector) : Finset (Fin 80) := univ.filter (fun i => X i = 0)

theorem face_refl (X : SignVector) : FaceLE X X := fun _ => Or.inr rfl

theorem face_trans {X Y Z : SignVector} (hxy : FaceLE X Y) (hyz : FaceLE Y Z) :
    FaceLE X Z := by
  intro i
  rcases hxy i with h | h
  · exact Or.inl h
  · rcases hyz i with hz | hz
    · exact Or.inl (h.trans hz)
    · exact Or.inr (h.trans hz)

theorem face_support_subset {X Y : SignVector} (h : FaceLE X Y) :
    signSupport X ⊆ signSupport Y := by
  intro i hi
  have hxi := (mem_filter.mp hi).2
  have he := (h i).resolve_left hxi
  exact mem_filter.mpr ⟨mem_univ _, fun hy => hxi (he.trans hy)⟩

theorem face_eq_of_support_card {X Y : SignVector} (h : FaceLE X Y)
    (hc : (signSupport Y).card ≤ (signSupport X).card) : X = Y := by
  have he := eq_of_subset_of_card_le (face_support_subset h) hc
  ext i
  by_cases hx : X i = 0
  · have hy : Y i = 0 := by
      by_contra hn
      have hm : i ∈ signSupport Y := mem_filter.mpr ⟨mem_univ _, hn⟩
      rw [← he] at hm
      exact (mem_filter.mp hm).2 hx
    rw [hx, hy]
  · exact (h i).resolve_left hx

theorem face_zero_subset {X Y : SignVector} (h : FaceLE X Y) :
    signZeros Y ⊆ signZeros X := by
  intro i hi
  have hy := (mem_filter.mp hi).2
  exact mem_filter.mpr ⟨mem_univ _, (h i).elim id (fun he => he.trans hy)⟩

theorem face_eq_of_zero_card {X Y : SignVector} (h : FaceLE X Y)
    (hc : (signZeros X).card ≤ (signZeros Y).card) : X = Y := by
  have he := eq_of_subset_of_card_le (face_zero_subset h) hc
  ext i
  rcases h i with hx | hx
  · have hm : i ∈ signZeros X := mem_filter.mpr ⟨mem_univ _, hx⟩
    rw [← he] at hm
    exact hx.trans (mem_filter.mp hm).2.symm
  · exact hx

/-- Every actual nonzero covector contains an actual cocircuit face.
    This is a finite minimal-support proof, not graph enumeration. -/
theorem covector_has_cocircuit_face (A : Matrix (Fin 80) (Fin 41) ℚ)
    (X : SignVector) (hc : Covector A X) (hne : X ≠ 0) :
    ∃ Y, Cocircuit A Y ∧ FaceLE Y X := by
  classical
  have hex : ∃ k : ℕ, ∃ Y, Covector A Y ∧ Y ≠ 0 ∧ FaceLE Y X ∧
      (signSupport Y).card = k := ⟨(signSupport X).card, X, hc, hne, face_refl X, rfl⟩
  obtain ⟨Y, hy, hyn, hyx, hcard⟩ := Nat.find_spec hex
  refine ⟨Y, ⟨hy, hyn, ?_⟩, hyx⟩
  intro Z hz hzn hzy
  apply face_eq_of_support_card hzy
  have hm := Nat.find_min' hex ⟨Z, hz, hzn, face_trans hzy hyx, rfl⟩
  simpa only [← hcard] using hm

/-- Converse to the previously proved forty-zero necessity, using only
    actual covectors and their support-minimal faces. -/
theorem uniform_covector_cocircuit_iff (A : Matrix (Fin 80) (Fin 41) ℚ)
    (hu : Uniform A) (X : SignVector) (hx : Covector A X) (hn : X ≠ 0) :
    Cocircuit A X ↔ (signZeros X).card = 40 := by
  constructor
  · exact uniform_cocircuit_zero_count A hu X
  · intro hc
    obtain ⟨Y, hy, hyx⟩ := covector_has_cocircuit_face A X hx hn
    have hY : (signZeros Y).card = 40 := uniform_cocircuit_zero_count A hu Y hy
    have he := face_eq_of_zero_card hyx (by omega)
    simpa only [he] using hy

#print axioms covector_has_cocircuit_face
#print axioms uniform_covector_cocircuit_iff
end
end ADKZPricing
