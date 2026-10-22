import Mathlib
import P16c.TorusFaces

/-! # Vertex sets in `(ℤ/s)²` are the orbits of the plane's faces

For `s ≥ 3` and faces `F, G` of the square tessellation of the plane, the images
in `(ℤ/s)²` satisfy `q(F) ⊆ q(G)` iff some translate `F + t`, `t ∈ sℤ²`, lies in
`G`, and `q(F) = q(G)` iff `F + t = G` for such a `t`. So recording the faces of
`{4,4}_(s,0)` (orbits of faces under the translations by `sℤ²`, incidence of
representatives) by their vertex sets, ordered by inclusion, is faithful. -/

namespace P16c.Torus

variable {s : ℕ}

/-- `t ∈ sℤ²`. -/
def InLattice (s : ℕ) (t : ℤ × ℤ) : Prop := (s : ℤ) ∣ t.1 ∧ (s : ℤ) ∣ t.2

/-- The unit box `{0,1}²`. -/
def box : Set (ℤ × ℤ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}

lemma proj_eq_iff {a b : ℤ × ℤ} :
    torusProj s a = torusProj s b ↔ InLattice s (b - a) := by
  simp only [torusProj, Prod.mk.injEq, InLattice, Prod.fst_sub, Prod.snd_sub,
    ZMod.intCast_eq_intCast_iff_dvd_sub]

lemma proj_sub (a b : ℤ × ℤ) : torusProj s (a - b) = torusProj s a - torusProj s b := by
  ext <;> simp [torusProj]

/-- `q` is injective on `{0,1,2}²` when `s ≥ 3`. -/
lemma eq_of_proj_eq (hs3 : 3 ≤ s) {a b : ℤ × ℤ} (ha : 0 ≤ a.1 ∧ a.1 ≤ 2 ∧ 0 ≤ a.2 ∧ a.2 ≤ 2)
    (hb : 0 ≤ b.1 ∧ b.1 ≤ 2 ∧ 0 ≤ b.2 ∧ b.2 ≤ 2) (h : torusProj s a = torusProj s b) :
    a = b := by
  obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ := proj_eq_iff.mp h
  simp only [Prod.fst_sub, Prod.snd_sub] at hk hl
  have hs : (3 : ℤ) ≤ s := by exact_mod_cast hs3
  have k0 : k = 0 := by
    rcases lt_trichotomy k 0 with h | h | h
    · nlinarith
    · exact h
    · nlinarith
  have l0 : l = 0 := by
    rcases lt_trichotomy l 0 with h | h | h
    · nlinarith
    · exact h
    · nlinarith
  subst k0 l0
  ext <;> linarith

lemma InLattice.neg {t : ℤ × ℤ} (h : InLattice s t) : InLattice s (-t) :=
  ⟨by simpa using h.1, by simpa using h.2⟩

/-- A nonempty proper face is a translate `v + S` of a shape `S ⊆ {0,1}²` containing `0`. -/
lemma face_shape {F : Set (ℤ × ℤ)} (hF : F ∈ planeFaces) :
    F = ∅ ∨ F = Set.univ ∨ ∃ v : ℤ × ℤ, ∃ S : Set (ℤ × ℤ), S ⊆ box ∧ (0 : ℤ × ℤ) ∈ S ∧
      F = (v + ·) '' S := by
  rcases mem_planeFaces.mp hF with rfl | rfl | ⟨v, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · refine Or.inr (Or.inr ⟨v, {0}, ?_, rfl, by simp⟩)
    rintro p rfl; simp [box]
  · refine Or.inr (Or.inr ⟨v, {0, (1, 0)}, ?_, by simp, by simp [Set.image_insert_eq]⟩)
    rintro p (rfl | rfl) <;> simp [box]
  · refine Or.inr (Or.inr ⟨v, {0, (0, 1)}, ?_, by simp, by simp [Set.image_insert_eq]⟩)
    rintro p (rfl | rfl) <;> simp [box]
  · refine Or.inr (Or.inr ⟨v, {0, (1, 0), (0, 1), (1, 1)}, ?_, by simp,
      by simp [Set.image_insert_eq]⟩)
    rintro p (rfl | rfl | rfl | rfl) <;> simp [box]

lemma proj_translate (t : ℤ × ℤ) (ht : InLattice s t) (F : Set (ℤ × ℤ)) :
    torusProj s '' ((· + t) '' F) = torusProj s '' F := by
  rw [Set.image_image]
  apply Set.image_congr
  intro a _
  exact proj_eq_iff.mpr (by simpa using ht.neg)

/-- Incidence of orbits is inclusion of vertex sets. -/
theorem proj_subset_iff (hs3 : 3 ≤ s) {F G : Set (ℤ × ℤ)} (hF : F ∈ planeFaces)
    (hG : G ∈ planeFaces) :
    torusProj s '' F ⊆ torusProj s '' G ↔ ∃ t, InLattice s t ∧ (· + t) '' F ⊆ G := by
  constructor
  swap
  · rintro ⟨t, ht, hsub⟩
    rw [← proj_translate t ht F]
    exact Set.image_mono hsub
  intro hsub
  have zero : InLattice s 0 := ⟨dvd_zero _, dvd_zero _⟩
  have inBox : ∀ {p : ℤ × ℤ}, p ∈ box → 0 ≤ p.1 ∧ p.1 ≤ 2 ∧ 0 ≤ p.2 ∧ p.2 ≤ 2 := by
    intro p hp; simp only [box, Set.mem_setOf_eq] at hp; omega
  have two : ((2, 2) : ℤ × ℤ) ∉ box := by simp [box]
  rcases face_shape hG with rfl | rfl | ⟨w, T, hT, -, rfl⟩
  · rcases face_shape hF with rfl | rfl | ⟨v, S, -, h0, rfl⟩
    · exact ⟨0, zero, by simp⟩
    · exact absurd (hsub (Set.mem_image_of_mem _ (Set.mem_univ 0))) (by simp)
    · exact absurd (hsub (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ h0))) (by simp)
  · exact ⟨0, zero, Set.subset_univ _⟩
  rcases face_shape hF with rfl | rfl | ⟨v, S, hS, h0, rfl⟩
  · exact ⟨0, zero, by simp⟩
  · -- the whole plane does not fit in a proper face
    exfalso
    obtain ⟨b, ⟨τ, hτ, rfl⟩, hb⟩ := hsub (Set.mem_image_of_mem _ (Set.mem_univ (w + (2, 2))))
    rw [torusProj_add, torusProj_add] at hb
    have := eq_of_proj_eq hs3 (inBox (hT hτ)) (by norm_num) (add_left_cancel hb)
    exact two (this ▸ hT hτ)
  -- `q v ∈ q(w + T)`: `q v = q(w + δ)`, and `t = w + δ - v`
  obtain ⟨b, ⟨δ, hδ, rfl⟩, hb⟩ := hsub (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ h0))
  refine ⟨w + δ - v, proj_eq_iff.mp (by simpa using hb.symm), ?_⟩
  rintro _ ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩
  obtain ⟨c, ⟨τ, hτ, rfl⟩, hc⟩ := hsub (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hσ))
  refine ⟨τ, hτ, ?_⟩
  have hσ' := hS hσ
  have hδ' := hT hδ
  simp only [box, Set.mem_setOf_eq] at hσ' hδ'
  have key : δ + σ = τ := by
    apply eq_of_proj_eq hs3 (by simp only [Prod.fst_add, Prod.snd_add]; omega) (inBox (hT hτ))
    simp only [torusProj_add, add_zero] at hb hc ⊢
    linear_combination hb - hc
  simp only
  rw [← key]
  abel

/-- Two faces have the same vertex set in `(ℤ/s)²` iff they are translates by `sℤ²`. -/
theorem proj_eq_iff_translate (hs3 : 3 ≤ s) {F G : Set (ℤ × ℤ)} (hF : F ∈ planeFaces)
    (hG : G ∈ planeFaces) :
    torusProj s '' F = torusProj s '' G ↔ ∃ t, InLattice s t ∧ (· + t) '' F = G := by
  constructor
  swap
  · rintro ⟨t, ht, rfl⟩
    exact (proj_translate t ht F).symm
  intro h
  obtain ⟨t, ht, h1⟩ := (proj_subset_iff hs3 hF hG).mp h.le
  obtain ⟨t', -, h2⟩ := (proj_subset_iff hs3 hG hF).mp h.ge
  refine ⟨t, ht, le_antisymm h1 ?_⟩
  -- `F + (t + t') ⊆ F` forces `t + t' = 0`, unless `F` is empty or the whole plane
  intro g hg
  have hgF : g + t' ∈ F := h2 (Set.mem_image_of_mem _ hg)
  rcases face_shape hF with rfl | rfl | ⟨v, S, hS, h0, rfl⟩
  · exact absurd hgF (Set.notMem_empty _)
  · exact ⟨g - t, Set.mem_univ _, by abel⟩
  have step : ∀ σ ∈ S, ∃ σ' ∈ S, v + σ' = v + σ + (t + t') := by
    intro σ hσ
    obtain ⟨σ', hσ', e⟩ := h2 (Set.mem_image_of_mem _ (h1 (Set.mem_image_of_mem _
      (Set.mem_image_of_mem (v + ·) hσ))))
    exact ⟨σ', hσ', by simp only at e; rw [e]; abel⟩
  have hu : t + t' = 0 := by
    obtain ⟨σ1, hσ1, e1⟩ := step 0 h0
    obtain ⟨σ2, hσ2, e2⟩ := step σ1 hσ1
    have e1' : σ1 = t + t' := by simpa using e1
    have e2' : σ2 = σ1 + (t + t') := by
      have := congrArg (-v + ·) e2; simp only [neg_add_cancel_left] at this; rw [this]; abel
    have b1 := hS hσ1
    have b2 := hS hσ2
    rw [e1'] at b1
    rw [e2', e1'] at b2
    simp only [box, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add] at b1 b2
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] <;> omega
  refine ⟨g + t', hgF, ?_⟩
  simp only
  rw [add_assoc, add_comm t' t, hu, add_zero]

end P16c.Torus
