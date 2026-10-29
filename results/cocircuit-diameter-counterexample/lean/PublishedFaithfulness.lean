import PathVariation

/- Bridge to ADKZ Definition 1.3 (p. 3) and its realizable cocircuit
   description (p. 6). The original endpoint and its definitions are unchanged. -/
namespace ADKZPricing
open Matrix Finset
noncomputable section

/-- Inclusion-minimal nonempty support among all covectors, without conformity. -/
def PublishedCocircuit (A : Matrix (Fin 80) (Fin 41) ℚ) (X : SignVector) : Prop :=
  Covector A X ∧ X ≠ 0 ∧ ∀ Y, Covector A Y → Y ≠ 0 →
    signSupport Y ⊆ signSupport X → signSupport Y = signSupport X

/-- Literal emptiness of the opposite-sign separation set. -/
def PublishedSeparationEmpty (X Y : SignVector) : Prop :=
  ∀ i, ¬ (X i = 1 ∧ Y i = -1) ∧ ¬ (X i = -1 ∧ Y i = 1)

/-- Published edge criterion, retaining its at-least r-2 common-zero bound. -/
def PublishedAdjacent (A : Matrix (Fin 80) (Fin 41) ℚ) (X Y : SignVector) : Prop :=
  PublishedCocircuit A X ∧ PublishedCocircuit A Y ∧ X ≠ Y ∧
    39 ≤ (signZeros X ∩ signZeros Y).card ∧ PublishedSeparationEmpty X Y

theorem published_cocircuit_iff (A : Matrix (Fin 80) (Fin 41) ℚ)
    (hu : Uniform A) (X : SignVector) : PublishedCocircuit A X ↔ Cocircuit A X := by
  classical
  constructor
  · rintro ⟨hc, hn, hminimal⟩
    refine ⟨hc, hn, ?_⟩
    intro Y hy hyn hf
    have he := hminimal Y hy hyn (face_support_subset hf)
    exact face_eq_of_support_card hf (by rw [he])
  · intro hx
    refine ⟨hx.1, hx.2.1, ?_⟩
    intro Y hy hyn hs
    have hxcard : (signZeros X).card = 40 := uniform_cocircuit_zero_count A hu X hx
    obtain ⟨v, hv⟩ := hy
    have hvn : v ≠ 0 := by
      intro he
      apply hyn
      ext i
      simpa [he, realSign] using hv i
    have hbound := rational_uniform_zero_count A hu v hvn
    have hzero : signZeros Y = univ.filter (fun i => (∑ j, (A i j : ℝ) * v j) = 0) := by
      ext i
      simp only [signZeros, mem_filter, mem_univ, true_and, hv i, realSign_zero_iff]
    have hsub : signZeros X ⊆ signZeros Y := by
      intro i hi
      have hxi : X i = 0 := (mem_filter.mp hi).2
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      by_contra hyi
      have hm := hs (mem_filter.mpr ⟨mem_univ _, hyi⟩)
      exact (mem_filter.mp hm).2 hxi
    have he : signZeros X = signZeros Y := eq_of_subset_of_card_le hsub (by rw [hzero]; omega)
    ext i
    have hz : X i = 0 ↔ Y i = 0 := by
      simpa only [signZeros, mem_filter, mem_univ, true_and] using (Finset.ext_iff.mp he i)
    simp only [signSupport, mem_filter, mem_univ, true_and]
    exact not_congr hz.symm

theorem published_separation_iff_compose (A : Matrix (Fin 80) (Fin 41) ℚ)
    (X Y : SignVector) (hx : Covector A X) (hy : Covector A Y) :
    PublishedSeparationEmpty X Y ↔ compose X Y = compose Y X := by
  constructor
  · intro h
    ext i
    have hs := h i
    rcases covector_sign_cases A X hx i with hxi | hxi | hxi <;>
      rcases covector_sign_cases A Y hy i with hyi | hyi | hyi <;>
      simp_all [compose]
  · intro h i
    have he := congrArg (fun Z : SignVector => Z i) h
    constructor <;> rintro ⟨hxi, hyi⟩ <;> simp [compose, hxi, hyi] at he

theorem published_composition_zeros (X Y : SignVector) :
    signZeros (compose X Y) = signZeros X ∩ signZeros Y := by
  ext i
  simp only [signZeros, mem_filter, mem_univ, true_and, mem_inter, compose_zero_iff]

/-- The published inequality cannot have forty common zeros: compatible
    composition is a nonzero covector, then a cocircuit, forcing X = Y. -/
theorem published_common_zeros_eq_39 (A : Matrix (Fin 80) (Fin 41) ℚ)
    (hu : Uniform A) (X Y : SignVector) (hx : Cocircuit A X) (hy : Cocircuit A Y)
    (hne : X ≠ Y) (hsep : PublishedSeparationEmpty X Y)
    (hlo : 39 ≤ (signZeros X ∩ signZeros Y).card) :
    (signZeros X ∩ signZeros Y).card = 39 := by
  have hcomm := (published_separation_iff_compose A X Y hx.1 hy.1).mp hsep
  have hXT := face_left_compose X Y
  have hYT := face_right_compose hcomm
  have hcov := covector_commuting_compose A X Y hx.1 hy.1 hcomm
  have hn := face_nonzero_upper hXT hx.2.1
  have hxc : (signZeros X).card = 40 := uniform_cocircuit_zero_count A hu X hx
  have hupper : (signZeros (compose X Y)).card ≤ 40 := by
    simpa only [hxc] using card_le_card (face_zero_subset hXT)
  have heq := published_composition_zeros X Y
  by_contra hnot
  have hforty : (signZeros (compose X Y)).card = 40 := by rw [heq] at hupper ⊢; omega
  have ht := (uniform_covector_cocircuit_iff A hu _ hcov hn).mpr hforty
  have hxeq := ht.2.2 X hx.1 hx.2.1 hXT
  have hyeq := ht.2.2 Y hy.1 hy.2.1 hYT
  exact hne (hxeq.trans hyeq.symm)

theorem published_adjacent_iff (A : Matrix (Fin 80) (Fin 41) ℚ)
    (hu : Uniform A) (X Y : SignVector) : PublishedAdjacent A X Y ↔ Adjacent A X Y := by
  constructor
  · rintro ⟨hpx, hpy, hne, hlo, hsep⟩
    have hx := (published_cocircuit_iff A hu X).mp hpx
    have hy := (published_cocircuit_iff A hu Y).mp hpy
    apply (uniform_adjacency_iff A hu X Y hx hy).mpr
    exact ⟨hne, (published_separation_iff_compose A X Y hx.1 hy.1).mp hsep,
      by rw [published_composition_zeros]; exact published_common_zeros_eq_39 A hu X Y hx hy hne hsep hlo⟩
  · intro he
    obtain ⟨hne, hcomm, hcard⟩ := (uniform_adjacency_iff A hu X Y he.1 he.2.1).mp he
    refine ⟨(published_cocircuit_iff A hu X).mpr he.1,
      (published_cocircuit_iff A hu Y).mpr he.2.1, hne, ?_,
      (published_separation_iff_compose A X Y he.1.1 he.2.1.1).mpr hcomm⟩
    rw [published_composition_zeros] at hcard
    omega

def PublishedShortWalk (A : Matrix (Fin 80) (Fin 41) ℚ) (X Y : SignVector) : Prop :=
  ∃ L : ℕ, L ≤ 41 ∧ ∃ p : Fin (L + 1) → SignVector,
    p 0 = X ∧ p (Fin.last L) = Y ∧
    (∀ i, PublishedCocircuit A (p i)) ∧
    ∀ i : Fin L, PublishedAdjacent A (p i.castSucc) (p i.succ)

theorem published_short_walk_iff (A : Matrix (Fin 80) (Fin 41) ℚ)
    (hu : Uniform A) (X Y : SignVector) : PublishedShortWalk A X Y ↔ ShortWalk A X Y := by
  simp only [PublishedShortWalk, ShortWalk, published_cocircuit_iff A hu,
    published_adjacent_iff A hu]

theorem proposed_endpoint_implies_published : ProposedEndpoint →
    ∃ A : Matrix (Fin 80) (Fin 41) ℚ, Uniform A ∧ ∃ X Y : SignVector,
      PublishedCocircuit A X ∧ PublishedCocircuit A Y ∧
      Complementary X Y ∧ ¬ PublishedShortWalk A X Y := by
  rintro ⟨A, hu, X, Y, hx, hy, hc, hn⟩
  exact ⟨A, hu, X, Y, (published_cocircuit_iff A hu X).mpr hx,
    (published_cocircuit_iff A hu Y).mpr hy, hc,
    fun hw => hn ((published_short_walk_iff A hu X Y).mp hw)⟩

#print axioms published_cocircuit_iff
#print axioms published_separation_iff_compose
#print axioms published_composition_zeros
#print axioms published_common_zeros_eq_39
#print axioms published_adjacent_iff
#print axioms published_short_walk_iff
#print axioms proposed_endpoint_implies_published
end
end ADKZPricing
