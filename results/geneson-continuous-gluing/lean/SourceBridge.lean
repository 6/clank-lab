import Solution

open Set MeasureTheory
namespace SrcCheck

/-- Projections as written in the journal. -/
def XP (P : Set (ℝ × ℝ)) : Set ℝ := {x | ∃ y, (x, y) ∈ P}
def YP (P : Set (ℝ × ℝ)) : Set ℝ := {y | ∃ x, (x, y) ∈ P}

/-- Equivalent difference form of the definition on journal p. 2: S contains P iff there are f_X : X_P → X_S, f_Y : Y_P → Y_S,
with f(x0) - f(x1) ≥ x0 - x1 for x0 > x1 (both axes) and (f_X x, f_Y y) ∈ S for (x,y) ∈ P. -/
def Cont (P S : Set (ℝ × ℝ)) : Prop :=
  ∃ (fX : XP P → XP S) (fY : YP P → YP S),
    (∀ x0 x1 : XP P, (x1 : ℝ) < x0 → (x0 : ℝ) - x1 ≤ (fX x0 : ℝ) - fX x1) ∧
    (∀ y0 y1 : YP P, (y1 : ℝ) < y0 → (y0 : ℝ) - y1 ≤ (fY y0 : ℝ) - fY y1) ∧
    ∀ x y (h : (x, y) ∈ P),
      (((fX ⟨x, y, h⟩ : ℝ), (fY ⟨y, x, h⟩ : ℝ)) ∈ S)

lemma X_eq (P : Set (ℝ × ℝ)) : Geneson.X P = XP P := by
  ext x; simp [Geneson.X, XP]
lemma Y_eq (P : Set (ℝ × ℝ)) : Geneson.Y P = YP P := by
  ext x; simp [Geneson.Y, YP]

def eX (P : Set (ℝ × ℝ)) : Geneson.X P ≃ XP P := Equiv.subtypeEquivRight (by simp [X_eq])
def eY (P : Set (ℝ × ℝ)) : Geneson.Y P ≃ YP P := Equiv.subtypeEquivRight (by simp [Y_eq])
@[simp] lemma eX_val (P) (x : Geneson.X P) : ((eX P x : XP P) : ℝ) = x := rfl
@[simp] lemma eY_val (P) (x : Geneson.Y P) : ((eY P x : YP P) : ℝ) = x := rfl
@[simp] lemma eX_symm_val (P) (x : XP P) : (((eX P).symm x : Geneson.X P) : ℝ) = x := rfl
@[simp] lemma eY_symm_val (P) (x : YP P) : (((eY P).symm x : Geneson.Y P) : ℝ) = x := rfl

lemma cont_iff (P S : Set (ℝ × ℝ)) : Cont P S ↔ Geneson.Contains P S := by
  constructor
  · rintro ⟨fX, fY, h1, h2, h3⟩
    refine ⟨fun x => (eX S).symm (fX (eX P x)), fun y => (eY S).symm (fY (eY P y)), ?_, ?_, ?_⟩
    · intro x x' hxx
      rw [le_div_iff₀ (sub_pos.mpr hxx)]
      simpa using h1 (eX P x') (eX P x) hxx
    · intro y y' hyy
      rw [le_div_iff₀ (sub_pos.mpr hyy)]
      simpa using h2 (eY P y') (eY P y) hyy
    · rintro ⟨⟨x, y⟩, h⟩
      exact h3 x y h
  · rintro ⟨fX, fY, h1, h2, h3⟩
    refine ⟨fun x => eX S (fX ((eX P).symm x)), fun y => eY S (fY ((eY P).symm y)), ?_, ?_, ?_⟩
    · intro x0 x1 hlt
      have := (le_div_iff₀ (sub_pos.mpr hlt)).1 (h1 ((eX P).symm x1) ((eX P).symm x0) hlt)
      simpa using this
    · intro y0 y1 hlt
      have := (le_div_iff₀ (sub_pos.mpr hlt)).1 (h2 ((eY P).symm y1) ((eY P).symm y0) hlt)
      simpa using this
    · intro x y h
      exact h3 ⟨(x, y), h⟩

/-- Equivalent difference form of the definition on journal p. 2: opx(n,P) = sup of μ₂(S) over open P-free S ⊆ [0,n]²
(ambient open, as in the paper's proof that such S avoids the boundary). -/
noncomputable def opx (n : ℝ) (P : Set (ℝ × ℝ)) : ℝ :=
  sSup {m : ℝ | ∃ S : Set (ℝ × ℝ), IsOpen S ∧ (∀ z ∈ S, 0 ≤ z.1 ∧ z.1 ≤ n ∧ 0 ≤ z.2 ∧ z.2 ≤ n)
    ∧ ¬ Cont P S ∧ m = (MeasureTheory.volume S).toReal}

lemma opx_eq (n : ℝ) (P : Set (ℝ × ℝ)) : opx n P = Geneson.opx n P := by
  unfold opx Geneson.opx
  congr 1
  ext m
  simp only [mem_ofPred_eq, cont_iff]
  constructor
  · rintro ⟨S, ho, hs, hc, rfl⟩
    refine ⟨S, ho, fun z hz => ?_, hc, rfl⟩
    obtain ⟨a, b, c, d⟩ := hs z hz
    exact ⟨⟨a, b⟩, ⟨c, d⟩⟩
  · rintro ⟨S, ho, hs, hc, rfl⟩
    refine ⟨S, ho, fun z hz => ?_, hc, rfl⟩
    obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := hs hz
    exact ⟨a, b, c, d⟩

/-- Journal Conjecture 6.3, stated in the independent vocabulary. -/
theorem conjecture_6_3_source
    (n : ℝ) (hn : 0 < n) (P Q : Set (ℝ × ℝ)) (c d : ℝ)
    (hP1 : (c, d) ∈ P) (hQ1 : (c, d) ∈ Q)
    (hP : ∀ p ∈ P, p ≠ (c, d) → p.1 ≤ c ∧ p.2 ≤ d)
    (hQ : ∀ q ∈ Q, q ≠ (c, d) → c ≤ q.1 ∧ d ≤ q.2) :
    opx n (P ∪ Q) ≤ opx n P + opx n Q := by
  rw [opx_eq, opx_eq, opx_eq]
  refine Geneson.geneson_conjecture_6_3 n hn P Q c d hP1 hQ1 ?_ ?_
  · intro p hp
    by_cases h : p = (c, d)
    · subst h; exact ⟨le_rfl, le_rfl⟩
    · exact hP p hp h
  · intro q hq
    by_cases h : q = (c, d)
    · subst h; exact ⟨le_rfl, le_rfl⟩
    · exact hQ q hq h


end SrcCheck
