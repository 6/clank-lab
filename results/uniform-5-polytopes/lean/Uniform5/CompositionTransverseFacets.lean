import Uniform5.CompositionPolygonClosure
import Mathlib.Logic.Equiv.Fin.Rotate

/-! The exact facet cycle around an actual polygon, including uniqueness,
complete coverage, and the two facets incident with each cell. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

/-- At most two distinct three-cells of a four-face contain a fixed
nonempty two-face. This is the proved ridge-incidence theorem inside it. -/
theorem fourFace_three_cells {P G F C₁ C₂ C₃ : Set E} (hP : FinitePolytope P)
    (hG : IsConvexFace P G) (hGne : G.Nonempty) (hdG : affineDimension G = 2)
    (hF : IsConvexFace P F) (hdF : affineDimension F = 4)
    (hC₁ : IsConvexFace P C₁) (hC₂ : IsConvexFace P C₂) (hC₃ : IsConvexFace P C₃)
    (hGC₁ : G ⊆ C₁) (hGC₂ : G ⊆ C₂) (hGC₃ : G ⊆ C₃)
    (hC₁F : C₁ ⊆ F) (hC₂F : C₂ ⊆ F) (hC₃F : C₃ ⊆ F)
    (hdC₁ : affineDimension C₁ = 3) (hdC₂ : affineDimension C₂ = 3)
    (hdC₃ : affineDimension C₃ = 3) : C₁ = C₂ ∨ C₁ = C₃ ∨ C₂ = C₃ := by
  have hGF : G ⊆ F := hGC₁.trans hC₁F
  have hFP := finitePolytope_face hP hF (hGne.mono hGF)
  obtain ⟨A, B, _, hclass⟩ := finitePolytope_ridge_two_facets hFP
    (face_restrict hG hF.2.1 hGF) hGne (by omega)
  have hclass' (C : Set E) (hC : IsConvexFace P C) (hGC : G ⊆ C) (hCF : C ⊆ F)
      (hdC : affineDimension C = 3) : C = A ∨ C = B :=
    (hclass C).mp ⟨⟨face_restrict hC hF.2.1 hCF, hGne.mono hGC, by omega⟩, hGC⟩
  rcases hclass' C₁ hC₁ hGC₁ hC₁F hdC₁ with h₁ | h₁ <;>
    rcases hclass' C₂ hC₂ hGC₂ hC₂F hdC₂ with h₂ | h₂ <;>
    rcases hclass' C₃ hC₃ hGC₃ hC₃F hdC₃ with h₃ | h₃ <;> aesop

/-- Explicit modular action of the finite cyclic successor. -/
theorem finRotate_val_mod {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    (finRotate n i).val = (i.val + 1) % n := by
  cases n with
  | zero => omega
  | succ m =>
    rw [finRotate_succ_apply]
    simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < m + 1 by omega)]

/-- With at least three indices, neither one nor two successor steps
return to the starting index. -/
theorem finRotate_ne_and_twice_ne {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    finRotate n i ≠ i ∧ finRotate n (finRotate n i) ≠ i := by
  have hval := finRotate_val_mod (by omega : 2 ≤ n)
  constructor
  · intro h
    have hv := congrArg Fin.val h
    rw [hval] at hv
    by_cases heq : i.val + 1 = n
    · rw [heq, Nat.mod_self] at hv
      omega
    · rw [Nat.mod_eq_of_lt (by omega : i.val + 1 < n)] at hv
      omega
  · intro h
    have hv := congrArg Fin.val h
    rw [hval, hval] at hv
    have hm : ((i.val + 1) % n + 1) % n = (i.val + 2) % n := by
      have hh := Nat.add_mod (i.val + 1) 1 n
      simpa only [Nat.mod_eq_of_lt (show 1 < n by omega), Nat.add_assoc] using hh.symm
    rw [hm] at hv
    by_cases hlt : i.val + 2 < n
    · rw [Nat.mod_eq_of_lt hlt] at hv
      omega
    · rw [Nat.mod_eq_sub_mod (by omega : n ≤ i.val + 2),
        Nat.mod_eq_of_lt (by omega : i.val + 2 - n < n)] at hv
      omega

/-- A closed natural-index cycle agrees with finite cyclic successor. -/
theorem cycle_apply_finRotate {α : Type*} {n : ℕ} (hn : 2 ≤ n)
    (C : ℕ → α) (hcycle : C n = C 0) (i : Fin n) : C (finRotate n i) = C (i.val + 1) := by
  rw [finRotate_val_mod hn]
  by_cases hlt : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt]
  · have heq : i.val + 1 = n := by omega
    rw [heq, Nat.mod_self, hcycle]

/-- Two known distinct members identify a predicate's two-element class. -/
theorem two_members_exhaust {α : Type*} (p : α → Prop) {a b : α}
    (h : ∃ x y, x ≠ y ∧ ∀ z, p z ↔ z = x ∨ z = y)
    (ha : p a) (hb : p b) (hab : a ≠ b) : ∀ z, p z ↔ z = a ∨ z = b := by
  obtain ⟨x, y, hxy, hclass⟩ := h
  have ha' := (hclass a).mp ha
  have hb' := (hclass b).mp hb
  intro z
  rw [hclass]
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;> aesop

set_option maxHeartbeats 650000 in
/-- The already constructed actual cell cycle determines exactly the
facet cycle: unique consecutive facets, no repetitions, all facets above
the polygon, and precisely the previous/next facets at each cell. -/
theorem ordered_cell_cycle_facet_cycle {P G : Set E} (hP : FinitePolytope P)
    (hdP : affineDimension P = 5) (hG : IsConvexFace P G) (hGne : G.Nonempty)
    (hdG : affineDimension G = 2) {n : ℕ} (hn : 3 ≤ n) (C : ℕ → Set E)
    (hC : ∀ i, IsConvexFace P (C i)) (hGC : ∀ i, G ⊆ C i)
    (hdC : ∀ i, affineDimension (C i) = 3) (hcycle : C n = C 0)
    (hinj : Set.InjOn C (Iio n))
    (hcov : ∀ F, IsConvexFace P F → G ⊆ F → affineDimension F = 3 → ∃ i < n, C i = F)
    (hadj : ∀ i < n, ∃ F, Facet P F ∧ G ⊆ F ∧ C i ⊆ F ∧ C (i + 1) ⊆ F) :
    ∃ A : Fin n → Set E,
      (∀ i, Facet P (A i) ∧ G ⊆ A i ∧ C i ⊆ A i ∧ C (i.val + 1) ⊆ A i) ∧
      Function.Injective A ∧
      (∀ F, (Facet P F ∧ G ⊆ F) ↔ ∃ i, A i = F) ∧
      (∀ i : Fin n, ∀ F, (Facet P F ∧ C i ⊆ F) ↔
        F = A ((finRotate n).symm i) ∨ F = A i) ∧
      (∀ i : Fin n, ∃! F, Facet P F ∧ C i ⊆ F ∧ C (i.val + 1) ⊆ F) := by
  let R := finRotate n
  let A : Fin n → Set E := fun i => (hadj i i.isLt).choose
  have hA (i : Fin n) : Facet P (A i) ∧ G ⊆ A i ∧ C i ⊆ A i ∧ C (i.val + 1) ⊆ A i :=
    (hadj i i.isLt).choose_spec
  have hnext (i : Fin n) : C (R i) ⊆ A i := by
    rw [cycle_apply_finRotate (by omega : 2 ≤ n) C hcycle]
    exact (hA i).2.2.2
  have hCin : Function.Injective (fun i : Fin n => C i) := by
    intro i j h
    exact Fin.ext (hinj i.isLt j.isLt h)
  have hR (i : Fin n) : R i ≠ i ∧ R (R i) ≠ i := finRotate_ne_and_twice_ne hn i
  have hthree (F : Set E) (hF : Facet P F) (i j k : Fin n)
      (hi : C i ⊆ F) (hj : C j ⊆ F) (hk : C k ⊆ F) : i = j ∨ i = k ∨ j = k := by
    have hdF : affineDimension F = 4 := by have hh := hF.2.2; omega
    rcases fourFace_three_cells hP hG hGne hdG hF.1 hdF (hC i) (hC j) (hC k)
      (hGC i) (hGC j) (hGC k) hi hj hk (hdC i) (hdC j) (hdC k) with h | h | h
    · exact Or.inl (hCin h)
    · exact Or.inr (Or.inl (hCin h))
    · exact Or.inr (Or.inr (hCin h))
  have hAinj : Function.Injective A := by
    intro i j heq
    have hj : C j ⊆ A i := heq.symm ▸ (hA j).2.2.1
    have hjnext : C (R j) ⊆ A i := heq.symm ▸ hnext j
    rcases hthree (A i) (hA i).1 i (R i) j (hA i).2.2.1 (hnext i) hj with h | h | h
    · exact False.elim ((hR i).1 h.symm)
    · exact h
    · rcases hthree (A i) (hA i).1 i (R i) (R j) (hA i).2.2.1 (hnext i) hjnext with h' | h' | h'
      · exact False.elim ((hR i).1 h'.symm)
      · have hbad : R (R i) = i := by rw [h]; exact h'.symm
        exact False.elim ((hR i).2 hbad)
      · exact R.injective h'
  have hprevne (i : Fin n) : R.symm i ≠ i := by
    intro h
    have hh := congrArg R h
    rw [R.apply_symm_apply] at hh
    exact (hR i).1 hh.symm
  have hprev (i : Fin n) : C i ⊆ A (R.symm i) := by
    simpa only [R.apply_symm_apply] using hnext (R.symm i)
  have htwo (i : Fin n) : ∀ F, (Facet P F ∧ C i ⊆ F) ↔ F = A (R.symm i) ∨ F = A i := by
    apply two_members_exhaust
    · exact finitePolytope_ridge_two_facets hP (hC i) (hGne.mono (hGC i)) (by rw [hdC, hdP])
    · exact ⟨(hA (R.symm i)).1, hprev i⟩
    · exact ⟨(hA i).1, (hA i).2.2.1⟩
    · intro h
      exact hprevne i (hAinj h)
  have hcoverage (F : Set E) : (Facet P F ∧ G ⊆ F) ↔ ∃ i, A i = F := by
    constructor
    · rintro ⟨hF, hGF⟩
      have hdF : affineDimension F = 4 := by have hh := hF.2.2; omega
      have hFP := finitePolytope_face hP hF.1 hF.2.1
      obtain ⟨X, Y, _, hfac⟩ := finitePolytope_ridge_two_facets hFP
        (face_restrict hG hF.1.2.1 hGF) hGne (by omega)
      have hX := (hfac X).mpr (Or.inl rfl)
      have hdX : affineDimension X = 3 := by have hh := hX.1.2.2; omega
      obtain ⟨i, hi, hCi⟩ := hcov X (face_of_face hF.1 hX.1.1) hX.2 hdX
      have hCiF : C i ⊆ F := hCi.symm ▸ hX.1.1.2.1
      rcases (htwo ⟨i, hi⟩ F).mp ⟨hF, hCiF⟩ with h | h
      · exact ⟨R.symm ⟨i, hi⟩, h.symm⟩
      · exact ⟨⟨i, hi⟩, h.symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨(hA i).1, (hA i).2.1⟩
  have huniq (i : Fin n) : ∃! F, Facet P F ∧ C i ⊆ F ∧ C (i.val + 1) ⊆ F := by
    refine ⟨A i, ⟨(hA i).1, (hA i).2.2.1, (hA i).2.2.2⟩, ?_⟩
    rintro F ⟨hF, hi, hj⟩
    rcases (htwo i F).mp ⟨hF, hi⟩ with h | h
    · subst F
      have hj' : C (R i) ⊆ A (R.symm i) := by
        rw [cycle_apply_finRotate (by omega : 2 ≤ n) C hcycle]
        exact hj
      rcases hthree _ (hA (R.symm i)).1 (R.symm i) i (R i)
        (hA (R.symm i)).2.2.1 (hprev i) hj' with h' | h' | h'
      · exact False.elim (hprevne i h')
      · have hb := congrArg R h'
        rw [R.apply_symm_apply] at hb
        exact False.elim ((hR i).2 hb.symm)
      · exact False.elim ((hR i).1 h'.symm)
    · exact h
  exact ⟨A, hA, hAinj, hcoverage, htwo, huniq⟩

/-- Consecutive cells in a genuine cycle with at least three entries are
distinct, including the last-to-first pair. -/
theorem cell_cycle_consecutive_ne {α : Type*} {n : ℕ} (hn : 3 ≤ n)
    (C : ℕ → α) (hcycle : C n = C 0) (hinj : Set.InjOn C (Iio n))
    {i : ℕ} (hi : i < n) : C i ≠ C (i + 1) := by
  intro h
  let j : Fin n := ⟨i, hi⟩
  have hh : C j = C (finRotate n j) := by
    rw [cycle_apply_finRotate (by omega : 2 ≤ n) C hcycle]
    exact h
  have heq : j = finRotate n j := Fin.ext (hinj j.isLt (finRotate n j).isLt hh)
  exact (finRotate_ne_and_twice_ne hn j).1 heq.symm

/-- Every actual polygon of a uniform five-polytope has complete,
nonrepeating cell and facet cycles with exact consecutive incidence. -/
theorem unitUniform5_polygon_facet_cycle {P G : Set (Space 5)}
    (hP : UnitUniform 5 P) {k : ℕ} (hG : PolygonFace P G k) :
    ∃ n : ℕ, 3 ≤ n ∧ ∃ C : ℕ → Set (Space 5),
    ∃ _hC : ∀ i, IsConvexFace P (C i), ∃ _hGC : ∀ i, G ⊆ C i,
      (∀ i, affineDimension (C i) = 3) ∧ C n = C 0 ∧ Set.InjOn C (Iio n) ∧
      (∀ F, IsConvexFace P F → G ⊆ F → affineDimension F = 3 → ∃ i < n, C i = F) ∧
      ∃ A : Fin n → Set (Space 5),
        (∀ i, Facet P (A i) ∧ G ⊆ A i ∧ C i ⊆ A i ∧ C (i.val + 1) ⊆ A i) ∧
        Function.Injective A ∧
        (∀ F, (Facet P F ∧ G ⊆ F) ↔ ∃ i, A i = F) ∧
        (∀ i : Fin n, ∀ F, (Facet P F ∧ C i ⊆ F) ↔
          F = A ((finRotate n).symm i) ∨ F = A i) ∧
        (∀ i : Fin n, ∃! F, Facet P F ∧ C i ⊆ F ∧ C (i.val + 1) ⊆ F) := by
  obtain ⟨n, hn, C, hC, hGC, hdC, hcycle, hinj, hcov, hadj, _⟩ :=
    unitUniform5_polygon_closure hP hG
  refine ⟨n, hn, C, hC, hGC, hdC, hcycle, hinj, hcov, ?_⟩
  exact ordered_cell_cycle_facet_cycle (uniform_finitePolytope hP.1) (uniform_dimension hP.1)
    hG.1 (polygonFace_nonempty hG) hG.2.1 hn C hC hGC hdC hcycle hinj hcov hadj

end Uniform5.Composition
