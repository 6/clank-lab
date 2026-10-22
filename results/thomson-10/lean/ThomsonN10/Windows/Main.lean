/- Adapted from aravindkarthigeyan/thomson-n9-lean,
   proof/lean/ClaudeWindow/Main.lean, MIT,
   commit 168ff0c98cab4dfda0460ba55f8d169070ac385e. -/
import ThomsonN10.Windows.WindowKernel
import ThomsonN10.Windows.Soundness
import ThomsonN10.Windows.AnchorFree

namespace ThomsonN10.Windows
open Iv
theorem d3R_1uu (u : ℝ) : d3R 1 u u = 0 := by unfold d3R; ring
theorem d3R_u1u (u : ℝ) : d3R u 1 u = 0 := by unfold d3R; ring
theorem d3R_uu1 (u : ℝ) : d3R u u 1 = 0 := by unfold d3R; ring

theorem d3R_perm (u v w : ℝ) :
    d3R v u w = d3R u v w ∧ d3R u w v = d3R u v w ∧ d3R w u v = d3R u v w ∧
      d3R v w u = d3R u v w ∧ d3R w v u = d3R u v w := by
  unfold d3R; exact ⟨by ring, by ring, by ring, by ring, by ring⟩

/-- Reordering an anchor triple so that its three pair colors are sorted. -/
theorem sort3 (col : Fin 10 → Fin 10 → ℕ) (hs : ∀ i j, col i j = col j i) (a b c : Fin 10) :
    ∃ p : Fin 10 × Fin 10 × Fin 10,
      (p = (a, b, c) ∨ p = (a, c, b) ∨ p = (b, a, c) ∨ p = (b, c, a) ∨ p = (c, a, b) ∨
        p = (c, b, a)) ∧
      col p.1 p.2.1 ≤ col p.1 p.2.2 ∧ col p.1 p.2.2 ≤ col p.2.1 p.2.2 := by
  have e1 := hs b a
  have e2 := hs c a
  have e3 := hs c b
  rcases le_total (col a b) (col a c) with h1 | h1 <;>
    rcases le_total (col a c) (col b c) with h2 | h2 <;>
    rcases le_total (col a b) (col b c) with h3 | h3
  all_goals first
    | exact ⟨(a, b, c), Or.inl rfl, by simp only; omega⟩
    | exact ⟨(a, c, b), Or.inr (Or.inl rfl), by simp only [e3]; omega⟩
    | exact ⟨(b, a, c), Or.inr (Or.inr (Or.inl rfl)), by simp only [e1]; omega⟩
    | exact ⟨(b, c, a), Or.inr (Or.inr (Or.inr (Or.inl rfl))), by simp only [e1, e2]; omega⟩
    | exact ⟨(c, a, b), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), by simp only [e2, e3]; omega⟩
    | exact ⟨(c, b, a), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))),
        by simp only [e1, e2, e3]; omega⟩

theorem window_rigidity {r : ℝ} (hh : hBox.Mem r)
    (x : Fin 10 → E3) (hx : ∀ i, ‖x i‖ = 1)
    (hwin : ∀ i j, i ≠ j → ∃ c : ℕ, c < 7 ∧
      |inner ℝ (x i) (x j) - palette r c| ≤ (windowRadius : ℝ)) :
    ∃ σ : Equiv.Perm (Fin 10), ∀ i j, i ≠ j →
      |inner ℝ (x i) (x j) - palette r (refColor (σ i) (σ j))| ≤ (windowRadius : ℝ) := by
  classical
  -- 2. the coloring
  let col : Fin 10 → Fin 10 → ℕ := fun i j => if h : i ≠ j then Classical.choose (hwin i j h) else 0
  have hcol : ∀ i j (h : i ≠ j),
      col i j < 7 ∧ |inner ℝ (x i) (x j) - palette r (col i j)| ≤ (windowRadius : ℝ) := by
    intro i j h
    simp only [col, dif_pos h]
    exact Classical.choose_spec (hwin i j h)
  have hsymm : ∀ i j, col i j = col j i := by
    intro i j
    by_cases h : i = j
    · subst h; rfl
    · obtain ⟨h1, h2⟩ := hcol i j h
      obtain ⟨h3, h4⟩ := hcol j i (Ne.symm h)
      rw [real_inner_comm] at h4
      exact window_unique hh h1 h3 h2 h4
  have hmem : ∀ i j, i ≠ j → (box (col i j)).Mem (inner ℝ (x i) (x j)) :=
    fun i j h => window_mem_box hh (hcol i j h).1 (hcol i j h).2
  -- 3. the anchor, distinct and with sorted colors
  have hlt : ∀ i j, col i j < 7 := by
    intro i j
    by_cases h : i ≠ j
    · exact (hcol i j h).1
    · simp only [col, dif_neg h]; norm_num
  obtain ⟨a, b, c, hd⟩ := exists_anchor x hx col hlt hmem
  have hθ : (0 : ℝ) < (thetaQ : ℝ) := by norm_num [thetaQ]
  have hab : a ≠ b := by
    rintro rfl
    rw [real_inner_self_eq_norm_sq, hx, one_pow, d3R_1uu] at hd
    linarith
  have hac : a ≠ c := by
    rintro rfl
    rw [real_inner_self_eq_norm_sq, hx, one_pow, real_inner_comm, d3R_u1u] at hd
    linarith
  have hbc : b ≠ c := by
    rintro rfl
    rw [real_inner_self_eq_norm_sq, hx, one_pow, d3R_uu1] at hd
    linarith
  obtain ⟨⟨a0, a1, a2⟩, hp, hs1, hs2⟩ := sort3 col hsymm a b c
  have eab := real_inner_comm (x a) (x b)
  have eac := real_inner_comm (x a) (x c)
  have ebc := real_inner_comm (x b) (x c)
  have hperm := d3R_perm (inner ℝ (x a) (x b)) (inner ℝ (x a) (x c)) (inner ℝ (x b) (x c))
  have hA : ((thetaQ : ℝ) : ℝ) <
        d3R (inner ℝ (x a0) (x a1)) (inner ℝ (x a0) (x a2)) (inner ℝ (x a1) (x a2)) ∧
      a0 ≠ a1 ∧ a0 ≠ a2 ∧ a1 ≠ a2 := by
    rcases hp with h | h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;>
      obtain ⟨rfl, rfl, rfl⟩ := h <;> refine ⟨?_, ?_, ?_, ?_⟩ <;>
      first
      | exact hab | exact hac | exact hbc | exact hab.symm | exact hac.symm | exact hbc.symm
      | exact hd
      | (simp only [eab, eac, ebc, hperm.1, hperm.2.1, hperm.2.2.1, hperm.2.2.2.1,
          hperm.2.2.2.2]; exact hd)
  obtain ⟨hdA, d01, d02, d12⟩ := hA
  -- 4. the hypotheses of the finite theorem
  have hH : ColHyp box thetaQ col a0 a1 a2 := by
    refine ⟨hsymm, fun i j h => (hcol i j h).1, d01, d02, d12, hs1, hs2, ?_, ?_, ?_⟩
    · have hm := mem_d3 (hmem a0 a1 d01) (hmem a0 a2 d02) (hmem a1 a2 d12)
      have h' : ((thetaQ : ℚ) : ℝ) < ((aD box (col a0 a1) (col a0 a2) (col a1 a2)).hi : ℝ) :=
        lt_of_lt_of_le hdA hm.2
      exact_mod_cast h'
    · intro k k0 k1 k2
      apply Iv.not_excl_of_mem_zero
      have hm := mem_norm (hmem a0 a1 d01) (hmem a0 a2 d02) (hmem a1 a2 d12)
        (hmem k a0 k0) (hmem k a1 k1) (hmem k a2 k2)
      rw [normR_eq_zero (x a0) (x a1) (x a2) (x k) (hx a0) (hx a1) (hx a2) (hx k)] at hm
      exact hm
    · intro k l k0 k1 k2 l0 l1 l2 hkl
      apply Iv.not_excl_of_mem_zero
      have hw0 : (box (col l a0)).Mem (inner ℝ (x a0) (x l)) := by
        rw [real_inner_comm]; exact hmem l a0 l0
      have hw1 : (box (col l a1)).Mem (inner ℝ (x a1) (x l)) := by
        rw [real_inner_comm]; exact hmem l a1 l1
      have hw2 : (box (col l a2)).Mem (inner ℝ (x a2) (x l)) := by
        rw [real_inner_comm]; exact hmem l a2 l2
      have hm := mem_pair (hmem a0 a1 d01) (hmem a0 a2 d02) (hmem a1 a2 d12)
        (hmem k a0 k0) (hmem k a1 k1) (hmem k a2 k2) hw0 hw1 hw2 (hmem k l hkl)
      rw [pairR_eq_zero (x a0) (x a1) (x a2) (x k) (x l) (hx a0) (hx a1) (hx a2)] at hm
      exact hm
  -- 5. the finite classification
  obtain ⟨σ, hσ⟩ := finite_classification coverage_ok records_ok hH
  refine ⟨σ, fun i j hij => ?_⟩
  rw [← hσ i j hij]
  exact (hcol i j hij).2


end ThomsonN10.Windows
