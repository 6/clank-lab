import Endpoint
import Mathlib.Data.List.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

/-! Finite iid counting: normalization and the exactly-once identity. -/
namespace ADG
set_option linter.unusedSectionVars false
open Finset

variable {α : Type} [Fintype α] [DecidableEq α]

theorem iidMass_nonneg (μ : α → ℝ) (hμ : ∀ x, 0 ≤ μ x) {n} (a : Fin n → α) :
    0 ≤ iidMass μ a := Finset.prod_nonneg (fun _ _ => hμ _)

theorem iidProb_nonneg (μ : α → ℝ) (hμ : ∀ x, 0 ≤ μ x) (n) (E) :
    0 ≤ iidProb μ n E := by
  classical
  exact Finset.sum_nonneg (fun a _ => by split_ifs; exact iidMass_nonneg μ hμ a; rfl)

theorem iidProb_univ (μ : α → ℝ) (hμ : ∑ x, μ x = 1) (n) :
    iidProb μ n (fun _ => True) = 1 := by
  classical
  simp only [iidProb, if_true, iidMass]
  rw [← Fintype.prod_sum]
  simp [hμ]

theorem iidProb_congr (μ : α → ℝ) {n} {E H : (Fin n → α) → Prop}
    (h : ∀ a, E a ↔ H a) : iidProb μ n E = iidProb μ n H := by
  classical
  unfold iidProb
  exact Finset.sum_congr rfl (fun a _ => by rw [h a])

theorem iidProb_succ (μ : α → ℝ) (n : ℕ) (E : (Fin (n+1) → α) → Prop) :
    iidProb μ (n+1) E = ∑ x, μ x * iidProb μ n (fun a => E (Fin.cons x a)) := by
  classical
  unfold iidProb
  calc
    _ = ∑ t : α × (Fin n → α), if E (Fin.cons t.1 t.2) then
        iidMass μ (Fin.cons t.1 t.2) else 0 := by
      apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => α)).symm
      intro a
      simp
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp [iidMass, Fin.prod_univ_succ, Finset.mul_sum, mul_ite]

/-- The subsequence of forbidden atoms is prescribed, retaining actual column order. -/
def pattern (F : Finset α) (ss : List α) {n : ℕ} (a : Fin n → α) : Prop :=
  (List.ofFn a).filter (fun x => decide (x ∈ F)) = ss

noncomputable def patternProb (μ : α → ℝ) (F : Finset α) (ss : List α) (n : ℕ) : ℝ :=
  iidProb μ n (pattern F ss)

theorem patternProb_zero (μ : α → ℝ) (F : Finset α) (ss : List α) :
    patternProb μ F ss 0 = if ss = [] then 1 else 0 := by
  classical
  simp [patternProb, iidProb, pattern, iidMass, eq_comm]

theorem patternProb_nil_succ (μ : α → ℝ) (F : Finset α) (n : ℕ) :
    patternProb μ F [] (n+1) = (∑ x, if x ∉ F then μ x else 0) * patternProb μ F [] n := by
  classical
  rw [patternProb, iidProb_succ, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : x ∈ F
  · simp [patternProb, iidProb, pattern, List.ofFn_succ, h]
  · simp [patternProb, iidProb, pattern, List.ofFn_succ, h]

theorem patternProb_cons_succ (μ : α → ℝ) (F : Finset α) (s : α) (ss : List α)
    (hs : s ∈ F) (n : ℕ) :
    patternProb μ F (s::ss) (n+1) =
      (∑ x, if x ∉ F then μ x else 0) * patternProb μ F (s::ss) n +
      μ s * patternProb μ F ss n := by
  classical
  rw [patternProb, iidProb_succ]
  calc
    _ = ∑ x, ((if x ∉ F then μ x else 0) * patternProb μ F (s::ss) n +
        if x = s then μ x * patternProb μ F ss n else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : x ∈ F
      · by_cases he : x = s
        · subst x
          simp [patternProb, iidProb, pattern, List.ofFn_succ, hs]
          left
          apply Finset.sum_congr rfl
          intro a ha
          congr 3
        · simp [patternProb, iidProb, pattern, List.ofFn_succ, h, he]
      · have he : x ≠ s := fun he => h (he ▸ hs)
        simp [patternProb, iidProb, pattern, List.ofFn_succ, h, he]
        left
        apply Finset.sum_congr rfl
        intro a ha
        congr 3
    _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_mul]

theorem patternProb_formula (μ : α → ℝ) (F : Finset α) (ss : List α)
    (hss : ∀ x ∈ ss, x ∈ F) (n : ℕ) :
    patternProb μ F ss n = (n.choose ss.length : ℝ) * (ss.map μ).prod *
      (∑ x, if x ∉ F then μ x else 0) ^ (n - ss.length) := by
  classical
  induction n generalizing ss with
  | zero =>
    cases ss <;> simp [patternProb_zero]
  | succ n ih =>
    cases ss with
    | nil =>
      rw [patternProb_nil_succ, ih [] (by simp)]
      simp [pow_succ]
      ring
    | cons s ss =>
      have hs : s ∈ F := hss s (by simp)
      have ht : ∀ x ∈ ss, x ∈ F := fun x hx => hss x (by simp [hx])
      rw [patternProb_cons_succ μ F s ss hs, ih (s::ss) hss, ih ss ht]
      simp only [List.length_cons, List.map_cons, List.prod_cons]
      by_cases h : ss.length < n
      · have he : n - ss.length = n - (ss.length + 1) + 1 := by omega
        have he' : n + 1 - (ss.length + 1) = n - ss.length := by omega
        rw [he', Nat.choose_succ_succ, Nat.cast_add, he, pow_succ]
        ring
      · by_cases he : ss.length = n
        · simp [he]
        · have hn : n < ss.length := by omega
          have hn' : n < ss.length + 1 := by omega
          have hn'' : n + 1 < ss.length + 1 := by omega
          simp [Nat.choose_eq_zero_of_lt hn, Nat.choose_eq_zero_of_lt hn',
            Nat.choose_eq_zero_of_lt hn'']

theorem outsideMass (μ : α → ℝ) (F : Finset α) (hμ : ∑ x, μ x = 1) :
    (∑ x, if x ∉ F then μ x else 0) = 1 - ∑ x ∈ F, μ x := by
  classical
  have h : (∑ x, if x ∈ F then μ x else 0) +
      (∑ x, if x ∉ F then μ x else 0) = 1 := by
    rw [← Finset.sum_add_distrib, ← hμ]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hxF : x ∈ F <;> simp [hxF]
  simp only [Finset.sum_ite_mem, Finset.univ_inter] at h
  simpa using eq_sub_of_add_eq' h

/-- Increasing three designated positions, all other columns outside the forbidden set. -/
def orderedThree (F : Finset α) (s t u : α) {n : ℕ} (a : Fin n → α) : Prop :=
  ∃ i j k : Fin n, i < j ∧ j < k ∧ a i = s ∧ a j = t ∧ a k = u ∧
    ∀ z, z ≠ i → z ≠ j → z ≠ k → a z ∉ F

def forbiddenIndices (F : Finset α) {n : ℕ} (a : Fin n → α) : List (Fin n) :=
  (List.finRange n).filter (fun i => decide (a i ∈ F))

@[simp] theorem mem_forbiddenIndices (F : Finset α) {n : ℕ} (a : Fin n → α) (i) :
    i ∈ forbiddenIndices F a ↔ a i ∈ F := by simp [forbiddenIndices]

theorem forbiddenIndices_sorted (F : Finset α) {n : ℕ} (a : Fin n → α) :
    (forbiddenIndices F a).Sorted (· < ·) :=
  (List.pairwise_lt_finRange n).filter _

theorem forbiddenIndices_map (F : Finset α) {n : ℕ} (a : Fin n → α) :
    (forbiddenIndices F a).map a = (List.ofFn a).filter (fun x => decide (x ∈ F)) := by
  simp only [List.ofFn_eq_map, List.filter_map, forbiddenIndices, Function.comp_def]

theorem pattern_three_iff (F : Finset α) (s t u : α) (hs : s ∈ F) (ht : t ∈ F)
    (hu : u ∈ F) {n : ℕ} (a : Fin n → α) :
    pattern F [s,t,u] a ↔ orderedThree F s t u a := by
  classical
  constructor
  · intro hp
    have hm : (forbiddenIndices F a).map a = [s,t,u] :=
      (forbiddenIndices_map F a).trans hp
    obtain ⟨i, l₁, hi, hai, hm₁⟩ := List.map_eq_cons_iff.mp hm
    obtain ⟨j, l₂, hj, haj, hm₂⟩ := List.map_eq_cons_iff.mp hm₁
    obtain ⟨k, l₃, hk, hak, hm₃⟩ := List.map_eq_cons_iff.mp hm₂
    have hn : l₃ = [] := List.map_eq_nil_iff.mp hm₃
    have hl : forbiddenIndices F a = [i,j,k] := by simp_all
    have hsort := forbiddenIndices_sorted F a
    rw [hl] at hsort
    have hij : i < j := (List.pairwise_cons.mp hsort).1 j (by simp)
    have hjk : j < k := (List.pairwise_cons.mp (List.pairwise_cons.mp hsort).2).1 k (by simp)
    refine ⟨i,j,k,hij,hjk,hai,haj,hak,?_⟩
    intro z hzi hzj hzk hzF
    have hz : z ∈ forbiddenIndices F a := (mem_forbiddenIndices F a z).mpr hzF
    simp [hl, hzi, hzj, hzk] at hz
  · rintro ⟨i,j,k,hij,hjk,hai,haj,hak,hout⟩
    have hik := lt_trans hij hjk
    have hl : forbiddenIndices F a = [i,j,k] := by
      apply List.Sorted.eq_of_mem_iff (forbiddenIndices_sorted F a)
      · simp [List.sorted_cons, hij, hjk, hik]
      · intro z
        simp only [mem_forbiddenIndices, List.mem_cons, List.not_mem_nil, or_false]
        constructor
        · intro hz
          by_contra hh
          push_neg at hh
          exact hout z hh.1 hh.2.1 hh.2.2 hz
        · rintro (rfl | rfl | rfl) <;> simp_all
    unfold pattern
    rw [← forbiddenIndices_map, hl]
    simp [hai, haj, hak]

theorem exactlyOnce_pattern_iff (F : Finset α) (s₁ s₂ s₃ : α)
    (h₁ : s₁ ∈ F) (h₂ : s₂ ∈ F) (h₃ : s₃ ∈ F) {n : ℕ} (a : Fin n → α) :
    exactlyOnceMiddleFirst F s₁ s₂ s₃ a ↔
      pattern F [s₂,s₁,s₃] a ∨ pattern F [s₂,s₃,s₁] a := by
  rw [pattern_three_iff F s₂ s₁ s₃ h₂ h₁ h₃,
    pattern_three_iff F s₂ s₃ s₁ h₂ h₃ h₁]
  constructor
  · rintro ⟨i₁,i₂,i₃,h₂₁,h₂₃,h₁₃,ha₁,ha₂,ha₃,hout⟩
    rcases lt_or_gt_of_ne h₁₃ with hh | hh
    · exact Or.inl ⟨i₂,i₁,i₃,h₂₁,hh,ha₂,ha₁,ha₃,
        fun z hzi₂ hzi₁ hzi₃ => hout z hzi₁ hzi₂ hzi₃⟩
    · exact Or.inr ⟨i₂,i₃,i₁,h₂₃,hh,ha₂,ha₃,ha₁,
        fun z hzi₂ hzi₃ hzi₁ => hout z hzi₁ hzi₂ hzi₃⟩
  · rintro (⟨i,j,k,hij,hjk,hai,haj,hak,hout⟩ | ⟨i,j,k,hij,hjk,hai,haj,hak,hout⟩)
    · exact ⟨j,i,k,hij,lt_trans hij hjk,ne_of_lt hjk,haj,hai,hak,
        fun z hzj hzi hzk => hout z hzi hzj hzk⟩
    · exact ⟨k,i,j,lt_trans hij hjk,hij,ne_of_gt hjk,hak,hai,haj,
        fun z hzk hzi hzj => hout z hzi hzj hzk⟩

theorem iidProb_disjoint_or (μ : α → ℝ) (n : ℕ) (E H : (Fin n → α) → Prop)
    (hd : ∀ a, ¬ (E a ∧ H a)) :
    iidProb μ n (fun a => E a ∨ H a) = iidProb μ n E + iidProb μ n H := by
  classical
  unfold iidProb
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases he : E a <;> by_cases hh : H a <;> simp_all

theorem falling_three_choose (n : ℕ) :
    ((n * (n-1) * (n-2) : ℕ) : ℝ) = 6 * (n.choose 3 : ℝ) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose n 3
  norm_num [Nat.descFactorial_succ] at h
  have hc : (((n - 2) * ((n - 1) * n) : ℕ) : ℝ) = 6 * (n.choose 3 : ℝ) := by
    exact_mod_cast h
  push_cast at hc ⊢
  nlinarith

/-- The exactly-once identity, for the actual finite iid weighted sum. -/
theorem exactlyOnce_identity : ExactlyOnceIdentity := by
  intro α _ _ μ hnonneg hnorm F s₁ s₂ s₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ n hn
  rw [iidProb_congr μ (exactlyOnce_pattern_iff F s₁ s₂ s₃ h₁ h₂ h₃)]
  rw [iidProb_disjoint_or]
  · change patternProb μ F [s₂,s₁,s₃] n + patternProb μ F [s₂,s₃,s₁] n = _
    rw [patternProb_formula μ F [s₂,s₁,s₃] (by simp_all),
      patternProb_formula μ F [s₂,s₃,s₁] (by simp_all), outsideMass μ F hnorm]
    simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    rw [falling_three_choose]
    ring
  · intro a ⟨hpa,hpb⟩
    have he : [s₂,s₁,s₃] = [s₂,s₃,s₁] := hpa.symm.trans hpb
    simpa using h₁₃ (List.cons.inj (List.cons.inj he).2).1

theorem exactlyOnce_impossible_of_lt_three (F : Finset α) (s₁ s₂ s₃ : α)
    {n : ℕ} (hn : n < 3) (a : Fin n → α) :
    ¬ exactlyOnceMiddleFirst F s₁ s₂ s₃ a := by
  rintro ⟨i₁,i₂,i₃,h₂₁,h₂₃,h₁₃,_⟩
  have hne : i₁.val ≠ i₃.val := fun h => h₁₃ (Fin.ext h)
  have h₂₁' : i₂.val < i₁.val := h₂₁
  have h₂₃' : i₂.val < i₃.val := h₂₃
  have h₁ := i₁.isLt
  have h₂ := i₂.isLt
  have h₃ := i₃.isLt
  omega

theorem exactlyOnce_probability_zero_of_lt_three (μ : α → ℝ) (F : Finset α)
    (s₁ s₂ s₃ : α) {n : ℕ} (hn : n < 3) :
    iidProb μ n (exactlyOnceMiddleFirst F s₁ s₂ s₃) = 0 := by
  classical
  simp [iidProb, exactlyOnce_impossible_of_lt_three F s₁ s₂ s₃ hn]

theorem columnMass_nonneg (m : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (s : Finset (Fin m)) : 0 ≤ columnMass m p s := by
  apply Finset.prod_nonneg
  intro i hi
  split_ifs <;> linarith

theorem columnMass_split (m : ℕ) (p : ℝ) (s : Finset (Fin m)) :
    columnMass m p s = (∏ i ∈ s, p) * ∏ i ∈ (univ \ s), (1-p) := by
  have hset : univ.filter (fun x : Fin m => x ∉ s) = univ \ s := by
    ext i
    simp
  rw [columnMass, Finset.prod_ite]
  simp [hset]

theorem columnMass_sum (m : ℕ) (p : ℝ) : ∑ s, columnMass m p s = 1 := by
  have h := Finset.prod_add (fun _ : Fin m => p) (fun _ => 1-p) univ
  simp only [add_sub_cancel, Finset.prod_const_one, Finset.powerset_univ] at h
  simpa only [columnMass_split] using h.symm

theorem matrixProb_nonneg (m n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (E : Matrix m n → Prop) : 0 ≤ matrixProb m n p E :=
  iidProb_nonneg _ (columnMass_nonneg m p hp hp') n E

theorem matrixProb_univ (m n : ℕ) (p : ℝ) : matrixProb m n p (fun _ => True) = 1 :=
  iidProb_univ _ (columnMass_sum m p) n

/-- Direct exhaustive word counts, independent of the symbolic counting theorem. -/
def exactlyOnceControlCount (n : ℕ) : ℕ := by
  letI : DecidablePred (exactlyOnceMiddleFirst ({0,1,2} : Finset (Fin 4)) 0 1 2 :
      (Fin n → Fin 4) → Prop) := fun a => by
    unfold exactlyOnceMiddleFirst
    infer_instance
  exact (univ.filter (exactlyOnceMiddleFirst ({0,1,2} : Finset (Fin 4)) 0 1 2 :
      (Fin n → Fin 4) → Prop)).card

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem exactlyOnce_control_count_three : exactlyOnceControlCount 3 = 2 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem exactlyOnce_control_count_four : exactlyOnceControlCount 4 = 8 := by decide

theorem iidProb_constant (c : ℝ) (n : ℕ) (E : (Fin n → α) → Prop) [DecidablePred E] :
    iidProb (fun _ : α => c) n E =
      ((univ.filter E).card : ℝ) * c^n := by
  classical
  simp [iidProb, iidMass, ← Finset.sum_filter, nsmul_eq_mul]

theorem exactlyOnce_uniform_control_law (n : ℕ) :
    iidProb (fun _ : Fin 4 => (1/4 : ℝ)) n
      (exactlyOnceMiddleFirst {0,1,2} 0 1 2) =
      (exactlyOnceControlCount n : ℝ) * (1/4 : ℝ)^n := by
  classical
  rw [iidProb_constant]
  congr 2
  unfold exactlyOnceControlCount
  congr 1
  ext a
  simp

/-- Direct exhaustive controls on the actual event/law; the symbolic identity is unused. -/
theorem exactlyOnce_four_atoms_three :
    iidProb (fun _ : Fin 4 => (1/4 : ℝ)) 3
      (exactlyOnceMiddleFirst {0,1,2} 0 1 2) = 2/64 := by
  rw [exactlyOnce_uniform_control_law, exactlyOnce_control_count_three]
  norm_num

theorem exactlyOnce_four_atoms_four :
    iidProb (fun _ : Fin 4 => (1/4 : ℝ)) 4
      (exactlyOnceMiddleFirst {0,1,2} 0 1 2) = 8/256 := by
  rw [exactlyOnce_uniform_control_law, exactlyOnce_control_count_four]
  norm_num

theorem columnMass_by_card (m : ℕ) (p : ℝ) (s : Finset (Fin m)) :
    columnMass m p s = p ^ s.card * (1-p) ^ (m - s.card) := by
  rw [columnMass_split]
  simp [Finset.card_sdiff (Finset.subset_univ s)]

end ADG
