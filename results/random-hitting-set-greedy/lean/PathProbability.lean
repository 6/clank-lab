import PathDefinitions
import Probability

/-! Exact probability of a fixed isolated path, and the forbidden-mass bound. -/
namespace ADG
open Finset
open scoped Classical

noncomputable def pathQ (m : ℕ) (p : ℝ) : ℝ := p^3 * (1-p)^(m-3)
noncomputable def forbiddenMass {m : ℕ} (t : PathTuple m) (p : ℝ) : ℝ :=
  ∑ s ∈ pathForbidden t, columnMass m p s

theorem pathLeft_card_probability {m : ℕ} (t : PathTuple m) : (pathLeft t).card = 3 := by
  simp [pathLeft, t.injective.eq_iff]

theorem pathMiddle_card_probability {m : ℕ} (t : PathTuple m) : (pathMiddle t).card = 3 := by
  simp [pathMiddle, t.injective.eq_iff]

theorem pathRight_card_probability {m : ℕ} (t : PathTuple m) : (pathRight t).card = 3 := by
  simp [pathRight, t.injective.eq_iff]

theorem path_supports_distinct {m : ℕ} (t : PathTuple m) :
    pathLeft t ≠ pathMiddle t ∧ pathLeft t ≠ pathRight t ∧
      pathMiddle t ≠ pathRight t := by
  constructor
  · intro he
    have h : t 0 ∈ pathMiddle t := he ▸ (by simp [pathLeft])
    simpa [pathMiddle, t.injective.eq_iff] using h
  constructor
  · intro he
    have h : t 0 ∈ pathRight t := he ▸ (by simp [pathLeft])
    simpa [pathRight, t.injective.eq_iff] using h
  · intro he
    have h : t 2 ∈ pathRight t := he ▸ (by simp [pathMiddle])
    simpa [pathRight, t.injective.eq_iff] using h

theorem path_supports_forbidden {m : ℕ} (t : PathTuple m) :
    pathLeft t ∈ pathForbidden t ∧ pathMiddle t ∈ pathForbidden t ∧
      pathRight t ∈ pathForbidden t := by
  have hrow (i : Fin 7) : t i ∈ pathRows t := by simp [pathRows]
  simp only [pathForbidden, mem_filter, mem_univ, true_and,
    pathLeft_card_probability, pathMiddle_card_probability, pathRight_card_probability, le_refl, true_and]
  refine ⟨?_,?_,?_⟩
  · exact Finset.not_disjoint_iff.mpr ⟨t 0, by simp [pathLeft], hrow 0⟩
  · exact Finset.not_disjoint_iff.mpr ⟨t 2, by simp [pathMiddle], hrow 2⟩
  · exact Finset.not_disjoint_iff.mpr ⟨t 4, by simp [pathRight], hrow 4⟩

/-- Exact fixed-path probability on the actual matrix iid law. -/
theorem path_probability {m n : ℕ} (t : PathTuple m) (p : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (hn : 3 ≤ n) :
    matrixProb m n p (fun A => pathOccurs A t) =
      ((n * (n-1) * (n-2) : ℕ) : ℝ) / 3 * (pathQ m p)^3 *
        (1 - forbiddenMass t p)^(n-3) := by
  have hf := path_supports_forbidden t
  have hd := path_supports_distinct t
  have h := exactlyOnce_identity (Finset (Fin m)) (columnMass m p)
    (columnMass_nonneg m p hp hp') (columnMass_sum m p) (pathForbidden t)
    (pathLeft t) (pathMiddle t) (pathRight t) hf.1 hf.2.1 hf.2.2
    hd.1 hd.2.1 hd.2.2 n hn
  change iidProb (columnMass m p) n
    (exactlyOnceMiddleFirst (pathForbidden t) (pathLeft t) (pathMiddle t) (pathRight t)) = _
  rw [h, columnMass_by_card, columnMass_by_card, columnMass_by_card,
    pathLeft_card_probability, pathMiddle_card_probability, pathRight_card_probability]
  unfold pathQ forbiddenMass
  ring

theorem sum_finset_prod_ite {ι : Type} [Fintype ι] [DecidableEq ι]
    (f g : ι → ℝ) :
    (∑ s : Finset ι, ∏ i, if i ∈ s then f i else g i) = ∏ i, (f i + g i) := by
  have h := Finset.prod_add f g univ
  simp only [Finset.powerset_univ] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.prod_ite]
  have hset : univ.filter (fun x : ι => x ∉ s) = univ \ s := by ext i; simp
  simp [hset]

/-- Exact Bernoulli inclusion probability, with all other entries summed out. -/
theorem columnMass_superset (m : ℕ) (p : ℝ) (r : Finset (Fin m)) :
    (∑ s : Finset (Fin m), if r ⊆ s then columnMass m p s else 0) = p^r.card := by
  classical
  calc
    _ = ∑ s : Finset (Fin m), ∏ i : Fin m,
        if i ∈ s then p else if i ∈ r then 0 else 1-p := by
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hr : r ⊆ s
      · rw [if_pos hr]
        apply Finset.prod_congr rfl
        intro i hi
        by_cases his : i ∈ s <;> by_cases hir : i ∈ r <;> simp_all
        exact False.elim (his (hr hir))
      · rw [if_neg hr]
        obtain ⟨i, hir, his⟩ := Finset.not_subset.mp hr
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [his, hir]
    _ = ∏ i : Fin m, (p + if i ∈ r then 0 else 1-p) :=
      sum_finset_prod_ite _ _
    _ = ∏ i : Fin m, if i ∈ r then p else 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      split_ifs <;> ring
    _ = p^r.card := by simp [Finset.prod_ite]

theorem finite_event_union_bound {α β : Type} [Fintype α] [DecidableEq β]
    (μ : α → ℝ) (hμ : ∀ a, 0 ≤ μ a) (E : α → Prop) (T : Finset β)
    (C : β → α → Prop) [DecidablePred E] [∀ t, DecidablePred (C t)]
    (hcover : ∀ a, E a → ∃ t ∈ T, C t a) :
    (∑ a, if E a then μ a else 0) ≤ ∑ t ∈ T, ∑ a, if C t a then μ a else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a ha
  have hnon (t : β) : 0 ≤ if C t a then μ a else 0 := by split_ifs <;> simp_all
  by_cases he : E a
  · obtain ⟨t,ht,hc⟩ := hcover a he
    simpa [he, hc] using Finset.single_le_sum (fun z hz => hnon z) ht
  · simpa [he] using Finset.sum_nonneg (fun z hz => hnon z)

theorem columnMass_large_containing_bound (m : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hp' : p ≤ 1) (r : Fin m) :
    (∑ s : Finset (Fin m), if 3 ≤ s.card ∧ r ∈ s then columnMass m p s else 0) ≤
      ((m-1).choose 2 : ℝ) * p^3 := by
  classical
  let T := (univ.erase r).powersetCard 2
  calc
    _ ≤ ∑ u ∈ T, ∑ s : Finset (Fin m), if insert r u ⊆ s then columnMass m p s else 0 := by
      apply finite_event_union_bound (columnMass m p) (columnMass_nonneg m p hp hp')
        (fun s => 3 ≤ s.card ∧ r ∈ s) T (fun u s => insert r u ⊆ s)
      intro s hs
      have hcard : 2 ≤ (s.erase r).card := by
        rw [Finset.card_erase_of_mem hs.2]
        omega
      obtain ⟨u, hus, huc⟩ := Finset.exists_subset_card_eq hcard
      refine ⟨u, ?_, ?_⟩
      · apply Finset.mem_powersetCard.mpr
        exact ⟨fun i hi => by simpa using (Finset.mem_erase.mp (hus hi)).1, huc⟩
      · exact Finset.insert_subset hs.2 (hus.trans (Finset.erase_subset _ _))
    _ = ∑ u ∈ T, p^3 := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [columnMass_superset]
      have hu' := Finset.mem_powersetCard.mp hu
      have hru : r ∉ u := fun hr => (Finset.mem_erase.mp (hu'.1 hr)).1 rfl
      rw [Finset.card_insert_of_not_mem hru, hu'.2]
    _ = _ := by
      simp [T, Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ r),
        nsmul_eq_mul]

theorem pathRows_card_probability {m : ℕ} (t : PathTuple m) : (pathRows t).card = 7 := by
  rw [pathRows, Finset.card_image_of_injective _ t.injective]
  simp

/-- The exact forbidden-mass bound. -/
theorem forbiddenMass_le {m : ℕ} (t : PathTuple m) (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    forbiddenMass t p ≤ 7 * ((m-1).choose 2 : ℝ) * p^3 := by
  classical
  have he : forbiddenMass t p =
      ∑ s : Finset (Fin m), if s ∈ pathForbidden t then columnMass m p s else 0 := by
    simp [forbiddenMass, ← Finset.sum_filter]
  rw [he]
  calc
    _ ≤ ∑ r ∈ pathRows t, ∑ s : Finset (Fin m),
        if 3 ≤ s.card ∧ r ∈ s then columnMass m p s else 0 := by
      apply finite_event_union_bound (columnMass m p) (columnMass_nonneg m p hp hp')
        (fun s => s ∈ pathForbidden t) (pathRows t) (fun r s => 3 ≤ s.card ∧ r ∈ s)
      intro s hs
      have hs' := (Finset.mem_filter.mp hs).2
      obtain ⟨r,hrs,hrr⟩ := Finset.not_disjoint_iff.mp hs'.2
      exact ⟨r,hrr,hs'.1,hrs⟩
    _ ≤ ∑ r ∈ pathRows t, ((m-1).choose 2 : ℝ) * p^3 := by
      apply Finset.sum_le_sum
      intro r hr
      exact columnMass_large_containing_bound m p hp hp' r
    _ = _ := by simp [pathRows_card_probability, nsmul_eq_mul]; ring

theorem iidProb_mono {α : Type} [Fintype α] (μ : α → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (n : ℕ) {E H : (Fin n → α) → Prop}
    (h : ∀ a, E a → H a) : iidProb μ n E ≤ iidProb μ n H := by
  classical
  unfold iidProb
  apply Finset.sum_le_sum
  intro a ha
  by_cases he : E a
  · simp [he, h a he]
  · simp only [he, if_false]
    split_ifs
    · exact iidMass_nonneg μ hμ a
    · rfl

theorem matrixProb_mono (m n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    {E H : Matrix m n → Prop} (h : ∀ A, E A → H A) :
    matrixProb m n p E ≤ matrixProb m n p H :=
  iidProb_mono _ (columnMass_nonneg m p hp hp') n h

theorem iidProb_forall {α : Type} [Fintype α] (μ : α → ℝ) (n : ℕ)
    (C : Fin n → α → Prop) [∀ i, DecidablePred (C i)] :
    iidProb μ n (fun a => ∀ i, C i (a i)) =
      ∏ i, ∑ x, if C i x then μ x else 0 := by
  classical
  unfold iidProb
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hc : ∀ i, C i (a i)
  · rw [if_pos hc]
    unfold iidMass
    apply Finset.prod_congr rfl
    intro i hi
    simp [hc i, iidMass]
  · rw [if_neg hc]
    push_neg at hc
    obtain ⟨i,hi⟩ := hc
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem iidProb_all {α : Type} [Fintype α] (μ : α → ℝ) (n : ℕ)
    (C : α → Prop) [DecidablePred C] :
    iidProb μ n (fun a => ∀ i, C (a i)) =
      (∑ x, if C x then μ x else 0)^n := by
  rw [iidProb_forall]
  simp

theorem iidProb_coordinate {α : Type} [Fintype α] (μ : α → ℝ)
    (hnorm : ∑ x, μ x = 1) {n : ℕ} (j : Fin n) (C : α → Prop) [DecidablePred C] :
    iidProb μ n (fun a => C (a j)) = ∑ x, if C x then μ x else 0 := by
  classical
  calc
    _ = iidProb μ n (fun a => ∀ i, i = j → C (a i)) := by
      apply iidProb_congr
      simp
    _ = ∏ i : Fin n, ∑ x, if i = j → C x then μ x else 0 := iidProb_forall μ n (fun i x => i = j → C x)
    _ = ∏ i : Fin n, if i = j then (∑ x, if C x then μ x else 0) else 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases h : i = j <;> simp [h, hnorm]
    _ = _ := by simp

theorem iidProb_union_bound {α β : Type} [Fintype α] [DecidableEq β]
    (μ : α → ℝ) (hμ : ∀ a, 0 ≤ μ a) (n : ℕ)
    (E : (Fin n → α) → Prop) (T : Finset β)
    (C : β → (Fin n → α) → Prop)
    (hcover : ∀ a, E a → ∃ t ∈ T, C t a) :
    iidProb μ n E ≤ ∑ t ∈ T, iidProb μ n (C t) := by
  classical
  exact finite_event_union_bound (iidMass μ) (iidMass_nonneg μ hμ) E T C hcover

theorem columnMass_card_ge_bound (m d : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (∑ s : Finset (Fin m), if d ≤ s.card then columnMass m p s else 0) ≤
      (m.choose d : ℝ) * p^d := by
  classical
  calc
    _ ≤ ∑ u ∈ (univ : Finset (Fin m)).powersetCard d,
        ∑ s : Finset (Fin m), if u ⊆ s then columnMass m p s else 0 := by
      apply finite_event_union_bound (columnMass m p) (columnMass_nonneg m p hp hp')
        (fun s => d ≤ s.card) (univ.powersetCard d) (fun u s => u ⊆ s)
      intro s hs
      obtain ⟨u, hus, huc⟩ := Finset.exists_subset_card_eq hs
      exact ⟨u, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, huc⟩, hus⟩
    _ = ∑ u ∈ (univ : Finset (Fin m)).powersetCard d, p^d := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [columnMass_superset, (Finset.mem_powersetCard.mp hu).2]
    _ = _ := by simp [Finset.card_powersetCard, nsmul_eq_mul]

/-- Probability of any actual column of size at least four. -/
theorem noLargeColumns_failure_bound (m n : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1) :
    matrixProb m n p (fun A => ¬ noLargeColumns A) ≤
      (n : ℝ) * (m.choose 4 : ℝ) * p^4 := by
  classical
  calc
    _ ≤ ∑ j : Fin n, matrixProb m n p (fun A => 4 ≤ (A j).card) := by
      apply iidProb_union_bound (columnMass m p) (columnMass_nonneg m p hp hp') n
        (fun A => ¬ noLargeColumns A) univ (fun j A => 4 ≤ (A j).card)
      intro A hA
      simp only [noLargeColumns, not_forall] at hA
      obtain ⟨j,hj⟩ := hA
      exact ⟨j, mem_univ j, by omega⟩
    _ ≤ ∑ j : Fin n, (m.choose 4 : ℝ) * p^4 := by
      apply Finset.sum_le_sum
      intro j hj
      rw [matrixProb, iidProb_coordinate (columnMass m p) (columnMass_sum m p) j
        (fun s => 4 ≤ s.card)]
      exact columnMass_card_ge_bound m 4 p hp hp'
    _ = _ := by simp [nsmul_eq_mul]; ring

theorem iidProb_avoid {α : Type} [Fintype α] [DecidableEq α] (μ : α → ℝ)
    (hnorm : ∑ x, μ x = 1) (n : ℕ) (r : α) :
    iidProb μ n (fun a => ∀ j, a j ≠ r) = (1 - μ r)^n := by
  classical
  rw [iidProb_all μ n (fun s => s ≠ r)]
  have h := outsideMass μ ({r} : Finset α) hnorm
  simpa using congrArg (fun x : ℝ => x^n) h

/-- An exact two-row support is absent with its exact iid probability. -/
theorem exactPair_absence_probability {m n : ℕ} (p : ℝ) (s : Finset (Fin m))
    (hs : s.card = 2) :
    matrixProb m n p (fun A => ∀ j, A j ≠ s) =
      (1 - p^2 * (1-p)^(m-2))^n := by
  rw [matrixProb, iidProb_avoid _ (columnMass_sum m p), columnMass_by_card, hs]

/-- Union over the actual unordered row pairs, retaining the choose(m,2) factor. -/
theorem allExactPairs_failure_bound (m n : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1) :
    matrixProb m n p (fun A => ¬ allExactPairs A) ≤
      (m.choose 2 : ℝ) * (1 - p^2 * (1-p)^(m-2))^n := by
  classical
  calc
    _ ≤ ∑ s ∈ (univ : Finset (Fin m)).powersetCard 2,
        matrixProb m n p (fun A => ∀ j, A j ≠ s) := by
      apply iidProb_union_bound (columnMass m p) (columnMass_nonneg m p hp hp') n
        (fun A => ¬ allExactPairs A) (univ.powersetCard 2) (fun s A => ∀ j, A j ≠ s)
      intro A hA
      simp only [allExactPairs, not_forall, not_exists, _root_.not_imp] at hA
      obtain ⟨i,j,hij,h⟩ := hA
      refine ⟨{i,j}, ?_, h⟩
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by simp [hij]⟩
    _ = ∑ _s ∈ (univ : Finset (Fin m)).powersetCard 2,
        (1 - p^2 * (1-p)^(m-2))^n := by
      apply Finset.sum_congr rfl
      intro s hs
      exact exactPair_absence_probability p s (Finset.mem_powersetCard.mp hs).2
    _ = _ := by simp [Finset.card_powersetCard, nsmul_eq_mul]

end ADG
