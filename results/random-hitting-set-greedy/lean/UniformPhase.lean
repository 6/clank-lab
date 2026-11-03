import UniformEndpoint
import ConflictCoupling
import Greedy

/-! From the uniform kernel to the triple conflict process. -/
namespace ADG.Uniform
open Finset
open scoped Classical

noncomputable def triples {m n : ℕ} (A : Matrix m n) (U : Finset (Fin m)) :
    Finset (Fin n) := univ.filter (fun j => (A j).card = 3 ∧ A j ⊆ U)

def conflict {m n : ℕ} (A : Matrix m n) (i j : Fin n) : Prop :=
  ¬ Disjoint (A i) (A j)

lemma mem_maximizers {m n : ℕ} (A : Matrix m n) (U : Finset (Fin m)) (j : Fin n) :
    j ∈ maximizers A U ↔ 0 < gain A U j ∧ ∀ t, gain A U t ≤ gain A U j := by
  simp [maximizers]

lemma mem_triples {m n : ℕ} (A : Matrix m n) (U : Finset (Fin m)) (j : Fin n) :
    j ∈ triples A U ↔ (A j).card = 3 ∧ A j ⊆ U := by simp [triples]

lemma triples_gain {m n : ℕ} (A : Matrix m n) (U : Finset (Fin m))
    (hn : noLargeColumns A) (j : Fin n) :
    j ∈ triples A U ↔ gain A U j = 3 := by
  rw [mem_triples]
  constructor
  · rintro ⟨hc, hs⟩
    simp [gain, inter_eq_right.mpr hs, hc]
  · intro hg
    have hcard : (A j).card = 3 := by have := gain_le_column A U j; have := hn j; omega
    refine ⟨hcard, ?_⟩
    apply inter_eq_right.mp
    apply eq_of_subset_of_card_le inter_subset_right
    simp only [gain] at hg
    omega

lemma triples_mono {m n : ℕ} (A : Matrix m n) {U V : Finset (Fin m)} (hUV : U ⊆ V) :
    triples A U ⊆ triples A V := by
  intro j hj
  rw [mem_triples] at hj ⊢
  exact ⟨hj.1, hj.2.trans hUV⟩

lemma maximizers_eq_triples {m n : ℕ} (A : Matrix m n) (U : Finset (Fin m))
    (hn : noLargeColumns A) (ht : (triples A U).Nonempty) :
    maximizers A U = triples A U := by
  obtain ⟨v, hv⟩ := ht
  have hv3 := (triples_gain A U hn v).mp hv
  ext j
  rw [mem_maximizers, triples_gain A U hn]
  constructor
  · rintro ⟨_, hmax⟩
    have := hmax v
    have := (gain_le_column A U j).trans (hn j)
    omega
  · intro hj
    refine ⟨by omega, fun t => ?_⟩
    rw [hj]
    exact (gain_le_column A U t).trans (hn t)

lemma triples_prune {m n : ℕ} (A : Matrix m n) (U : Finset (Fin m))
    (j : Fin n) (_hj : j ∈ triples A U) :
    triples A (U \ A j) = Conflict.prune (conflict A) j (triples A U) := by
  ext v
  simp only [mem_triples, Conflict.prune, mem_filter, conflict, not_not]
  constructor
  · rintro ⟨hc, hs⟩
    refine ⟨⟨hc, hs.trans sdiff_subset⟩, ?_, ?_⟩
    · intro he
      subst v
      have hz : A j = ∅ := subset_empty.mp (by
        intro x hx
        exact False.elim ((mem_sdiff.mp (hs hx)).2 hx))
      rw [hz] at hc
      simp at hc
    · exact (disjoint_left.mpr (fun x hxj hxv => (mem_sdiff.mp (hs hxv)).2 hxj))
  · rintro ⟨⟨hc, hs⟩, _, hd⟩
    exact ⟨hc, subset_sdiff.mpr ⟨hs, hd.symm⟩⟩

lemma maximizers_nonempty {m n : ℕ} (A : Matrix m n) (hf : feasible A)
    (U : Finset (Fin m)) (hu : U ≠ ∅) : (maximizers A U).Nonempty := by
  obtain ⟨j, hb, hp⟩ := best_exists_positive A hf U hu
  exact ⟨j, (mem_maximizers A U j).mpr ⟨hp,
    fun t => (best_mem_max A U _ j hb).2 t (List.mem_finRange t)⟩⟩

lemma maximal_low_gain {m n : ℕ} (A : Matrix m n) (hp : allExactPairs A)
    (hn : noLargeColumns A) (U : Finset (Fin m)) (ht : triples A U = ∅)
    (j : Fin n) (hj : j ∈ maximizers A U) :
    gain A U j = min 2 U.card := by
  obtain ⟨hpos, hmax⟩ := (mem_maximizers A U j).mp hj
  have hle3 := (gain_le_column A U j).trans (hn j)
  have hne3 : gain A U j ≠ 3 := by
    intro he
    have := (triples_gain A U hn j).mpr he
    simpa [ht] using this
  have hleU := gain_le_card A U j
  by_cases htwo : 2 ≤ U.card
  · obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp htwo
    obtain ⟨t, ht⟩ := hp a b hab
    have hsub : ({a,b} : Finset (Fin m)) ⊆ U := by simp [insert_subset_iff, ha, hb]
    have htwo' : gain A U t = 2 := by simp [gain, ht, inter_eq_right.mpr hsub, hab]
    have := hmax t
    rw [htwo'] at this
    rw [min_eq_left htwo]
    omega
  · rw [min_eq_right (by omega : U.card ≤ 2)]
    omega

noncomputable def phasePayoff {m n : ℕ} (A : Matrix m n) (U : Finset (Fin m))
    (event : ℕ → Prop) (T : Finset (Fin n)) : ℝ :=
  if event (T.card + ((U \ T.biUnion A).card + 1)/2) then 1 else 0

/-- All later fresh ties are retained in countProb. On the good event their
only effect on the count is through the accepted labelled triple set. -/
theorem countProb_phase {m n : ℕ} (A : Matrix m n) (hf : feasible A)
    (hn : noLargeColumns A) (hp : allExactPairs A) (fuel : ℕ)
    (U : Finset (Fin m)) (hfu : U.card ≤ fuel) (event : ℕ → Prop) :
    countProb A fuel U event =
      Conflict.choose (conflict A) (triples A U) (phasePayoff A U event) := by
  induction fuel generalizing U event with
  | zero =>
    have hU : U = ∅ := card_eq_zero.mp (by omega)
    have ht : triples A U = ∅ := by
      apply eq_empty_iff_forall_not_mem.mpr
      intro j hj
      obtain ⟨hc, hs⟩ := (mem_triples A U j).mp hj
      rw [hU] at hs
      have := subset_empty.mp hs
      simp [this] at hc
    rw [ht, Conflict.choose.eq_def, dif_pos rfl]
    simp [countProb, phasePayoff, hU]
  | succ fuel ih =>
    by_cases hU : U = ∅
    · have ht : triples A U = ∅ := by
        apply eq_empty_iff_forall_not_mem.mpr
        intro j hj
        obtain ⟨hc, hs⟩ := (mem_triples A U j).mp hj
        rw [hU] at hs
        have := subset_empty.mp hs
        simp [this] at hc
      have hJ : maximizers A U = ∅ := by simp [maximizers, gain, hU]
      rw [ht, Conflict.choose.eq_def, dif_pos rfl]
      simp only [countProb, hJ, if_pos rfl]
      simp [phasePayoff, hU]
    have hJ := maximizers_nonempty A hf U hU
    rw [countProb, if_neg (nonempty_iff_ne_empty.mp hJ)]
    by_cases ht : triples A U = ∅
    · rw [ht, Conflict.choose.eq_def, dif_pos rfl]
      simp only [phasePayoff, card_empty, biUnion_empty, sdiff_empty, zero_add]
      have hterm (j : Fin n) (hj : j ∈ maximizers A U) :
          countProb A fuel (U \ A j) (fun g => event (g+1)) =
            if event ((U.card+1)/2) then (1 : ℝ) else 0 := by
        have hg := maximal_low_gain A hp hn U ht j hj
        have hmass := card_sdiff_add_card_inter U (A j)
        change (U \ A j).card + gain A U j = U.card at hmass
        have hpos := ((mem_maximizers A U j).mp hj).1
        have hres : (U \ A j).card ≤ fuel := by omega
        have htc : triples A (U \ A j) = ∅ := subset_empty.mp (by
          simpa [ht] using (triples_mono A (sdiff_subset : U \ A j ⊆ U)))
        rw [ih _ hres, htc, Conflict.choose.eq_def, dif_pos rfl]
        simp only [phasePayoff, card_empty, biUnion_empty, sdiff_empty, zero_add]
        have heq : ((U \ A j).card + 1)/2 + 1 = (U.card+1)/2 := by omega
        rw [heq]
      rw [sum_congr rfl hterm]
      simp only [sum_const, nsmul_eq_mul]
      exact mul_div_cancel_left₀ _ (by exact_mod_cast card_ne_zero.mpr hJ)
    · have hT := nonempty_iff_ne_empty.mpr ht
      rw [maximizers_eq_triples A U hn hT, Conflict.choose.eq_def, dif_neg ht]
      rw [Finset.sum_coe_sort (triples A U) (fun j =>
        Conflict.choose (conflict A) (Conflict.prune (conflict A) j (triples A U))
          (fun T => phasePayoff A U event (insert j T)))]
      congr 1
      apply sum_congr rfl
      intro j hj
      have hg := (triples_gain A U hn j).mp hj
      have hmass := card_sdiff_add_card_inter U (A j)
      change (U \ A j).card + gain A U j = U.card at hmass
      have hres : (U \ A j).card ≤ fuel := by omega
      rw [ih _ hres, triples_prune A U j hj]
      apply Conflict.choose_congr
      intro T hT
      have hjT : j ∉ T := by
        intro hjT
        have := Conflict.prune_subset (conflict A) j (triples A U) (hT hjT)
        simp at this
      have hsd : (U \ A j) \ T.biUnion A = U \ (insert j T).biUnion A := by
        ext x
        simp only [mem_sdiff, mem_biUnion, mem_insert]
        constructor <;> intro h <;> aesop
      simp only [phasePayoff, card_insert_of_not_mem hjT, hsd]
      have heq : T.card + ((U \ (insert j T).biUnion A).card + 1)/2 + 1 =
          (T.card+1) + ((U \ (insert j T).biUnion A).card + 1)/2 := by omega
      rw [heq]


end ADG.Uniform
