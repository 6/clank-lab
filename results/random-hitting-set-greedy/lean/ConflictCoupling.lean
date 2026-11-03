import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-! General labelled conflict-graph processes.
The payoff on the accepted set is arbitrary: equality for all payoffs entails
equality of full accepted-set laws, not merely equality of expectations of size. -/
namespace ADG.Uniform.Conflict
open Finset
variable {α : Type} [DecidableEq α]

def prune (adj : α → α → Prop) [DecidableRel adj] (v : α) (S : Finset α) : Finset α :=
  S.filter (fun w => w ≠ v ∧ ¬ adj v w)

lemma prune_subset (adj : α → α → Prop) [DecidableRel adj] (v : α) (S : Finset α) :
    prune adj v S ⊆ S.erase v := by
  intro w hw
  obtain ⟨hw, hne, _⟩ := mem_filter.mp hw
  exact mem_erase.mpr ⟨hne, hw⟩

lemma prune_card_lt (adj : α → α → Prop) [DecidableRel adj] (v : α)
    (S : Finset α) (hv : v ∈ S) : (prune adj v S).card < S.card :=
  (card_le_card (prune_subset adj v S)).trans_lt (card_erase_lt_of_mem hv)

/-- Each call chooses uniformly from the CURRENT eligible labelled vertices. -/
noncomputable def choose (adj : α → α → Prop) [DecidableRel adj]
    (S : Finset α) (payoff : Finset α → ℝ) : ℝ :=
  if h : S = ∅ then payoff ∅
  else (∑ v : S, choose adj (prune adj v S) (fun T => payoff (insert (v : α) T))) / S.card
termination_by S.card
decreasing_by exact prune_card_lt adj _ _ (Subtype.mem _)

/-- Generate a permutation by repeatedly drawing uniformly without replacement.
Blocked vertices are scanned and skipped; only eligible draws are accepted. -/
noncomputable def scan (adj : α → α → Prop) [DecidableRel adj]
    (R S : Finset α) (payoff : Finset α → ℝ) : ℝ :=
  if h : R = ∅ then payoff ∅
  else (∑ v : R,
    if (v : α) ∈ S then
      scan adj (R.erase v) (prune adj v S) (fun T => payoff (insert (v : α) T))
    else scan adj (R.erase v) S payoff) / R.card
termination_by R.card
decreasing_by all_goals exact card_erase_lt_of_mem (Subtype.mem _)

/-- Only subsets of the initially eligible labels can be returned. -/
theorem choose_congr (adj : α → α → Prop) [DecidableRel adj]
    (S : Finset α) (f g : Finset α → ℝ) (h : ∀ T ⊆ S, f T = g T) :
    choose adj S f = choose adj S g := by
  classical
  induction S using Finset.strongInduction generalizing f g with
  | H S ih =>
    rw [choose.eq_def, choose.eq_def]
    split_ifs with hS
    · exact h ∅ (empty_subset S)
    · congr 1
      apply sum_congr rfl
      intro v _
      apply ih _ (Finset.ssubset_iff_subset_ne.mpr ⟨
        ((prune_subset adj v S).trans (erase_subset _ _)),
        by intro he; have := prune_card_lt adj v S v.property; rw [he] at this; omega⟩)
      intro T hT
      apply h
      exact insert_subset v.property (hT.trans ((prune_subset adj v S).trans (erase_subset _ _)))

private lemma average_extend (R S : Finset α) (hSR : S ⊆ R)
    (f : α → ℝ) (a : ℝ) (hf : (∑ v ∈ S, f v) = S.card * a) :
    (∑ v : R, if (v : α) ∈ S then f v else a) = R.card * a := by
  rw [Finset.sum_coe_sort R (fun v => if v ∈ S then f v else a)]
  have hz : (∑ v ∈ R, if v ∈ S then f v - a else 0) = 0 := by
    rw [sum_ite_mem, inter_eq_right.mpr hSR, sum_sub_distrib,
      sum_const, nsmul_eq_mul, hf, sub_self]
  have heq : (∑ v ∈ R, if v ∈ S then f v else a) =
      (∑ v ∈ R, if v ∈ S then f v - a else 0) + R.card * a := by
    have hconst : (∑ _v ∈ R, a) = R.card * a := by simp
    rw [← hconst, ← sum_add_distrib]
    apply sum_congr rfl
    intro v hv
    split_ifs <;> ring
  rw [heq, hz, zero_add]

/-- Equality for arbitrary accepted-set payoffs, for every finite labelled
conflict relation. No exchangeability assumption is a premise. -/
theorem scan_eq_choose (adj : α → α → Prop) [DecidableRel adj]
    (R S : Finset α) (hSR : S ⊆ R) (payoff : Finset α → ℝ) :
    scan adj R S payoff = choose adj S payoff := by
  classical
  induction R using Finset.strongInduction generalizing S payoff with
  | H R ih =>
    by_cases hR : R = ∅
    · have hS : S = ∅ := subset_empty.mp (hR ▸ hSR)
      simp [scan, choose, hR, hS]
    rw [scan, dif_neg hR]
    have hterms :
        (∑ v : R, if (v : α) ∈ S then
          scan adj (R.erase v) (prune adj v S) (fun T => payoff (insert (v : α) T))
        else scan adj (R.erase v) S payoff) =
        ∑ v : R, if (v : α) ∈ S then
          choose adj (prune adj v S) (fun T => payoff (insert (v : α) T))
        else choose adj S payoff := by
      apply sum_congr rfl
      intro v _
      have hlt : R.erase (v : α) ⊂ R := erase_ssubset v.property
      split_ifs with hv
      · apply ih _ hlt
        intro w hw
        obtain ⟨hne, hwS⟩ := mem_erase.mp (prune_subset adj v S hw)
        exact mem_erase.mpr ⟨hne, hSR hwS⟩
      · apply ih _ hlt
        intro w hw
        exact mem_erase.mpr ⟨by rintro rfl; exact hv hw, hSR hw⟩
    rw [hterms]
    have hsum : (∑ v ∈ S, choose adj (prune adj v S)
        (fun T => payoff (insert v T))) = S.card * choose adj S payoff := by
      by_cases hS : S = ∅
      · simp [hS]
      · rw [choose.eq_def adj S payoff, dif_neg hS]
        rw [Finset.sum_coe_sort S (fun v => choose adj (prune adj v S)
          (fun T => payoff (insert v T)))]
        have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hS)
        field_simp
    rw [average_extend R S hSR _ _ hsum]
    exact mul_div_cancel_left₀ _ (by exact_mod_cast card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hR))

end ADG.Uniform.Conflict
