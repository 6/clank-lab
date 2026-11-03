import OrderedPhase
import UniformInvariance
import Mathlib.Data.List.NodupEquivFin

/-! Joint transport of matrix and ordering under column relabelling. -/
namespace ADG.Uniform
open Finset
open scoped Classical

lemma prune_relabel {m n : ℕ} (A : Matrix m n) (π : Equiv.Perm (Fin n))
    (j : Fin n) (S : Finset (Fin n)) :
    (Conflict.prune (conflict (relabel A π)) j S).image π =
      Conflict.prune (conflict A) (π j) (S.image π) := by
  ext v
  simp only [mem_image, Conflict.prune, mem_filter, conflict, relabel]
  constructor
  · rintro ⟨w, ⟨hw, hwj, hd⟩, rfl⟩
    exact ⟨⟨w, hw, rfl⟩, fun h => hwj (π.injective h), hd⟩
  · rintro ⟨⟨w, hw, rfl⟩, hwj, hd⟩
    exact ⟨w, ⟨hw, fun h => hwj (congrArg π h), hd⟩, rfl⟩

lemma scanList_relabel {m n : ℕ} (A : Matrix m n) (π : Equiv.Perm (Fin n))
    (l : List (Fin n)) (S : Finset (Fin n)) :
    Conflict.scanList (conflict A) (l.map π) (S.image π) =
      (Conflict.scanList (conflict (relabel A π)) l S).image π := by
  induction l generalizing S with
  | nil => simp [Conflict.scanList]
  | cons v l ih =>
    by_cases hv : v ∈ S
    · have hv' : π v ∈ S.image π := mem_image.mpr ⟨v, hv, rfl⟩
      simp only [List.map_cons, Conflict.scanList, if_pos hv, if_pos hv', image_insert]
      rw [← prune_relabel, ih]
    · have hv' : π v ∉ S.image π := by
        rintro hh
        obtain ⟨w, hw, he⟩ := mem_image.mp hh
        exact hv ((π.injective he) ▸ hw)
      simp only [List.map_cons, Conflict.scanList, if_neg hv, if_neg hv']
      exact ih S

lemma triples_relabel_image {m n : ℕ} (A : Matrix m n) (π : Equiv.Perm (Fin n))
    (U : Finset (Fin m)) : (triples (relabel A π) U).image π = triples A U := by
  ext j
  simp only [mem_image, mem_triples, relabel]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact hv
  · intro hj; exact ⟨π.symm j, by simpa using hj, by simp⟩

lemma phasePayoff_relabel {m n : ℕ} (A : Matrix m n) (π : Equiv.Perm (Fin n))
    (U : Finset (Fin m)) (event : ℕ → Prop) (T : Finset (Fin n)) :
    phasePayoff A U event (T.image π) = phasePayoff (relabel A π) U event T := by
  have hc : (T.image π).card = T.card := card_image_of_injective T π.injective
  have hu : (T.image π).biUnion A = T.biUnion (relabel A π) := by
    ext i
    simp only [mem_biUnion, mem_image, relabel]
    constructor
    · rintro ⟨j, ⟨t, ht, rfl⟩, hi⟩; exact ⟨t, ht, hi⟩
    · rintro ⟨t, ht, hi⟩; exact ⟨π t, ⟨t, ht, rfl⟩, hi⟩
  simp only [phasePayoff, hc, hu]

lemma ordered_payoff_relabel {m n : ℕ} (A : Matrix m n) (π : Equiv.Perm (Fin n))
    (hf : feasible A) (hn : noLargeColumns A) (hp : allExactPairs A)
    (event : ℕ → Prop) :
    phasePayoff A univ event
      (Conflict.scanList (conflict A) ((List.finRange n).map π) (triples A univ)) =
      if event (G (relabel A π)) then 1 else 0 := by
  rw [← triples_relabel_image A π univ, scanList_relabel, phasePayoff_relabel]
  have h := original_count_phase (relabel A π) ((feasible_relabel A π).mpr hf)
    ((noLarge_relabel A π).mpr hn) ((allPairs_relabel A π).mpr hp) m univ
    (by simp)
  change _ = if event ((trace (relabel A π) m univ).length) then 1 else 0
  rw [h]
  rfl

lemma order_is_relabel {n : ℕ} (l : List (Fin n)) (hl : l ∈ Conflict.orders univ) :
    ∃ π : Equiv.Perm (Fin n), l = (List.finRange n).map π := by
  obtain ⟨hn, hs⟩ := (Conflict.mem_orders _ _).mp hl
  have hlen : l.length = n := by
    have hc := congrArg Finset.card hs
    simpa only [List.toFinset_card_of_nodup hn, card_univ, Fintype.card_fin] using hc
  have hall : ∀ j : Fin n, j ∈ l := by intro j; simpa only [← List.mem_toFinset, hs] using mem_univ j
  let π : Equiv.Perm (Fin n) := (finCongr hlen.symm).trans
    (hn.getEquivOfForallMemList l hall)
  refine ⟨π, ?_⟩
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi hj
    simp [π, Equiv.trans_apply, List.getElem_map, List.getElem_finRange]

end ADG.Uniform
