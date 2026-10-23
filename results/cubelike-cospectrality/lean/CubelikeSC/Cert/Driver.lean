import CubelikeSC.Cert.Sound

/-!
# From per-key checks to Lemma F

A case's key is its coset `0` followed by its other seven cosets sorted by
`(μ_u, r_u)`, which is a permutation of its cosets. `lemmaF_of_certs`: if every
certificate entry passes `Entry.check`, and every case `(n, B, t)` finds an
entry for `n` whose cosets equal its key, Lemma F holds.
-/

namespace CubelikeSC.Cert

open CubelikeSC

lemma caseKey_perm (n : ℕ) (B : Finset (Fin 8)) (t : Fin 8) :
    (caseKey n B t).Perm (allU.map (caseCoset n B t)) :=
  List.Perm.cons _ (List.perm_insertionSort _ _)

theorem lemmaF_of_certs (certs : ℕ → List Entry)
    (hc : ∀ n < 128, (certs n).all Entry.check = true)
    (hd : ∀ B : Finset (Fin 8), (0 : Fin 8) ∉ B → ∀ t : Fin 8, ∀ n < 128, B.card ≤ n →
      covered certs n B t = true) : LemmaF := by
  intro n hn B hB0 hBn t α β hadm
  have hn' : n < 128 := by norm_num at hn; exact hn
  have := hd B hB0 t n hn' hBn
  simp only [covered, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at this
  obtain ⟨e, he, hen, hek⟩ := this
  have hchk := (List.all_eq_true.1 (hc n hn')) e he
  simp only [Entry.check, hen, hek] at hchk
  exact case_sound n B t α β hadm _ _ (caseKey_perm n B t) hchk

end CubelikeSC.Cert
