import Mathlib
import P16c.Polytope

/-! # Basic facts about abstract polytopes (ARP §2A–2B)

Flags meet every rank exactly once; order isomorphisms preserve rank; each
flag has an `j`-adjacent flag for every proper rank `j`; and an automorphism
fixing every face of one flag is the identity. -/

namespace P16c

/-- A strictly increasing self-map of an integer interval is the identity there. -/
lemma Int.strictMono_on_Icc_eq {a b : ℤ} (f : ℤ → ℤ)
    (hf : ∀ i j, a ≤ i → i < j → j ≤ b → f i < f j)
    (hmem : ∀ i, a ≤ i → i ≤ b → a ≤ f i ∧ f i ≤ b) :
    ∀ i, a ≤ i → i ≤ b → f i = i := by
  have lo : ∀ k : ℕ, a + k ≤ b → a + k ≤ f (a + k) := by
    intro k
    induction k with
    | zero => intro h; simpa using (hmem a le_rfl (by simpa using h)).1
    | succ k ih =>
      intro h
      have h1 := ih (by push_cast at h; omega)
      have h2 := hf (a + k) (a + (k + 1 : ℕ)) (by omega) (by push_cast; omega) h
      push_cast at h2 ⊢; omega
  have hi : ∀ k : ℕ, a ≤ b - k → f (b - k) ≤ b - k := by
    intro k
    induction k with
    | zero => intro h; simpa using (hmem b (by simpa using h) le_rfl).2
    | succ k ih =>
      intro h
      have h1 := ih (by push_cast at h; omega)
      have h2 := hf (b - (k + 1 : ℕ)) (b - k) h (by push_cast; omega) (by omega)
      push_cast at h2 ⊢; omega
  intro i hai hib
  have e1 := lo (i - a).toNat (by omega)
  have e2 := hi (b - i).toNat (by omega)
  rw [show a + ((i - a).toNat : ℤ) = i by omega] at e1
  rw [show b - ((b - i).toNat : ℤ) = i by omega] at e2
  omega

lemma exists_flag_mem {P : Type*} [PartialOrder P] (F : P) : ∃ Φ : Flag P, F ∈ Φ := by
  obtain ⟨M, hM, hsub⟩ := (Set.Subsingleton.isChain (Set.subsingleton_singleton (a := F)) :
    IsChain (· ≤ ·) ({F} : Set P)).exists_maxChain
  exact ⟨Flag.ofIsMaxChain M hM, hsub (Set.mem_singleton F)⟩

namespace IsPolytope

variable {P : Type*} [PartialOrder P] {n : ℕ} {rank : P → ℤ} (hP : IsPolytope P n rank)
include hP

lemma eq_of_rank_eq {F G : P} (h : F ≤ G ∨ G ≤ F) (hr : rank F = rank G) : F = G := by
  rcases h with h | h
  · rcases h.lt_or_eq with h | h
    · exact absurd hr (hP.rank_strictMono h).ne
    · exact h
  · rcases h.lt_or_eq with h | h
    · exact absurd hr (hP.rank_strictMono h).ne'
    · exact h.symm

lemma lt_of_rank_lt {F G : P} (h : F ≤ G ∨ G ≤ F) (hr : rank F < rank G) : F < G := by
  rcases h with h | h
  · exact lt_of_le_of_ne h (fun e => by rw [e] at hr; exact lt_irrefl _ hr)
  · exact absurd (hP.rank_strictMono.monotone h) (not_le.mpr hr)

lemma flag_eq_of_rank_eq (Φ : Flag P) {F G : P} (hF : F ∈ Φ) (hG : G ∈ Φ)
    (hr : rank F = rank G) : F = G :=
  hP.eq_of_rank_eq (Φ.le_or_le hF hG) hr

lemma flag_lt_of_rank_lt (Φ : Flag P) {F G : P} (hF : F ∈ Φ) (hG : G ∈ Φ)
    (hr : rank F < rank G) : F < G :=
  hP.lt_of_rank_lt (Φ.le_or_le hF hG) hr

omit hP in
lemma mem_flag_of_comparable (Φ : Flag P) {B : P} (hB : ∀ G ∈ Φ, B ≤ G ∨ G ≤ B) : B ∈ Φ := by
  have hc : IsChain (· ≤ ·) (insert B (Φ : Set P)) :=
    Φ.chain_le.insert (fun b hb _ => hB b hb)
  have := Φ.max_chain' hc (Set.subset_insert _ _)
  change B ∈ Φ.carrier
  rw [this]; exact Set.mem_insert _ _

lemma rank_image (Φ : Flag P) : rank '' (Φ : Set P) = Set.Icc (-1 : ℤ) n := by
  have hinj : Set.InjOn rank (Φ : Set P) := fun F hF G hG hr =>
    hP.flag_eq_of_rank_eq Φ hF hG hr
  have hsub : rank '' (Φ : Set P) ⊆ Set.Icc (-1) n := by
    rintro _ ⟨F, -, rfl⟩; exact hP.rank_mem F
  apply Set.eq_of_subset_of_ncard_le hsub _ (Set.finite_Icc _ _)
  rw [hinj.ncard_image, hP.flag_ncard Φ, Set.ncard_eq_toFinset_card',
    Set.toFinset_Icc, Int.card_Icc]
  omega

lemma exists_rank_mem (Φ : Flag P) {j : ℤ} (h1 : -1 ≤ j) (h2 : j ≤ n) :
    ∃ F ∈ Φ, rank F = j := by
  have : j ∈ rank '' (Φ : Set P) := by rw [hP.rank_image Φ]; exact ⟨h1, h2⟩
  obtain ⟨F, hF, e⟩ := this
  exact ⟨F, hF, e⟩

/-- A chain meeting every rank is a flag. -/
lemma isMaxChain_of_ranks {S : Set P} (hS : IsChain (· ≤ ·) S)
    (hr : ∀ j : ℤ, -1 ≤ j → j ≤ n → ∃ F ∈ S, rank F = j) : IsMaxChain (· ≤ ·) S := by
  refine ⟨hS, fun T hT hST => le_antisymm hST ?_⟩
  intro G hG
  obtain ⟨F, hF, e⟩ := hr (rank G) (hP.rank_mem G).1 (hP.rank_mem G).2
  have : F = G := by
    by_cases hFG : F = G
    · exact hFG
    exact hP.eq_of_rank_eq (hT (hST hF) hG hFG) e
  exact this ▸ hF

/-- Order isomorphisms between polytopes of the same rank preserve rank. -/
theorem rank_map {P' : Type*} [PartialOrder P'] {rank' : P' → ℤ}
    (hP' : IsPolytope P' n rank') (e : P ≃o P') (F : P) : rank' (e F) = rank F := by
  classical
  obtain ⟨Φ, hFΦ⟩ := exists_flag_mem F
  have hex : ∀ j : ℤ, ∃ G : P, -1 ≤ j → j ≤ n → G ∈ Φ ∧ rank G = j := by
    intro j
    by_cases h : -1 ≤ j ∧ j ≤ n
    · obtain ⟨G, hG, e⟩ := hP.exists_rank_mem Φ h.1 h.2
      exact ⟨G, fun _ _ => ⟨hG, e⟩⟩
    · exact ⟨F, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose g hg using hex
  have key := Int.strictMono_on_Icc_eq (a := -1) (b := n) (fun j => rank' (e (g j)))
    (fun i j hi hij hj => by
      have hgi := hg i hi (by omega); have hgj := hg j (by omega) hj
      apply hP'.rank_strictMono
      apply e.strictMono
      exact hP.flag_lt_of_rank_lt Φ hgi.1 hgj.1 (by rw [hgi.2, hgj.2]; exact hij))
    (fun i _ _ => hP'.rank_mem _)
  have hFr := hP.rank_mem F
  have hgF := hg (rank F) hFr.1 hFr.2
  have : g (rank F) = F := hP.flag_eq_of_rank_eq Φ hgF.1 hFΦ hgF.2
  have k2 : rank' (e (g (rank F))) = rank F := key (rank F) hFr.1 hFr.2
  rwa [‹g (rank F) = F›] at k2

lemma least_rank {B : P} (hB : ∀ G, B ≤ G) : rank B = -1 := by
  obtain ⟨Φ⟩ : Nonempty (Flag P) := ⟨(exists_flag_mem B).choose⟩
  obtain ⟨A, hA, hAr⟩ := hP.exists_rank_mem Φ le_rfl (by omega)
  have := hP.rank_strictMono.monotone (hB A)
  have := (hP.rank_mem B).1
  omega

lemma greatest_rank {T : P} (hT : ∀ G, G ≤ T) : rank T = n := by
  obtain ⟨Φ⟩ : Nonempty (Flag P) := ⟨(exists_flag_mem T).choose⟩
  obtain ⟨A, hA, hAr⟩ := hP.exists_rank_mem Φ (by omega) le_rfl
  have := hP.rank_strictMono.monotone (hT A)
  have := (hP.rank_mem T).2
  omega

/-- If `Ψ' ` differs from `Ψ` only in `F`, it differs only in one face `F'` of the
same rank, lying strictly between the neighbours `A`, `C` of `F` in `Ψ`. -/
lemma adjacent_structure {Ψ Ψ' : Flag P} {F : P} (hd : (Ψ : Set P) \ Ψ' = {F})
    {G : P} (hG : G ∈ Ψ') (hGΨ : G ∉ Ψ) :
    rank G = rank F ∧ ∃ A ∈ Ψ, ∃ C ∈ Ψ, A ∈ Ψ' ∧ C ∈ Ψ' ∧ A < F ∧ F < C ∧ A < G ∧ G < C ∧
      rank C = rank A + 2 := by
  have hF : F ∈ (Ψ : Set P) \ Ψ' := hd ▸ Set.mem_singleton F
  -- faces of `Ψ` other than `F` lie in `Ψ'`
  have hother : ∀ H ∈ Ψ, H ≠ F → H ∈ Ψ' := fun H hH hne => by
    by_contra h
    have : H ∈ (Ψ : Set P) \ Ψ' := ⟨hH, h⟩
    rw [hd] at this; exact hne this
  have hGr := hP.rank_mem G
  obtain ⟨H, hH, hHr⟩ := hP.exists_rank_mem Ψ hGr.1 hGr.2
  have hHF : H = F := by
    by_contra hne
    exact hGΨ (hP.flag_eq_of_rank_eq Ψ' (hother H hH hne) hG hHr ▸ hH)
  subst hHF
  refine ⟨hHr.symm, ?_⟩
  -- `F` is neither the least nor the greatest face
  obtain ⟨B, hB⟩ := hP.exists_least
  obtain ⟨T, hT⟩ := hP.exists_greatest
  have hBΨ' : B ∈ Ψ' := mem_flag_of_comparable Ψ' (fun G _ => Or.inl (hB G))
  have hTΨ' : T ∈ Ψ' := mem_flag_of_comparable Ψ' (fun G _ => Or.inr (hT G))
  have hBr := hP.least_rank hB
  have hTr := hP.greatest_rank hT
  have hlo : -1 < rank H := by
    by_contra h
    have : rank G = rank B := by omega
    exact hGΨ (hP.flag_eq_of_rank_eq Ψ' hG hBΨ' this ▸
      mem_flag_of_comparable Ψ (fun G _ => Or.inl (hB G)))
  have hhi : rank H < n := by
    by_contra h
    have : rank G = rank T := by omega
    exact hGΨ (hP.flag_eq_of_rank_eq Ψ' hG hTΨ' this ▸
      mem_flag_of_comparable Ψ (fun G _ => Or.inr (hT G)))
  obtain ⟨A, hA, hAr⟩ := hP.exists_rank_mem Ψ (j := rank H - 1) (by omega) (by omega)
  obtain ⟨C, hC, hCr⟩ := hP.exists_rank_mem Ψ (j := rank H + 1) (by omega) (by omega)
  have hAΨ' := hother A hA (fun e => by rw [e] at hAr; omega)
  have hCΨ' := hother C hC (fun e => by rw [e] at hCr; omega)
  exact ⟨A, hA, C, hC, hAΨ', hCΨ',
    hP.flag_lt_of_rank_lt Ψ hA hH (by omega), hP.flag_lt_of_rank_lt Ψ hH hC (by omega),
    hP.flag_lt_of_rank_lt Ψ' hAΨ' hG (by omega), hP.flag_lt_of_rank_lt Ψ' hG hCΨ' (by omega),
    by omega⟩

/-- In a diamond, a face other than one given face is the other one. -/
lemma diamond_other {A C F G H : P} (hAC : A < C) (hr : rank C = rank A + 2)
    (hF : A < F ∧ F < C) (hG : A < G ∧ G < C) (hFG : F ≠ G) (hH : A < H ∧ H < C)
    (hHF : H ≠ F) : H = G := by
  obtain ⟨x, y, hxy, hxy'⟩ := Set.ncard_eq_two.mp (hP.diamond A C hAC hr)
  have mF : F ∈ ({x, y} : Set P) := hxy' ▸ hF
  have mG : G ∈ ({x, y} : Set P) := hxy' ▸ hG
  have mH : H ∈ ({x, y} : Set P) := hxy' ▸ hH
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at mF mG mH
  rcases mF with rfl | rfl <;> rcases mG with rfl | rfl <;> rcases mH with rfl | rfl <;>
    first | rfl | exact absurd rfl hFG | exact absurd rfl hHF

/-- An automorphism fixing every face of a flag fixes every face of an adjacent flag. -/
lemma fix_adjacent (τ : P ≃o P) {Ψ Ψ' : Flag P} (hfix : ∀ F ∈ Ψ, τ F = F) {F : P}
    (hd : (Ψ : Set P) \ Ψ' = {F}) : ∀ G ∈ Ψ', τ G = G := by
  intro G hG
  by_cases hGΨ : G ∈ Ψ
  · exact hfix G hGΨ
  have hF : F ∈ (Ψ : Set P) \ Ψ' := hd ▸ Set.mem_singleton F
  obtain ⟨-, A, hA, C, hC, -, -, hAF, hFC, hAG, hGC, hr⟩ := hP.adjacent_structure hd hG hGΨ
  have hGF : G ≠ F := fun e => hF.2 (e ▸ hG)
  apply hP.diamond_other (hAF.trans hFC) hr ⟨hAF, hFC⟩ ⟨hAG, hGC⟩ hGF.symm
  · rw [← hfix A hA, ← hfix C hC]
    exact ⟨τ.strictMono hAG, τ.strictMono hGC⟩
  · rw [← hfix F hF.1]
    exact fun e => hGF (τ.injective e)

/-- **An automorphism fixing every face of one flag is the identity** (from
strong flag-connectedness and the diamond condition). -/
theorem eq_one_of_fix (τ : P ≃o P) (Φ : Flag P) (hfix : ∀ F ∈ Φ, τ F = F) : τ = 1 := by
  have hall : ∀ Ψ : Flag P, ∀ F ∈ Ψ, τ F = F := by
    intro Ψ
    have h := Relation.ReflTransGen.mono (fun _ _ h => h.1) _ _ (hP.strongly_flag_connected Φ Ψ)
    induction h with
    | refl => exact hfix
    | tail _ hab ih =>
      obtain ⟨F, hd⟩ := hab
      exact hP.fix_adjacent τ ih hd
  ext F
  obtain ⟨Ψ, hΨ⟩ := exists_flag_mem F
  exact hall Ψ F hΨ

/-- Every flag has a `j`-adjacent flag for each proper rank `j`: replacing its
`j`-face `F` by the other face `F'` between its neighbours `A` and `C`. -/
theorem exists_adjacent (Φ : Flag P) {A F C : P} (hA : A ∈ Φ) (hF : F ∈ Φ) (hC : C ∈ Φ)
    (hAr : rank A + 1 = rank F) (hCr : rank F + 1 = rank C) :
    ∃ F', F' ≠ F ∧ A < F' ∧ F' < C ∧
      ∃ Ψ : Flag P, (Ψ : Set P) = insert F' ((Φ : Set P) \ {F}) := by
  have hAF := hP.flag_lt_of_rank_lt Φ hA hF (by omega)
  have hFC := hP.flag_lt_of_rank_lt Φ hF hC (by omega)
  have h2 := hP.diamond A C (hAF.trans hFC) (by omega)
  obtain ⟨x, y, hxy, hxy'⟩ := Set.ncard_eq_two.mp h2
  have mF : F ∈ ({x, y} : Set P) := hxy' ▸ ⟨hAF, hFC⟩
  obtain ⟨F', hF'F, hF'⟩ : ∃ F', F' ≠ F ∧ F' ∈ ({x, y} : Set P) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at mF
    rcases mF with rfl | rfl
    · exact ⟨y, hxy.symm, by simp⟩
    · exact ⟨x, hxy, by simp⟩
  rw [← hxy'] at hF'
  obtain ⟨hAF', hF'C⟩ := hF'
  have hrF' : rank F' = rank F := by
    have := hP.rank_strictMono hAF'; have := hP.rank_strictMono hF'C; omega
  refine ⟨F', hF'F, hAF', hF'C, ?_⟩
  have hchain : IsChain (· ≤ ·) (insert F' ((Φ : Set P) \ {F})) := by
    refine (Φ.chain_le.mono Set.sdiff_subset).insert ?_
    rintro G ⟨hG, hGF⟩ -
    have hGF' : G ≠ F := hGF
    have hGr : rank G ≠ rank F := fun e => hGF' (hP.flag_eq_of_rank_eq Φ hG hF e)
    rcases lt_or_gt_of_ne hGr with h | h
    · have : G ≤ A := by
        by_cases e : G = A
        · exact e.le
        exact (hP.flag_lt_of_rank_lt Φ hG hA (by
          have : rank G ≠ rank A := fun e' => e (hP.flag_eq_of_rank_eq Φ hG hA e')
          omega)).le
      exact Or.inr (this.trans hAF'.le)
    · have : C ≤ G := by
        by_cases e : G = C
        · exact e.ge
        exact (hP.flag_lt_of_rank_lt Φ hC hG (by
          have : rank G ≠ rank C := fun e' => e (hP.flag_eq_of_rank_eq Φ hG hC e')
          omega)).le
      exact Or.inl (hF'C.le.trans this)
  have hmax := hP.isMaxChain_of_ranks hchain (fun j h1 h2 => by
    obtain ⟨G, hG, hGr⟩ := hP.exists_rank_mem Φ h1 h2
    by_cases e : G = F
    · subst e; exact ⟨F', Set.mem_insert _ _, hrF'.trans hGr⟩
    · exact ⟨G, Set.mem_insert_of_mem _ ⟨hG, e⟩, hGr⟩)
  exact ⟨Flag.ofIsMaxChain _ hmax, rfl⟩

end IsPolytope

end P16c
