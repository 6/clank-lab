import Mathlib
import P16c.PolytopeTheory

/-! # Distinguished generators of a regular polytope (ARP §2B)

For a regular `n`-polytope with base flag `Φ = {φ_{-1}, …, φ_n}`, `σ_i` is the
automorphism mapping `Φ` to its `i`-adjacent flag. The `σ_i` generate the
automorphism group, are involutions, and `σ_i, σ_j` commute for `|i - j| ≥ 2`. -/

namespace P16c

/-- A base flag, by rank, with its adjacent faces and distinguished generators. -/
structure Distinguished (Q : Type*) [PartialOrder Q] (n : ℕ) (rank : Q → ℤ) where
  Φ : Flag Q
  φ : ℤ → Q
  φ' : ℤ → Q
  σ : ℤ → (Q ≃o Q)
  φ_mem : ∀ j : ℤ, -1 ≤ j → j ≤ n → φ j ∈ Φ
  φ_rank : ∀ j : ℤ, -1 ≤ j → j ≤ n → rank (φ j) = j
  φ'_ne : ∀ i : ℤ, 0 ≤ i → i < n → φ' i ≠ φ i
  φ'_lt : ∀ i : ℤ, 0 ≤ i → i < n → φ (i - 1) < φ' i
  lt_φ' : ∀ i : ℤ, 0 ≤ i → i < n → φ' i < φ (i + 1)
  σ_φ : ∀ i : ℤ, 0 ≤ i → i < n → ∀ j : ℤ, -1 ≤ j → j ≤ n → j ≠ i → σ i (φ j) = φ j
  σ_φi : ∀ i : ℤ, 0 ≤ i → i < n → σ i (φ i) = φ' i

namespace IsPolytope

variable {Q : Type*} [PartialOrder Q] {n : ℕ} {rank : Q → ℤ} (hQ : IsPolytope Q n rank)
include hQ

/-- Every regular polytope has distinguished generators for any base flag. -/
theorem exists_distinguished (hreg : IsRegular Q) (Φ : Flag Q) :
    ∃ D : Distinguished Q n rank, D.Φ = Φ := by
  classical
  obtain ⟨B, hB⟩ := hQ.exists_least
  have hBΦ : B ∈ Φ := mem_flag_of_comparable Φ (fun G _ => Or.inl (hB G))
  have hex : ∀ j : ℤ, ∃ G : Q, -1 ≤ j → j ≤ n → G ∈ Φ ∧ rank G = j := by
    intro j
    by_cases h : -1 ≤ j ∧ j ≤ n
    · obtain ⟨G, hG, e⟩ := hQ.exists_rank_mem Φ h.1 h.2
      exact ⟨G, fun _ _ => ⟨hG, e⟩⟩
    · exact ⟨B, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose φ hφ using hex
  have hadj : ∀ i : ℤ, ∃ p : Q × (Q ≃o Q), 0 ≤ i → i < n →
      p.1 ≠ φ i ∧ φ (i - 1) < p.1 ∧ p.1 < φ (i + 1) ∧
      (∀ j : ℤ, -1 ≤ j → j ≤ n → j ≠ i → p.2 (φ j) = φ j) ∧ p.2 (φ i) = p.1 := by
    intro i
    by_cases h : 0 ≤ i ∧ i < n
    · have h1 := hφ (i - 1) (by omega) (by omega)
      have h2 := hφ i (by omega) (by omega)
      have h3 := hφ (i + 1) (by omega) (by omega)
      obtain ⟨F', hne, hlt1, hlt2, Ψ, hΨ⟩ := hQ.exists_adjacent Φ h1.1 h2.1 h3.1
        (by rw [h1.2, h2.2]; ring) (by rw [h2.2, h3.2])
      obtain ⟨σ, hσ⟩ := hreg Φ Ψ
      have hrF' : rank F' = i := by
        have := hQ.rank_strictMono hlt1; have := hQ.rank_strictMono hlt2
        rw [h1.2] at *; rw [h3.2] at *; omega
      have hmemΨ : ∀ G ∈ Φ, σ G ∈ Ψ := fun G hG => by
        rw [← hσ]; show σ G ∈ (Flag.map σ Φ : Set Q); rw [Flag.coe_map]; exact ⟨G, hG, rfl⟩
      refine ⟨(F', σ), fun _ _ => ⟨hne, hlt1, hlt2, ?_, ?_⟩⟩
      · intro j hj1 hj2 hji
        have hj := hφ j hj1 hj2
        have hin : φ j ∈ (Ψ : Set Q) := by
          rw [hΨ]; refine Set.mem_insert_of_mem _ ⟨hj.1, ?_⟩
          intro e; apply hji; rw [← hj.2, ← h2.2]; exact congrArg rank e
        exact hQ.flag_eq_of_rank_eq Ψ (hmemΨ _ hj.1) hin
          (by rw [hQ.rank_map hQ, hj.2])
      · have hin : F' ∈ (Ψ : Set Q) := by rw [hΨ]; exact Set.mem_insert _ _
        exact hQ.flag_eq_of_rank_eq Ψ (hmemΨ _ h2.1) hin (by rw [hQ.rank_map hQ, h2.2, hrF'])
    · exact ⟨(B, 1), fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose p hp using hadj
  exact ⟨{ Φ := Φ, φ := φ, φ' := fun i => (p i).1, σ := fun i => (p i).2
           φ_mem := fun j h1 h2 => (hφ j h1 h2).1
           φ_rank := fun j h1 h2 => (hφ j h1 h2).2
           φ'_ne := fun i h1 h2 => (hp i h1 h2).1
           φ'_lt := fun i h1 h2 => (hp i h1 h2).2.1
           lt_φ' := fun i h1 h2 => (hp i h1 h2).2.2.1
           σ_φ := fun i h1 h2 => (hp i h1 h2).2.2.2.1
           σ_φi := fun i h1 h2 => (hp i h1 h2).2.2.2.2 }, rfl⟩

end IsPolytope

namespace Distinguished

variable {Q : Type*} [PartialOrder Q] {n : ℕ} {rank : Q → ℤ} (D : Distinguished Q n rank)
  (hQ : IsPolytope Q n rank)
include hQ

lemma mem_Φ {F : Q} (hF : F ∈ D.Φ) : F = D.φ (rank F) := by
  have h := hQ.rank_mem F
  exact hQ.flag_eq_of_rank_eq D.Φ hF (D.φ_mem _ h.1 h.2) (D.φ_rank _ h.1 h.2).symm

lemma φ_lt {j k : ℤ} (hj : -1 ≤ j) (hjk : j < k) (hk : k ≤ n) : D.φ j < D.φ k :=
  hQ.flag_lt_of_rank_lt D.Φ (D.φ_mem j hj (by omega)) (D.φ_mem k (by omega) hk)
    (by rw [D.φ_rank j hj (by omega), D.φ_rank k (by omega) hk]; exact hjk)

/-- An automorphism fixing every `φ_j` is the identity. -/
lemma eq_one (τ : Q ≃o Q) (h : ∀ j : ℤ, -1 ≤ j → j ≤ n → τ (D.φ j) = D.φ j) : τ = 1 :=
  hQ.eq_one_of_fix τ D.Φ (fun F hF => by
    rw [D.mem_Φ hQ hF]; exact h _ (hQ.rank_mem F).1 (hQ.rank_mem F).2)

/-- Automorphisms fix the least and the greatest face. -/
lemma fix_ends (τ : Q ≃o Q) : τ (D.φ (-1)) = D.φ (-1) ∧ τ (D.φ n) = D.φ n := by
  obtain ⟨B, hB⟩ := hQ.exists_least
  obtain ⟨T, hT⟩ := hQ.exists_greatest
  have hBφ : B = D.φ (-1) := hQ.flag_eq_of_rank_eq D.Φ
    (IsPolytope.mem_flag_of_comparable D.Φ (fun G _ => Or.inl (hB G)))
    (D.φ_mem _ le_rfl (by omega)) (by rw [hQ.least_rank hB, D.φ_rank _ le_rfl (by omega)])
  have hTφ : T = D.φ n := hQ.flag_eq_of_rank_eq D.Φ
    (IsPolytope.mem_flag_of_comparable D.Φ (fun G _ => Or.inr (hT G)))
    (D.φ_mem _ (by omega) le_rfl) (by rw [hQ.greatest_rank hT, D.φ_rank _ (by omega) le_rfl])
  rw [← hBφ, ← hTφ]
  refine ⟨le_antisymm ?_ (hB _), le_antisymm (hT _) ?_⟩
  · simpa using τ.monotone (hB (τ.symm B))
  · simpa using τ.monotone (hT (τ.symm T))

lemma between (i : ℤ) (hi0 : 0 ≤ i) (hin : i < n) :
    D.φ (i - 1) < D.φ (i + 1) ∧ rank (D.φ (i + 1)) = rank (D.φ (i - 1)) + 2 :=
  ⟨D.φ_lt hQ (by omega) (by omega) (by omega),
    by rw [D.φ_rank _ (by omega) (by omega), D.φ_rank _ (by omega) (by omega)]; ring⟩

/-- `σ_i` swaps `φ_i` and `φ'_i`. -/
lemma σ_φ'_self (i : ℤ) (hi0 : 0 ≤ i) (hin : i < n) : D.σ i (D.φ' i) = D.φ i := by
  obtain ⟨hAC, hr⟩ := D.between hQ i hi0 hin
  have hA := D.σ_φ i hi0 hin (i - 1) (by omega) (by omega) (by omega)
  have hC := D.σ_φ i hi0 hin (i + 1) (by omega) (by omega) (by omega)
  apply hQ.diamond_other hAC hr ⟨D.φ'_lt i hi0 hin, D.lt_φ' i hi0 hin⟩
    ⟨D.φ_lt hQ (by omega) (by omega) (by omega), D.φ_lt hQ (by omega) (by omega) (by omega)⟩
    (D.φ'_ne i hi0 hin)
  · rw [← hA, ← hC]
    exact ⟨(D.σ i).strictMono (D.φ'_lt i hi0 hin), (D.σ i).strictMono (D.lt_φ' i hi0 hin)⟩
  · intro e
    apply D.φ'_ne i hi0 hin
    rw [← D.σ_φi i hi0 hin] at e ⊢
    exact (D.σ i).injective e

/-- `σ_i` fixes `φ'_j` for `|i - j| ≥ 2`. -/
lemma σ_φ'_far (i j : ℤ) (hi0 : 0 ≤ i) (hin : i < n) (hj0 : 0 ≤ j) (hjn : j < n)
    (hij : 2 ≤ i - j ∨ 2 ≤ j - i) : D.σ i (D.φ' j) = D.φ' j := by
  obtain ⟨hAC, hr⟩ := D.between hQ j hj0 hjn
  have hA := D.σ_φ i hi0 hin (j - 1) (by omega) (by omega) (by omega)
  have hC := D.σ_φ i hi0 hin (j + 1) (by omega) (by omega) (by omega)
  have hF := D.σ_φ i hi0 hin j (by omega) (by omega) (by omega)
  apply hQ.diamond_other hAC hr
    ⟨D.φ_lt hQ (by omega) (by omega) (by omega), D.φ_lt hQ (by omega) (by omega) (by omega)⟩
    ⟨D.φ'_lt j hj0 hjn, D.lt_φ' j hj0 hjn⟩ (D.φ'_ne j hj0 hjn).symm
  · rw [← hA, ← hC]
    exact ⟨(D.σ i).strictMono (D.φ'_lt j hj0 hjn), (D.σ i).strictMono (D.lt_φ' j hj0 hjn)⟩
  · rw [← hF]
    exact fun e => D.φ'_ne j hj0 hjn ((D.σ i).injective e)

theorem σ_sq (i : ℤ) (hi0 : 0 ≤ i) (hin : i < n) : D.σ i ^ 2 = 1 := by
  apply D.eq_one hQ
  intro j hj1 hj2
  rw [pow_two, RelIso.mul_apply]
  by_cases hji : j = i
  · subst hji; rw [D.σ_φi j hi0 hin, D.σ_φ'_self hQ j hi0 hin]
  · rw [D.σ_φ i hi0 hin j hj1 hj2 hji, D.σ_φ i hi0 hin j hj1 hj2 hji]

theorem σ_comm (i j : ℤ) (hi0 : 0 ≤ i) (hin : i < n) (hj0 : 0 ≤ j) (hjn : j < n)
    (hij : 2 ≤ i - j ∨ 2 ≤ j - i) : (D.σ i * D.σ j) ^ 2 = 1 := by
  apply D.eq_one hQ
  intro k hk1 hk2
  simp only [pow_two, RelIso.mul_apply]
  by_cases hki : k = i
  · subst hki
    have hkj : k ≠ j := by omega
    rw [D.σ_φ j hj0 hjn k hk1 hk2 hkj, D.σ_φi k hi0 hin, D.σ_φ'_far hQ j k hj0 hjn hi0 hin
      (by omega), D.σ_φ'_self hQ k hi0 hin]
  by_cases hkj : k = j
  · subst hkj
    rw [D.σ_φi k hj0 hjn, D.σ_φ'_far hQ i k hi0 hin hj0 hjn hij, D.σ_φ'_self hQ k hj0 hjn,
      D.σ_φ i hi0 hin k hk1 hk2 hki]
  · rw [D.σ_φ j hj0 hjn k hk1 hk2 hkj, D.σ_φ i hi0 hin k hk1 hk2 hki,
      D.σ_φ j hj0 hjn k hk1 hk2 hkj, D.σ_φ i hi0 hin k hk1 hk2 hki]

/-- **The distinguished generators generate the automorphism group** (ARP 2B). -/
theorem mem_closure (τ : Q ≃o Q) :
    τ ∈ Subgroup.closure (Set.range fun i : Fin n => D.σ i) := by
  set W := Subgroup.closure (Set.range fun i : Fin n => D.σ i)
  have key : ∀ Ψ : Flag Q, ∃ w ∈ W, Flag.map w D.Φ = Ψ := by
    intro Ψ
    have h := Relation.ReflTransGen.mono (fun _ _ h => h.1) _ _
      (hQ.strongly_flag_connected D.Φ Ψ)
    induction h with
    | refl => exact ⟨1, W.one_mem, SetLike.coe_injective (by simp [Flag.coe_map])⟩
    | @tail Ψ1 Ψ2 _ hadj ih =>
      obtain ⟨w, hw, hwΦ⟩ := ih
      obtain ⟨F, hd⟩ := hadj
      have hF : F ∈ (Ψ1 : Set Q) \ Ψ2 := hd ▸ Set.mem_singleton F
      have hmem : ∀ G ∈ D.Φ, w G ∈ Ψ1 := fun G hG => by
        rw [← hwΦ]; show w G ∈ (Flag.map w D.Φ : Set Q); rw [Flag.coe_map]; exact ⟨G, hG, rfl⟩
      -- the new face of `Ψ2`
      obtain ⟨G, hG, hGr⟩ := hQ.exists_rank_mem Ψ2 (j := rank F) (hQ.rank_mem F).1
        (hQ.rank_mem F).2
      have hGΨ1 : G ∉ Ψ1 := fun h => hF.2 (hQ.flag_eq_of_rank_eq Ψ1 h hF.1 hGr ▸ hG)
      obtain ⟨-, A, hA, C, hC, -, -, hAF, hFC, hAG, hGC, hr⟩ :=
        hQ.adjacent_structure hd hG hGΨ1
      set i := rank F with hi
      have hAr : rank A = i - 1 := by
        have := hQ.rank_strictMono hAF; have := hQ.rank_strictMono hFC; omega
      have hCr : rank C = i + 1 := by
        have := hQ.rank_strictMono hAF; have := hQ.rank_strictMono hFC; omega
      have hi0 : 0 ≤ i := by have := (hQ.rank_mem A).1; omega
      have hin : i < n := by have := (hQ.rank_mem C).2; omega
      have hrank : ∀ j : ℤ, -1 ≤ j → j ≤ n → rank (w (D.φ j)) = j := fun j h1 h2 => by
        rw [hQ.rank_map hQ, D.φ_rank j h1 h2]
      have hFw : F = w (D.φ i) := hQ.flag_eq_of_rank_eq Ψ1 hF.1 (hmem _ (D.φ_mem i (by omega)
        (by omega))) (by rw [hrank i (by omega) (by omega)])
      have hAw : A = w (D.φ (i - 1)) := hQ.flag_eq_of_rank_eq Ψ1 hA (hmem _ (D.φ_mem _
        (by omega) (by omega))) (by rw [hrank _ (by omega) (by omega), hAr])
      have hCw : C = w (D.φ (i + 1)) := hQ.flag_eq_of_rank_eq Ψ1 hC (hmem _ (D.φ_mem _
        (by omega) (by omega))) (by rw [hrank _ (by omega) (by omega), hCr])
      have hother : ∀ H ∈ Ψ1, H ≠ F → H ∈ Ψ2 := fun H hH hne => by
        by_contra h
        have : H ∈ (Ψ1 : Set Q) \ Ψ2 := ⟨hH, h⟩
        rw [hd] at this; exact hne this
      refine ⟨w * D.σ i, W.mul_mem hw (Subgroup.subset_closure ⟨⟨i.toNat, by omega⟩,
        by simp only; congr 1; omega⟩), ?_⟩
      apply SetLike.coe_injective
      apply (Flag.map (w * D.σ i) D.Φ).max_chain' Ψ2.chain_le
      change ((Flag.map (w * D.σ i) D.Φ : Set Q)) ⊆ Ψ2
      rw [Flag.coe_map]
      rintro _ ⟨H, hH, rfl⟩
      rw [D.mem_Φ hQ hH, RelIso.mul_apply]
      have hHr := hQ.rank_mem H
      by_cases hji : rank H = i
      · rw [hji, D.σ_φi i hi0 hin]
        have hne : w (D.φ' i) ≠ F := by
          rw [hFw]; exact fun e => D.φ'_ne i hi0 hin (w.injective e)
        have := hQ.diamond_other (hAF.trans hFC) hr ⟨hAF, hFC⟩ ⟨hAG, hGC⟩
          (fun e => hGΨ1 (e ▸ hF.1)) (H := w (D.φ' i))
          (by rw [hAw, hCw]; exact ⟨w.strictMono (D.φ'_lt i hi0 hin),
            w.strictMono (D.lt_φ' i hi0 hin)⟩) hne
        rw [this]; exact hG
      · rw [D.σ_φ i hi0 hin _ hHr.1 hHr.2 hji]
        apply hother _ (hmem _ (D.φ_mem _ hHr.1 hHr.2))
        rw [hFw]; intro e
        exact hji (by have := congrArg rank (w.injective e)
                      rwa [D.φ_rank _ hHr.1 hHr.2, D.φ_rank _ (by omega) (by omega)] at this)
  obtain ⟨w, hw, hwτ⟩ := key (Flag.map τ D.Φ)
  have hfix : w⁻¹ * τ = 1 := by
    apply D.eq_one hQ
    intro j hj1 hj2
    have hτ : τ (D.φ j) ∈ (Flag.map w D.Φ : Set Q) := by
      rw [hwτ, Flag.coe_map]; exact ⟨_, D.φ_mem j hj1 hj2, rfl⟩
    obtain ⟨G, hG, hGe⟩ := hτ
    have hGr : rank G = j := by
      rw [← hQ.rank_map hQ w, hGe, hQ.rank_map hQ, D.φ_rank j hj1 hj2]
    rw [RelIso.mul_apply, ← hGe, RelIso.inv_apply_self, D.mem_Φ hQ hG, hGr]
  rw [inv_mul_eq_one] at hfix
  exact hfix ▸ hw

end Distinguished

end P16c
