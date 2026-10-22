import Mathlib
import P16c.SectionRelations

/-! # `P(Γ)` covers every regular polytope whose group is a quotient of `Γ`
under its distinguished generators (ARP 4A2, covering form)

The covering is `x Γ_k ↦ π(x) φ_{k-1}`. -/

namespace P16c

open scoped Pointwise

namespace StringCGroup

variable {G : Type*} [Group G] {n : ℕ} (Γ : StringCGroup G n)
  {Q : Type*} [PartialOrder Q] {rank : Q → ℤ} (hQ : IsPolytope Q n rank)
  (D : Distinguished Q n rank) (π : G →* (Q ≃o Q)) (hπ : ∀ i, π (Γ.ρ i) = D.σ i)

include hπ in
lemma pi_sub_fix (k : Fin (n + 2)) {g : G} (hg : g ∈ Γ.sub k) :
    π g (D.φ ((k.val : ℤ) - 1)) = D.φ ((k.val : ℤ) - 1) := by
  have hle : Γ.sub k ≤ (D.stab ((k.val : ℤ) - 1) ((k.val : ℤ) - 1)).comap π := by
    apply Subgroup.closure_le _ |>.mpr
    rintro _ ⟨i, hi, rfl⟩
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi
    have h := D.σ_φ i (by omega) (by have := i.isLt; omega) ((k.val : ℤ) - 1) (by omega)
      (by have := k.isLt; omega) (by omega)
    change π (Γ.ρ i) ∈ D.stab _ _
    rw [hπ]
    exact ⟨h, h⟩
  exact (hle hg).1

/-- The covering map `x Γ_k ↦ π(x) φ_{k-1}`. -/
noncomputable def cov (F : Γ.Face) : Q :=
  π (Γ.exists_face F).choose (D.φ ((F.1.1.val : ℤ) - 1))

include hπ in
lemma cov_face (k : Fin (n + 2)) {x : G} (hx : x ∈ Γ.group) :
    Γ.cov D π (Γ.face k hx) = π x (D.φ ((k.val : ℤ) - 1)) := by
  unfold cov
  obtain ⟨hy, he⟩ := (Γ.exists_face (Γ.face k hx)).choose_spec
  set y := (Γ.exists_face (Γ.face k hx)).choose
  have h := ((Γ.face_eq_iff hx hy).mp he).2
  simp only [face_type]
  have := Γ.pi_sub_fix D π hπ k h
  rw [map_mul, map_inv, RelIso.mul_apply] at this
  have h2 := congrArg (π x) this
  rw [RelIso.apply_inv_self] at h2
  exact h2

lemma flagOf_adjacent_char {x y : G} (hx : x ∈ Γ.group) (hy : y ∈ Γ.group) {F : Γ.Face}
    (hd : (Γ.flagOf hx : Set Γ.Face) \ Γ.flagOf hy = {F}) :
    x = y ∨ ∃ i : Fin n, y = x * Γ.ρ i ∧ F = Γ.face ⟨i.val + 1, by omega⟩ hx := by
  classical
  have hF : F ∈ (Γ.flagOf hx : Set Γ.Face) \ Γ.flagOf hy := hd ▸ Set.mem_singleton F
  obtain ⟨k, hk⟩ := hF.1
  have hother : ∀ l, l ≠ k → x⁻¹ * y ∈ Γ.sub l := by
    intro l hl
    have hmem : Γ.face l hx ∈ (Γ.flagOf hy : Set Γ.Face) := by
      by_contra h
      have : Γ.face l hx ∈ (Γ.flagOf hx : Set Γ.Face) \ Γ.flagOf hy := ⟨⟨l, rfl⟩, h⟩
      rw [hd, ← hk] at this
      exact hl ((Γ.face_eq_iff hx hx).mp this).1
    obtain ⟨l', hl'⟩ := hmem
    obtain ⟨rfl, h⟩ := (Γ.face_eq_iff hy hx).mp hl'
    simpa using (Γ.sub l').inv_mem h
  have hxy : x⁻¹ * y ∈ Γ.group := Γ.group.mul_mem (Γ.group.inv_mem hx) hy
  have hm := Γ.mem_parabolic_filter (Finset.univ.erase k) hxy
    (fun l hl => hother l (Finset.ne_of_mem_erase hl))
  by_cases hk0 : ∃ i : Fin n, i.val + 1 = k.val
  · obtain ⟨i, hi⟩ := hk0
    have hS : (Finset.univ.filter fun i' : Fin n =>
        ∀ l ∈ Finset.univ.erase k, i'.val + 1 ≠ l.val) = {i} := by
      ext i'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
        Finset.mem_singleton, and_true]
      constructor
      · intro h
        by_contra hne
        exact h ⟨i'.val + 1, by omega⟩ (fun e => hne (Fin.ext (by
          have := congrArg Fin.val e; simp only at this; omega))) rfl
      · rintro rfl l hl e; exact hl (Fin.ext (by omega))
    rw [hS] at hm
    rcases Γ.mem_parabolic_singleton hm with h | h
    · left; rwa [inv_mul_eq_one] at h
    · right
      refine ⟨i, by rw [← h]; group, ?_⟩
      rw [← hk]; congr 1; exact Fin.ext hi.symm
  · have hS : (Finset.univ.filter fun i' : Fin n =>
        ∀ l ∈ Finset.univ.erase k, i'.val + 1 ≠ l.val) = ∅ := by
      ext i'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true,
        Finset.notMem_empty, iff_false, not_forall, not_not]
      refine ⟨⟨i'.val + 1, by omega⟩, fun e => hk0 ⟨i', by rw [← e]⟩, rfl⟩
    rw [hS, parabolic_empty, Subgroup.mem_bot, inv_mul_eq_one] at hm
    exact Or.inl hm

include hQ hπ in
/-- **The covering.** If `π : Γ → Γ(Q)` maps the generators to the distinguished
generators of `Q` and is onto `Γ(Q)`, then `x Γ_k ↦ π(x) φ_{k-1}` is a covering
`P(Γ) → Q`. -/
theorem isCovering_cov (hsurj : ∀ τ : Q ≃o Q, ∃ x ∈ Γ.group, π x = τ) (hreg : IsRegular Q) :
    IsCovering Γ.rank rank (Γ.cov D π) := by
  have hcov := Γ.cov_face D π hπ
  have hrank : ∀ (k : Fin (n + 2)) {x : G} (hx : x ∈ Γ.group),
      rank (Γ.cov D π (Γ.face k hx)) = (k.val : ℤ) - 1 := fun k x hx => by
    rw [hcov, hQ.rank_map hQ, D.φ_rank _ (by omega) (by have := k.isLt; omega)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro G'
    obtain ⟨Ψ, hΨ⟩ := exists_flag_mem G'
    obtain ⟨τ, hτ⟩ := hreg D.Φ Ψ
    obtain ⟨x, hx, rfl⟩ := hsurj τ
    have : G' ∈ (Flag.map (π x) D.Φ : Set Q) := by rw [hτ]; exact hΨ
    rw [Flag.coe_map] at this
    obtain ⟨H, hH, rfl⟩ := this
    have hHr := hQ.rank_mem H
    obtain ⟨j, hj⟩ : ∃ j, rank H = j := ⟨_, rfl⟩
    rw [hj] at hHr
    refine ⟨Γ.face ⟨(j + 1).toNat, by omega⟩ hx, ?_⟩
    rw [hcov]
    congr 1
    have e : H = D.φ j := by rw [← hj]; exact D.mem_Φ hQ hH
    refine Eq.trans ?_ e.symm
    congr 1; simp only; omega
  · intro F H hFH
    obtain ⟨w, hwF, hwH⟩ := hFH.2
    have hw := Γ.mem_group_of_mem F hwF
    rw [Γ.face_eq_of_mem F hwF hw, Γ.face_eq_of_mem H hwH hw, hcov, hcov]
    apply (π w).monotone
    have h1 := Fin.le_def.mp hFH.1
    rcases (show (F.1.1.val : ℤ) - 1 = (H.1.1.val : ℤ) - 1 ∨
        (F.1.1.val : ℤ) - 1 < (H.1.1.val : ℤ) - 1 by omega) with e | e
    · rw [e]
    · exact (D.φ_lt hQ (by omega) e (by have := H.1.1.isLt; omega)).le
  · intro F
    obtain ⟨x, hx, hF⟩ := Γ.exists_face F
    rw [hF, hrank]; rfl
  · intro Φ Ψ ⟨F, hd⟩
    obtain ⟨x, hx, rfl⟩ := Γ.exists_flagOf Φ
    obtain ⟨y, hy, rfl⟩ := Γ.exists_flagOf Ψ
    obtain hyx | ⟨i, hyx, hF⟩ := Γ.flagOf_adjacent_char hx hy hd
    · subst hyx
      have := hd ▸ Set.mem_singleton F
      exact absurd this.1 this.2
    · subst hyx
      refine ⟨π x (D.φ i), ?_⟩
      have hi0 : (0 : ℤ) ≤ i := by omega
      have hin : (i : ℤ) < n := by have := i.isLt; omega
      have himg : ∀ z (hz : z ∈ Γ.group), Γ.cov D π '' (Γ.flagOf hz : Set Γ.Face) =
          Set.range fun k : Fin (n + 2) => π z (D.φ ((k.val : ℤ) - 1)) := by
        intro z hz
        rw [coe_flagOf, flagSet, ← Set.range_comp]
        congr 1; funext k; exact hcov k hz
      rw [himg, himg]
      ext G'
      simp only [Set.mem_sdiff, Set.mem_range, Set.mem_singleton_iff, map_mul,
        RelIso.mul_apply, hπ]
      constructor
      · rintro ⟨⟨k, rfl⟩, hnot⟩
        by_contra hne
        apply hnot
        refine ⟨k, ?_⟩
        have hki : (k.val : ℤ) - 1 ≠ i := fun e => hne (by rw [e])
        rw [D.σ_φ i hi0 hin _ (by omega) (by have := k.isLt; omega) hki]
      · rintro rfl
        refine ⟨⟨⟨i.val + 1, by omega⟩, by congr 2; simp⟩, ?_⟩
        rintro ⟨k, hk⟩
        have := (π x).injective hk
        by_cases hki : (k.val : ℤ) - 1 = i
        · rw [hki, D.σ_φi i hi0 hin] at this
          exact (D.φ'_ne i hi0 hin this).elim
        · rw [D.σ_φ i hi0 hin _ (by omega) (by have := k.isLt; omega) hki] at this
          have := congrArg rank this
          rw [D.φ_rank _ (by omega) (by have := k.isLt; omega),
            D.φ_rank _ (by omega) (by omega)] at this
          exact hki this

end StringCGroup

end P16c
