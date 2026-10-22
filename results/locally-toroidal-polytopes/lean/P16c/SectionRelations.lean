import Mathlib
import P16c.Distinguished
import P16c.CosetRegular

/-! # Facet and vertex-figure relations hold for the distinguished generators

If the section of a regular polytope `Q` between the base faces `φ_a` and
`φ_{a+m+1}` is isomorphic to `P(T)` for a string C-group `T` of rank `m`, then
every relation of `T`'s generators holds for `σ_{a+1}, …, σ_{a+m}` in the group
of `Q`. Used for the facet (`a = -1`) and the vertex-figure (`a = 0`). -/

namespace P16c

namespace Distinguished

variable {Q : Type*} [PartialOrder Q] {n : ℕ} {rank : Q → ℤ} (D : Distinguished Q n rank)
  (hQ : IsPolytope Q n rank)

/-- Automorphisms fixing `φ_a` and `φ_b`. -/
def stab (a b : ℤ) : Subgroup (Q ≃o Q) where
  carrier := {τ | τ (D.φ a) = D.φ a ∧ τ (D.φ b) = D.φ b}
  mul_mem' {τ τ'} h h' := by
    simp only [Set.mem_setOf_eq, RelIso.mul_apply] at *; rw [h'.1, h.1, h'.2, h.2]; simp
  one_mem' := by simp
  inv_mem' {τ} h := by
    simp only [Set.mem_setOf_eq] at *
    constructor
    · conv_lhs => rw [← h.1]
      exact RelIso.inv_apply_self τ _
    · conv_lhs => rw [← h.2]
      exact RelIso.inv_apply_self τ _

/-- Restriction of a stabilizing automorphism to the section `[φ_a, φ_b]`. -/
def restrictIcc (a b : ℤ) (τ : D.stab a b) :
    Set.Icc (D.φ a) (D.φ b) ≃o Set.Icc (D.φ a) (D.φ b) where
  toEquiv := (τ : Q ≃o Q).toEquiv.subtypeEquiv (fun x => by
    have h1 : D.φ a ≤ (τ : Q ≃o Q) x ↔ D.φ a ≤ x := by
      conv_lhs => rw [← τ.2.1]
      exact (τ : Q ≃o Q).le_iff_le
    have h2 : (τ : Q ≃o Q) x ≤ D.φ b ↔ x ≤ D.φ b := by
      conv_lhs => rw [← τ.2.2]
      exact (τ : Q ≃o Q).le_iff_le
    show (x ∈ Set.Icc _ _) ↔ ((τ : Q ≃o Q) x ∈ Set.Icc _ _)
    simp only [Set.mem_Icc, h1, h2])
  map_rel_iff' := (τ : Q ≃o Q).le_iff_le

@[simp] lemma restrictIcc_apply (a b : ℤ) (τ : D.stab a b) (x : Set.Icc (D.φ a) (D.φ b)) :
    ((D.restrictIcc a b τ x : Set.Icc (D.φ a) (D.φ b)) : Q) = (τ : Q ≃o Q) x := rfl

/-- The restriction, transported to `P(T)` along `e`. -/
def resHom {β : Type*} [PartialOrder β] (a b : ℤ) (e : Set.Icc (D.φ a) (D.φ b) ≃o β) :
    D.stab a b →* (β ≃o β) where
  toFun τ := e.symm.trans ((D.restrictIcc a b τ).trans e)
  map_one' := RelIso.ext fun F => by
    change e (D.restrictIcc a b 1 (e.symm F)) = F
    rw [show D.restrictIcc a b 1 (e.symm F) = e.symm F from Subtype.ext rfl]; simp
  map_mul' τ τ' := RelIso.ext fun F => by
    change e (D.restrictIcc a b (τ * τ') (e.symm F)) =
      e (D.restrictIcc a b τ (e.symm (e (D.restrictIcc a b τ' (e.symm F)))))
    rw [OrderIso.symm_apply_apply]; rfl

variable {H : Type*} [Group H] {m : ℕ} (T : StringCGroup H m)

include hQ in
/-- **The relations of a section's C-group hold for the distinguished generators.** -/
theorem section_relation (a : ℤ) (ha : -1 ≤ a) (ha0 : a ≤ 0) (hb : (n : ℤ) - 1 ≤ a + m + 1)
    (hbn : a + m + 1 ≤ n) (e : Set.Icc (D.φ a) (D.φ (a + m + 1)) ≃o T.Face)
    (w : FreeGroup (Fin m)) (hw : FreeGroup.lift T.ρ w = 1) :
    FreeGroup.lift (fun i : Fin m => D.σ (a + 1 + i)) w = 1 := by
  classical
  set b := a + m + 1 with hbdef
  have hT := T.isPolytope
  -- the base chain in `P(T)`
  have hgI : ∀ j : ℤ, -1 ≤ j → j ≤ m → D.φ (a + 1 + j) ∈ Set.Icc (D.φ a) (D.φ b) := by
    intro j h1 h2
    constructor
    · rcases (show a = a + 1 + j ∨ a < a + 1 + j by omega) with h | h
      · rw [← h]
      · exact (D.φ_lt hQ ha h (by omega)).le
    · rcases (show a + 1 + j = b ∨ a + 1 + j < b by omega) with h | h
      · rw [h]
      · exact (D.φ_lt hQ (by omega) h hbn).le
  let gI : ℤ → Set.Icc (D.φ a) (D.φ b) := fun j =>
    if h : -1 ≤ j ∧ j ≤ m then ⟨_, hgI j h.1 h.2⟩ else ⟨_, hgI (-1) le_rfl (by omega)⟩
  have gI_val : ∀ j : ℤ, -1 ≤ j → j ≤ m → (gI j : Q) = D.φ (a + 1 + j) := fun j h1 h2 => by
    simp only [gI, dif_pos (And.intro h1 h2)]
  have gI_lt : ∀ j k : ℤ, -1 ≤ j → j < k → k ≤ m → gI j < gI k := fun j k h1 h2 h3 => by
    change (gI j : Q) < gI k
    rw [gI_val j h1 (by omega), gI_val k (by omega) h3]
    exact D.φ_lt hQ (by omega) (by omega) (by omega)
  have hC : IsChain (· ≤ ·) (Set.range fun j => e (gI j)) := by
    rintro _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ -
    have : ∀ j : ℤ, ∃ j' : ℤ, -1 ≤ j' ∧ j' ≤ m ∧ gI j = gI j' := fun j => by
      by_cases h : -1 ≤ j ∧ j ≤ m
      · exact ⟨j, h.1, h.2, rfl⟩
      · exact ⟨-1, le_rfl, by omega, by simp only [gI, dif_neg h,
          dif_pos (And.intro le_rfl (by omega : (-1 : ℤ) ≤ m))]⟩
    obtain ⟨j', h1, h2, hj⟩ := this j
    obtain ⟨k', h3, h4, hk⟩ := this k
    beta_reduce
    rw [hj, hk]
    rcases lt_trichotomy j' k' with h | h | h
    · exact Or.inl (e.monotone (gI_lt _ _ h1 h h4).le)
    · exact Or.inl (by rw [h])
    · exact Or.inr (e.monotone (gI_lt _ _ h3 h h2).le)
  obtain ⟨x, hx, hxC⟩ := T.chain_common hC
  have hrank : ∀ j : ℤ, -1 ≤ j → j ≤ m → T.rank (e (gI j)) = j := by
    have := Int.strictMono_on_Icc_eq (a := -1) (b := m) (fun j => T.rank (e (gI j)))
      (fun i j hi hij hj => hT.rank_strictMono (e.strictMono (gI_lt i j hi hij hj)))
      (fun i _ _ => hT.rank_mem _)
    exact this
  have hbase : ∀ (j : ℕ) (hj : j < m + 2), e (gI ((j : ℤ) - 1)) = T.face ⟨j, hj⟩ hx := by
    intro j hj
    have h := hxC (e (gI ((j : ℤ) - 1))) ⟨(j : ℤ) - 1, rfl⟩
    rw [h]
    congr 1
    apply Fin.ext
    change _ = j
    have := hrank ((j : ℤ) - 1) (by omega) (by omega)
    rw [h] at this
    unfold StringCGroup.rank at this
    simp only [StringCGroup.face_type] at this
    omega
  -- the generators lie in the stabilizer, and are the conjugated generators of `T`
  have hσS : ∀ i : Fin m, D.σ (a + 1 + i) ∈ D.stab a b := fun i =>
    ⟨D.σ_φ _ (by omega) (by omega) a ha (by omega) (by omega),
      D.σ_φ _ (by omega) (by omega) b (by omega) hbn (by omega)⟩
  let σS : Fin m → D.stab a b := fun i => ⟨_, hσS i⟩
  have hIcc : ∀ j : ℤ, a ≤ j → j ≤ b → D.φ j ∈ Set.Icc (D.φ a) (D.φ b) := by
    intro j h1 h2
    have := hgI (j - a - 1) (by omega) (by omega)
    rwa [show a + 1 + (j - a - 1) = j by ring] at this
  have hres : ∀ i : Fin m, D.resHom a b e (σS i) =
      T.act ⟨x * T.ρ i * x⁻¹, T.group.mul_mem (T.group.mul_mem hx (T.rho_mem_group i))
        (T.group.inv_mem hx)⟩ := by
    intro i
    set α := T.act ⟨x * T.ρ i * x⁻¹, T.group.mul_mem (T.group.mul_mem hx (T.rho_mem_group i))
        (T.group.inv_mem hx)⟩
    have hxr : x * T.ρ i ∈ T.group := T.group.mul_mem hx (T.rho_mem_group i)
    have hi0 : 0 ≤ a + 1 + (i : ℤ) := by omega
    have hin : a + 1 + (i : ℤ) < n := by have := i.isLt; omega
    -- the moved face
    have hmove : e (D.restrictIcc a b (σS i) (gI i)) = T.face ⟨i.val + 1, by omega⟩ hxr := by
      have hval : ((D.restrictIcc a b (σS i) (gI i) : Set.Icc (D.φ a) (D.φ b)) : Q) =
          D.φ' (a + 1 + i) := by
        rw [restrictIcc_apply, gI_val i (by omega) (by have := i.isLt; omega)]
        exact D.σ_φi _ hi0 hin
      have hlo : gI ((i : ℤ) - 1) < D.restrictIcc a b (σS i) (gI i) := by
        change (gI ((i : ℤ) - 1) : Q) < _
        rw [hval, gI_val _ (by omega) (by omega),
          show a + 1 + ((i : ℤ) - 1) = a + 1 + i - 1 by ring]
        exact D.φ'_lt _ hi0 hin
      have hhi : D.restrictIcc a b (σS i) (gI i) < gI ((i : ℤ) + 1) := by
        change _ < (gI ((i : ℤ) + 1) : Q)
        rw [hval, gI_val _ (by omega) (by have := i.isLt; omega),
          show a + 1 + ((i : ℤ) + 1) = a + 1 + i + 1 by ring]
        exact D.lt_φ' _ hi0 hin
      have hne : D.restrictIcc a b (σS i) (gI i) ≠ gI i := by
        intro h
        have := congrArg Subtype.val h
        rw [hval, gI_val i (by omega) (by have := i.isLt; omega)] at this
        exact D.φ'_ne _ hi0 hin this
      have hb0 := hbase i.val (by omega)
      have hb1 := hbase (i.val + 1) (by omega)
      have hb2 := hbase (i.val + 2) (by omega)
      push_cast at hb0 hb1 hb2
      rw [show (i : ℤ) + 1 - 1 = i by ring] at hb1
      rw [show (i : ℤ) + 2 - 1 = i + 1 by ring] at hb2
      have hmem : e (D.restrictIcc a b (σS i) (gI i)) ∈
          {F | T.face ⟨i.val, by omega⟩ hx < F ∧ F < T.face ⟨i.val + 2, by omega⟩ hx} := by
        rw [← hb0, ← hb2]
        exact ⟨e.strictMono hlo, e.strictMono hhi⟩
      rw [T.between_eq (by omega) hx hxr] at hmem
      rcases hmem with h | h
      · exact absurd (e.injective (h.trans hb1.symm)) hne
      · exact h
    have := hT.eq_one_of_fix (α⁻¹ * D.resHom a b e (σS i)) (T.flagOf hx) (by
      rintro _ ⟨k, rfl⟩
      rw [RelIso.mul_apply]
      suffices hs : D.resHom a b e (σS i) (T.face k hx) = α (T.face k hx) by
        rw [hs, RelIso.inv_apply_self]
      have hαk : α (T.face k hx) = T.face k hxr := by
        rw [T.act_face]; exact T.face_congr k _ _ (by simp)
      rw [hαk]
      have hk := hbase k.val k.isLt
      change e (D.restrictIcc a b (σS i) (e.symm (T.face k hx))) = _
      rw [← hk, e.symm_apply_apply]
      by_cases hki : k.val = i.val + 1
      · have : ((k.val : ℤ) - 1) = i := by omega
        rw [this, hmove]
        exact T.face_congr' (Fin.ext hki.symm) _ _ rfl
      · have hfix : D.restrictIcc a b (σS i) (gI ((k.val : ℤ) - 1)) = gI ((k.val : ℤ) - 1) := by
          apply Subtype.ext
          rw [restrictIcc_apply, gI_val _ (by omega) (by have := k.isLt; omega)]
          exact D.σ_φ _ hi0 hin _ (by omega) (by have := k.isLt; omega) (by omega)
        rw [hfix, hk]
        exact (T.face_mul k hx hxr (T.rho_mem_sub (by omega))).symm)
    rw [inv_mul_eq_one] at this
    exact this.symm
  -- a relation of `T` acts trivially on the section, hence on `Q`
  let ρT : Fin m → T.group := fun i => ⟨T.ρ i, T.rho_mem_group i⟩
  have hρT : FreeGroup.lift ρT w = 1 := by
    have h := FreeGroup.lift_unique (f := T.ρ) (T.group.subtype.comp (FreeGroup.lift ρT))
      (fun i => by simp [ρT]) (x := w)
    rw [hw] at h
    exact Subtype.ext h
  have hcomp : D.resHom a b e (FreeGroup.lift σS w) = 1 := by
    have h1 := FreeGroup.lift_unique (f := fun i => D.resHom a b e (σS i))
      ((D.resHom a b e).comp (FreeGroup.lift σS)) (fun i => by simp) (x := w)
    have h2 := FreeGroup.lift_unique (f := fun i => D.resHom a b e (σS i))
      ((T.act.comp (MulAut.conj (⟨x, hx⟩ : T.group)).toMonoidHom).comp (FreeGroup.lift ρT))
      (fun i => by
        rw [hres i]
        simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply]
        rfl) (x := w)
    rw [MonoidHom.comp_apply] at h1
    rw [h1, ← h2]
    simp [hρT]
  have hτfix : ∀ y : Set.Icc (D.φ a) (D.φ b),
      ((FreeGroup.lift σS w : D.stab a b) : Q ≃o Q) y = y := by
    intro y
    have := congrArg (fun f : T.Face ≃o T.Face => f (e y)) hcomp
    simp only [RelIso.coe_one, id_eq] at this
    change e (D.restrictIcc a b _ (e.symm (e y))) = e y at this
    rw [e.symm_apply_apply] at this
    exact congrArg Subtype.val (e.injective this)
  have hτ : ((FreeGroup.lift σS w : D.stab a b) : Q ≃o Q) = 1 := by
    apply D.eq_one hQ
    intro j hj1 hj2
    by_cases hj : a ≤ j ∧ j ≤ b
    · exact hτfix ⟨_, hIcc j hj.1 hj.2⟩
    · rcases (show j = -1 ∨ j = n by omega) with rfl | rfl
      · exact (D.fix_ends hQ _).1
      · exact (D.fix_ends hQ _).2
  have hsub := FreeGroup.lift_unique (f := fun i : Fin m => D.σ (a + 1 + i))
    ((D.stab a b).subtype.comp (FreeGroup.lift σS)) (fun i => by simp [σS]) (x := w)
  rw [← hsub]
  exact hτ

end Distinguished

end P16c
