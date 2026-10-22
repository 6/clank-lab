import Mathlib
import P16c.PolytopeAssembly
import P16c.TorusStab
import P16c.TorusFaces

/-! # The geometric toroidal map is the coset poset of `[4,4]_(s,0)`

`x Γ_k ↦ φ(x)(B_k)`, for the base faces `B_k` (empty, vertex `0`, edge
`{0,(1,0)}`, square `{0,(1,0),(0,1),(1,1)}`, everything), is an order
isomorphism `P([4,4]_(s,0)) ≃o {4,4}_(s,0)` preserving rank. -/

namespace P16c.Torus

open Toroid

variable {s : ℕ}

/-- The base faces `B_k`, `k = 0, …, 4` (rank `k - 1`). -/
def base (s : ℕ) : Fin 5 → Set (TorusVertex s) := ![∅, {(0, 0)}, E s, Q s, Set.univ]

section
variable (hs : Odd s) (hs3 : 3 ≤ s)

lemma toroidC_group : (toroidC s hs hs3).group = ⊤ := by
  change Subgroup.closure (Toroid.r s '' ((Finset.univ : Finset (Fin 3)) : Set (Fin 3))) = ⊤
  rw [Finset.coe_univ, Set.image_univ]
  exact PresentedGroup.closure_range_of _

lemma mem_group (x : G s) : x ∈ (toroidC s hs hs3).group := by
  rw [toroidC_group]; trivial

lemma rho_mem {i : Fin 3} {k : Fin 5} (h : i.val + 1 ≠ k.val) : Toroid.r s i ∈ (toroidC s hs hs3).sub k :=
  (toroidC s hs hs3).rho_mem_sub h

lemma sub_eq_top {k : Fin 5} (hk : k = 0 ∨ k = 4) : (toroidC s hs hs3).sub k = ⊤ := by
  rw [eq_top_iff, ← PresentedGroup.closure_range_of (Toroid.rels s), Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  apply rho_mem
  rcases hk with rfl | rfl <;> simp; omega

lemma gen_base (i : Fin 3) (k : Fin 5) (h : i.val + 1 ≠ k.val) :
    phi s (Toroid.r s i) '' base s k = base s k := by
  fin_cases i <;> fin_cases k <;> (try simp at h) <;>
    (try exact Set.image_univ_of_surjective (Equiv.surjective _)) <;>
    simp [base, E, Q, Set.image_insert_eq]
  all_goals try exact Set.pair_comm _ _
  all_goals try (ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)

/-- `Γ_k` stabilizes `B_k`. -/
lemma sub_base {k : Fin 5} {g : G s} (hg : g ∈ (toroidC s hs hs3).sub k) :
    phi s g '' base s k = base s k := by
  induction hg using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi
    exact gen_base i k hi
  | inv_mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi
    have : (Toroid.r s i)⁻¹ = Toroid.r s i := inv_eq_of_mul_eq_one_right (r_mul_self s i)
    change phi s (Toroid.r s i)⁻¹ '' _ = _
    rw [this]; exact gen_base i k hi
  | one => simp
  | mul x y _ _ ihx ihy => rw [map_mul, Equiv.Perm.coe_mul, Set.image_comp, ihy, ihx]

/-- `φ(x)(B_k)` for the face `x Γ_k`. -/
noncomputable def psi (F : (toroidC s hs hs3).Face) : Set (TorusVertex s) :=
  phi s F.2.choose '' base s F.1.1

lemma psi_face (k : Fin 5) {x : G s} (hx : x ∈ (toroidC s hs hs3).group) :
    psi hs hs3 ((toroidC s hs hs3).face k hx) = phi s x '' base s k := by
  set F := (toroidC s hs hs3).face k hx
  obtain ⟨-, hy⟩ := F.2.choose_spec
  have hxy : x⁻¹ * F.2.choose ∈ (toroidC s hs hs3).sub k :=
    (leftCoset_eq_iff _).mp (by simpa [F] using hy)
  change phi s F.2.choose '' base s k = _
  rw [show F.2.choose = x * (x⁻¹ * F.2.choose) by group, map_mul, Equiv.Perm.coe_mul,
    Set.image_comp, sub_base hs hs3 hxy]

lemma base_mem (k : Fin 5) : base s k ∈ torusFaces s := by
  fin_cases k
  · exact mem_torusFaces.mpr (Or.inl rfl)
  · exact mem_torusFaces.mpr (Or.inr (Or.inr (Or.inl ⟨(0, 0), rfl⟩)))
  · exact hface (0, 0) (by simp [base, E])
  · exact qface (0, 0) (by simp [base, Q])
  · exact mem_torusFaces.mpr (Or.inr (Or.inl rfl))

lemma psi_mem (F : (toroidC s hs hs3).Face) : psi hs hs3 F ∈ torusFaces s := by
  obtain ⟨x, hx, hF⟩ := (toroidC s hs hs3).exists_face F
  rw [hF, psi_face]
  exact phi_image_mem x (base_mem _)

lemma base_mono {j k : Fin 5} (h : j ≤ k) : base s j ⊆ base s k := by
  fin_cases j <;> fin_cases k <;> simp at h <;> simp [base, E, Q, Set.insert_subset_iff]

/-- Order reflection, at the base: if `φ(g)(B_j) ⊆ B_k` then `j ≤ k` and the cosets
`g Γ_j` and `Γ_k` meet. -/
lemma reflect {j k : Fin 5} {g : G s} (h : phi s g '' base s j ⊆ base s k) :
    j ≤ k ∧ ∃ h' ∈ (toroidC s hs hs3).sub j, g * h' ∈ (toroidC s hs hs3).sub k := by
  haveI : NeZero s := ⟨by omega⟩
  have f1 := one_ne_zero' hs3
  have f2 := two_ne_zero' hs3
  have f3 := two_ne_one' hs3
  have top0 := sub_eq_top hs hs3 (k := 0) (Or.inl rfl)
  have top4 := sub_eq_top hs hs3 (k := 4) (Or.inr rfl)
  have m : ∀ {i : Fin 3} {l : Fin 5}, i.val + 1 ≠ l.val → Toroid.r s i ∈ (toroidC s hs hs3).sub l :=
    fun h => rho_mem hs hs3 h
  -- the image of the whole map is the whole map, which no proper base face contains
  have huniv : ∀ l : Fin 5, l ≠ 4 → ¬ phi s g '' Set.univ ⊆ base s l := by
    intro l hl hsub
    have : ((2, 2) : TorusVertex s) ∈ base s l := hsub (by
      rw [Set.image_univ_of_surjective (Equiv.surjective _)]; trivial)
    fin_cases l <;> simp [base, E, Q, f2, f3] at this hl
  have inj := (phi s g).injective
  have c0 : ∀ l : Fin 5, (0 : Fin 5) ≤ l ∧
      ∃ h' ∈ (toroidC s hs hs3).sub 0, g * h' ∈ (toroidC s hs hs3).sub l :=
    fun l => ⟨Fin.zero_le _, g⁻¹, by rw [top0]; trivial, by simp⟩
  have c4 : ∀ l : Fin 5, l ≤ 4 ∧
      ∃ h' ∈ (toroidC s hs hs3).sub l, g * h' ∈ (toroidC s hs hs3).sub 4 :=
    fun l => ⟨Fin.le_last _, 1, Subgroup.one_mem _, by rw [top4]; trivial⟩
  have v1 : ((0, 0) : TorusVertex s) ∈ base s 1 := rfl
  have v2 : ((0, 0) : TorusVertex s) ∈ base s 2 := by simp [base, E]
  have w2 : ((1, 0) : TorusVertex s) ∈ base s 2 := by simp [base, E]
  have v3 : ((0, 0) : TorusVertex s) ∈ base s 3 := by simp [base, Q]
  have w3 : ((1, 0) : TorusVertex s) ∈ base s 3 := by simp [base, Q]
  have u3 : ((0, 1) : TorusVertex s) ∈ base s 3 := by simp [base, Q]
  have empty : ∀ p, p ∉ base s 0 := fun p => by simp [base]
  have two : ∀ l : Fin 5, (phi s g) '' base s l ⊆ base s 1 →
      ((0, 0) : TorusVertex s) ∈ base s l → ((1, 0) : TorusVertex s) ∈ base s l → False := by
    intro l hl a b
    have a' := image_sub hl a
    have b' := image_sub hl b
    simp only [base, Matrix.cons_val, Set.mem_singleton_iff] at a' b'
    have := inj (a'.trans b'.symm)
    simp [f1.symm] at this
  fin_cases j <;> fin_cases k
  · exact c0 _
  · exact c0 _
  · exact c0 _
  · exact c0 _
  · exact c0 _
  · exact absurd (image_sub h v1) (empty _)
  · exact ⟨by decide, 1, Subgroup.one_mem _, by
      simpa using stab1 _ (m (by decide)) (m (by decide)) h⟩
  · exact ⟨by decide, reach12 _ _ (m (by decide)) (m (by decide)) (m (by decide))
      (image_sub h v1)⟩
  · exact ⟨by decide, reach13 _ _ (m (by decide)) (m (by decide)) (m (by decide)) (m (by decide))
      (image_sub h v1)⟩
  · exact c4 _
  · exact absurd (image_sub h v2) (empty _)
  · exact (two 2 h v2 w2).elim
  · exact ⟨by decide, 1, Subgroup.one_mem _, by
      simpa using stab2 _ hs3 (m (by decide)) (m (by decide)) h⟩
  · exact ⟨by decide, reach23 _ hs3 _ (m (by decide)) (m (by decide)) (m (by decide)) h⟩
  · exact c4 _
  · exact absurd (image_sub h v3) (empty _)
  · exact (two 3 h v3 w3).elim
  · exfalso
    have a := image_sub h v3
    have b := image_sub h w3
    have c := image_sub h u3
    simp only [base, E] at a b c
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c
    all_goals first
      | (have := inj (a.trans b.symm); simp [f1.symm] at this)
      | (have := inj (a.trans c.symm); simp [f1.symm] at this)
      | (have := inj (b.trans c.symm); simp [f1.symm] at this)
  · exact ⟨by decide, 1, Subgroup.one_mem _, by
      simpa using stab3 _ hs3 (m (by decide)) (m (by decide)) h⟩
  · exact c4 _
  · exact absurd h (huniv _ (by decide))
  · exact absurd h (huniv _ (by decide))
  · exact absurd h (huniv _ (by decide))
  · exact absurd h (huniv _ (by decide))
  · exact c4 _

lemma psi_le_iff (F H : (toroidC s hs hs3).Face) : psi hs hs3 F ⊆ psi hs hs3 H ↔ F ≤ H := by
  obtain ⟨x, hx, hF⟩ := (toroidC s hs hs3).exists_face F
  obtain ⟨y, hy, hH⟩ := (toroidC s hs hs3).exists_face H
  constructor
  · intro hsub
    rw [hF, hH, psi_face, psi_face] at hsub
    have h' : phi s (y⁻¹ * x) '' base s F.1.1 ⊆ base s H.1.1 := by
      rw [map_mul, Equiv.Perm.coe_mul, Set.image_comp]
      intro p hp
      obtain ⟨q, hq, rfl⟩ := hp
      obtain ⟨t, ht, he⟩ := hsub hq
      rw [← he]
      simpa using ht
    obtain ⟨hjk, h', hh', hm⟩ := reflect hs hs3 h'
    rw [hF, hH]
    refine ⟨hjk, x * h', ?_, ?_⟩
    · simpa using Set.smul_mem_smul_set (a := x) hh'
    · have : x * h' = y * (y⁻¹ * x * h') := by group
      rw [StringCGroup.face_set, this]
      exact Set.smul_mem_smul_set hm
  · intro hle
    obtain ⟨w, hwF, hwH⟩ := hle.2
    have hw := mem_group hs hs3 w
    rw [(toroidC s hs hs3).face_eq_of_mem F hwF hw, (toroidC s hs hs3).face_eq_of_mem H hwH hw,
      psi_face, psi_face]
    exact Set.image_mono (base_mono hle.1)

lemma psi_surj (S : Set (TorusVertex s)) (hS : S ∈ torusFaces s) :
    ∃ F : (toroidC s hs hs3).Face, psi hs hs3 F = S := by
  haveI : NeZero s := ⟨by omega⟩
  have g := mem_group hs hs3
  rcases mem_torusFaces.mp hS with rfl | rfl | ⟨v, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩
  · exact ⟨_, (psi_face hs hs3 0 (g 1)).trans (by simp [base])⟩
  · exact ⟨_, (psi_face hs hs3 4 (g 1)).trans (by simp [base])⟩
  · refine ⟨_, (psi_face hs hs3 1 (g (tr s v.1 v.2))).trans ?_⟩
    simp [base, phi_tr]
  · refine ⟨_, (psi_face hs hs3 2 (g (tr s v.1 v.2))).trans ?_⟩
    change phi s _ '' E s = _
    rw [E, image_pair, phi_tr, phi_tr]
    simp [add_comm, Prod.mk_zero_zero]
  · refine ⟨_, (psi_face hs hs3 2 (g (tr s v.1 v.2 * Toroid.r s 1))).trans ?_⟩
    change phi s _ '' E s = _
    rw [E, image_pair, map_mul, Equiv.Perm.mul_apply,
      Equiv.Perm.mul_apply, phi_tr, phi_tr]
    simp [add_comm, Prod.mk_zero_zero]
  · refine ⟨_, (psi_face hs hs3 3 (g (tr s v.1 v.2))).trans ?_⟩
    change phi s _ '' Q s = _
    rw [Q, image_quad, phi_tr, phi_tr, phi_tr, phi_tr]
    simp [add_comm, Prod.mk_zero_zero]

include hs3 in
lemma rank_image (k : Fin 5) (x : G s) :
    (if phi s x '' base s k = Set.univ then (3 : ℤ)
      else if (phi s x '' base s k).ncard = 4 then 2
      else ((phi s x '' base s k).ncard : ℤ) - 1) = (k.val : ℤ) - 1 := by
  have f1 := one_ne_zero' hs3
  have f2 := two_ne_zero' hs3
  have f3 := two_ne_one' hs3
  have hinj := (phi s x).injective
  have hne : ∀ l : Fin 5, l ≠ 4 → phi s x '' base s l ≠ Set.univ := by
    intro l hl he
    have : ((2, 2) : TorusVertex s) ∈ base s l := by
      have h22 : phi s x (2, 2) ∈ phi s x '' base s l := by rw [he]; trivial
      obtain ⟨q, hq, hq'⟩ := h22
      rwa [hinj hq'] at hq
    fin_cases l <;> simp [base, E, Q, f2, f3] at this hl
  rw [Set.ncard_image_of_injective _ hinj]
  fin_cases k
  · rw [if_neg (hne _ (by decide))]; simp [base]
  · rw [if_neg (hne _ (by decide))]; simp [base]
  · rw [if_neg (hne _ (by decide))]
    have : (base s 2).ncard = 2 := Set.ncard_pair (by simp [f1.symm])
    show (if (base s 2).ncard = 4 then (2 : ℤ) else ((base s 2).ncard : ℤ) - 1) = ((2 : Fin 5).val : ℤ) - 1
    rw [this]; norm_num
  · rw [if_neg (hne _ (by decide))]
    have : (base s 3).ncard = 4 := by
      change ({(0, 0), (1, 0), (0, 1), (1, 1)} : Set (TorusVertex s)).ncard = 4
      rw [Set.ncard_insert_of_notMem (by simp [f1.symm]), Set.ncard_insert_of_notMem
        (by simp [f1.symm]), Set.ncard_pair (by simp [f1.symm])]
    show (if (base s 3).ncard = 4 then (2 : ℤ) else ((base s 3).ncard : ℤ) - 1) = ((3 : Fin 5).val : ℤ) - 1
    rw [if_pos this]; norm_num
  · rw [if_pos (by simp [base, Set.image_univ_of_surjective (Equiv.surjective _)])]; norm_num

lemma psi_rank (F : (toroidC s hs hs3).Face) :
    torusRank s ⟨psi hs hs3 F, psi_mem hs hs3 F⟩ = (toroidC s hs hs3).rank F := by
  obtain ⟨x, hx, hF⟩ := (toroidC s hs hs3).exists_face F
  have hrank : (toroidC s hs hs3).rank F = (F.1.1.val : ℤ) - 1 := rfl
  have hpsi : psi hs hs3 F = phi s x '' base s F.1.1 := by rw [hF, psi_face]; rfl
  simp only [torusRank, hrank, hpsi]
  exact rank_image hs3 _ x

/-- The coset poset of `[4,4]_(s,0)` is the geometric toroidal map. -/
noncomputable def toroidIso : ToroidalMap s hs hs3 ≃o TorusMap s :=
  OrderIso.ofSurjective
    (OrderEmbedding.ofMapLEIff (fun F => ⟨psi hs hs3 F, psi_mem hs hs3 F⟩)
      (fun F H => psi_le_iff hs hs3 F H))
    (fun S => by
      obtain ⟨F, hF⟩ := psi_surj hs hs3 S S.2
      exact ⟨F, Subtype.ext hF⟩)

lemma toroidIso_rank (F : ToroidalMap s hs hs3) :
    torusRank s (toroidIso hs hs3 F) = (toroidC s hs hs3).rank F := psi_rank hs hs3 F

end

end P16c.Torus
