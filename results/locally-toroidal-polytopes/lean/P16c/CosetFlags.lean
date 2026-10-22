import Mathlib
import P16c.Polytope
import P16c.CosetPoset

/-! # Faces and flags of `P(Γ)`

Every chain of faces has a common element `z ∈ Γ` (string relations only), so
the flags are exactly the sets `{z Γ_k}`; the diamond condition and strong
flag-connectedness then follow from the intersection property. -/

namespace P16c

open scoped Pointwise

namespace StringCGroup

variable {G : Type*} [Group G] {n : ℕ} (Γ : StringCGroup G n)

lemma ip (I J : Finset (Fin n)) :
    parabolic Γ.ρ I ⊓ parabolic Γ.ρ J = parabolic Γ.ρ (I ∩ J) := Γ.stringC.2.2 I J

lemma rho_mem_parabolic {i : Fin n} {A : Finset (Fin n)} (h : i ∈ A) :
    Γ.ρ i ∈ parabolic Γ.ρ A := Subgroup.subset_closure ⟨i, h, rfl⟩

lemma rho_mem_group (i : Fin n) : Γ.ρ i ∈ Γ.group :=
  Γ.rho_mem_parabolic (Finset.mem_univ i)

lemma rho_mem_sub {i : Fin n} {k : Fin (n + 2)} (h : i.val + 1 ≠ k.val) : Γ.ρ i ∈ Γ.sub k :=
  Γ.rho_mem_parabolic (by simpa using h)

lemma rho_inv (i : Fin n) : (Γ.ρ i)⁻¹ = Γ.ρ i :=
  inv_eq_of_mul_eq_one_right (by simpa [pow_two] using Γ.rho_sq i)

/-- `ρ_i ∉ Γ_{i+1}`: the intersection property and `ρ_i ≠ 1`. -/
lemma rho_not_mem_sub (i : Fin n) {k : Fin (n + 2)} (hk : k.val = i.val + 1) :
    Γ.ρ i ∉ Γ.sub k := by
  intro h
  have hinter : ({i} ∩ Finset.univ.filter fun i' : Fin n => i'.val + 1 ≠ k.val) = ∅ := by
    ext i'; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and, not_not]
    rintro rfl; omega
  have hmem : Γ.ρ i ∈ parabolic Γ.ρ ∅ := by
    rw [← hinter, ← Γ.ip]
    exact ⟨Γ.rho_mem_parabolic (Finset.mem_singleton_self i), h⟩
  rw [parabolic_empty, Subgroup.mem_bot] at hmem
  exact Γ.ne_one i hmem

lemma mem_parabolic_singleton {i : Fin n} {x : G} (hx : x ∈ parabolic Γ.ρ {i}) :
    x = 1 ∨ x = Γ.ρ i := by
  have hx' : x ∈ Subgroup.closure ({Γ.ρ i} : Set G) := by
    simpa [parabolic] using hx
  obtain ⟨m, rfl⟩ := Subgroup.mem_closure_singleton.mp hx'
  have h2 : Γ.ρ i ^ (2 : ℤ) = 1 := by exact_mod_cast Γ.rho_sq i
  rw [zpow_eq_zpow_emod m h2]
  rcases Int.emod_two_eq_zero_or_one m with h | h <;> rw [h] <;> simp

/-- The intersection property over any finite family of the subgroups `Γ_k`. -/
lemma mem_parabolic_filter (K : Finset (Fin (n + 2))) {x : G} (hx : x ∈ Γ.group)
    (h : ∀ k ∈ K, x ∈ Γ.sub k) :
    x ∈ parabolic Γ.ρ (Finset.univ.filter fun i : Fin n => ∀ k ∈ K, i.val + 1 ≠ k.val) := by
  classical
  induction K using Finset.induction_on with
  | empty => simpa [group] using hx
  | insert k K _ ih =>
    have h1 := ih (fun k' hk' => h k' (Finset.mem_insert_of_mem hk'))
    have h2 := h k (Finset.mem_insert_self _ _)
    have hmem := (Γ.ip _ _).le ⟨h1, h2⟩
    convert hmem using 2
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_inter, forall_eq_or_imp]
    tauto

/-! ### Faces -/

lemma mem_self_coset (H : Subgroup G) (x : G) : x ∈ x • (H : Set G) := by
  rw [mem_leftCoset_iff]; simp

lemma le_def {F H : Γ.Face} : F ≤ H ↔ F.1.1 ≤ H.1.1 ∧ (F.1.2 ∩ H.1.2).Nonempty := Iff.rfl

@[simp] lemma face_type (k : Fin (n + 2)) {x : G} (hx : x ∈ Γ.group) :
    (Γ.face k hx).1.1 = k := rfl

@[simp] lemma face_set (k : Fin (n + 2)) {x : G} (hx : x ∈ Γ.group) :
    (Γ.face k hx).1.2 = x • (Γ.sub k : Set G) := rfl

lemma face_congr (k : Fin (n + 2)) {x y : G} (hx : x ∈ Γ.group) (hy : y ∈ Γ.group)
    (h : x = y) : Γ.face k hx = Γ.face k hy := by subst h; rfl

lemma face_congr' {k l : Fin (n + 2)} (hkl : k = l) {x y : G} (hx : x ∈ Γ.group)
    (hy : y ∈ Γ.group) (h : x = y) : Γ.face k hx = Γ.face l hy := by subst hkl; subst h; rfl

lemma face_eq_iff {k l : Fin (n + 2)} {x y : G} (hx : x ∈ Γ.group) (hy : y ∈ Γ.group) :
    Γ.face k hx = Γ.face l hy ↔ k = l ∧ x⁻¹ * y ∈ Γ.sub k := by
  constructor
  · intro h
    have hk : k = l := congrArg (fun F : Γ.Face => F.1.1) h
    subst hk
    exact ⟨rfl, (leftCoset_eq_iff _).mp (congrArg (fun F : Γ.Face => F.1.2) h)⟩
  · rintro ⟨rfl, h⟩
    exact Subtype.ext (Prod.ext rfl ((leftCoset_eq_iff _).mpr h))

lemma face_mul (k : Fin (n + 2)) {x b : G} (hx : x ∈ Γ.group) (hxb : x * b ∈ Γ.group)
    (hb : b ∈ Γ.sub k) : Γ.face k hxb = Γ.face k hx := by
  rw [face_eq_iff]
  exact ⟨rfl, by simpa [mul_assoc] using hb⟩

lemma exists_face (F : Γ.Face) : ∃ x, ∃ hx : x ∈ Γ.group, F = Γ.face F.1.1 hx := by
  obtain ⟨x, hx, h⟩ := F.2
  exact ⟨x, hx, Subtype.ext (Prod.ext rfl h)⟩

lemma face_eq_of_mem (F : Γ.Face) {w : G} (hw : w ∈ F.1.2) (hwg : w ∈ Γ.group) :
    F = Γ.face F.1.1 hwg := by
  obtain ⟨x, hx, hF⟩ := Γ.exists_face F
  rw [hF] at hw ⊢
  rw [face_eq_iff]
  exact ⟨rfl, (mem_leftCoset_iff x).mp hw⟩

lemma face_le_face {j k : Fin (n + 2)} (h : j ≤ k) {x : G} (hx : x ∈ Γ.group) :
    Γ.face j hx ≤ Γ.face k hx :=
  ⟨h, x, mem_self_coset _ x, mem_self_coset _ x⟩

lemma eq_of_le_of_type_eq {F H : Γ.Face} (h : F ≤ H) (ht : F.1.1 = H.1.1) : F = H :=
  le_antisymm h ⟨ht.ge, by rw [Set.inter_comm]; exact h.2⟩

lemma type_le_of_le {F H : Γ.Face} (h : F ≤ H) : F.1.1 ≤ H.1.1 := h.1

lemma type_lt_of_lt {F H : Γ.Face} (h : F < H) : F.1.1 < H.1.1 :=
  lt_of_le_of_ne h.le.1 (fun ht => h.ne (Γ.eq_of_le_of_type_eq h.le ht))

lemma chain_type_eq {C : Set Γ.Face} (hC : IsChain (· ≤ ·) C) {F H : Γ.Face}
    (hF : F ∈ C) (hH : H ∈ C) (ht : F.1.1 = H.1.1) : F = H := by
  by_cases hFH : F = H
  · exact hFH
  rcases hC hF hH hFH with h | h
  · exact Γ.eq_of_le_of_type_eq h ht
  · exact (Γ.eq_of_le_of_type_eq h ht.symm).symm

/-- **Every chain has a common element.** Uses only the string relations. -/
theorem chain_common {C : Set Γ.Face} (hC : IsChain (· ≤ ·) C) :
    ∃ z, ∃ hz : z ∈ Γ.group, ∀ F ∈ C, F = Γ.face F.1.1 hz := by
  classical
  suffices h : ∀ m : ℕ, ∃ z, ∃ hz : z ∈ Γ.group,
      ∀ F ∈ C, F.1.1.val < m → F = Γ.face F.1.1 hz by
    obtain ⟨z, hz, h⟩ := h (n + 2)
    exact ⟨z, hz, fun F hF => h F hF F.1.1.isLt⟩
  intro m
  induction m with
  | zero => exact ⟨1, Γ.group.one_mem, fun F _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨z, hz, hzC⟩ := ih
    by_cases hH : ∃ H ∈ C, H.1.1.val = m
    swap
    · push Not at hH
      exact ⟨z, hz, fun F hF hlt => hzC F hF (by have := hH F hF; omega)⟩
    obtain ⟨H, hHC, hHm⟩ := hH
    obtain ⟨y, hy, hHy⟩ := Γ.exists_face H
    have htop : ∀ F ∈ C, F.1.1.val = m → F = H := fun F hF hFm =>
      Γ.chain_type_eq hC hF hHC (Fin.ext (hFm.trans hHm.symm))
    let T : Finset (Fin (n + 2)) :=
      Finset.univ.filter fun t => t.val < m ∧ ∃ F ∈ C, F.1.1 = t
    by_cases hT : T.Nonempty
    swap
    · refine ⟨y, hy, fun F hF hlt => ?_⟩
      have hFm : F.1.1.val = m := by
        by_contra hne
        have hmem : F.1.1 ∈ T := by
          simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨by omega, F, hF, rfl⟩
        exact hT ⟨F.1.1, hmem⟩
      have hFH := htop F hF hFm
      subst hFH
      exact hHy
    · set j := T.max' hT with hj
      obtain ⟨hjm, Fj, hFjC, hFjt⟩ : j.val < m ∧ ∃ F ∈ C, F.1.1 = j := by
        have := T.max'_mem hT
        simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using this
      have hFj : Fj = Γ.face j hz := by
        have := hzC Fj hFjC (by rw [hFjt]; omega)
        rw [this]; exact Γ.face_congr _ _ _ rfl |>.trans (by rw [hFjt])
      have hle : Fj ≤ H := by
        have hne : Fj ≠ H := fun h => by
          have := congrArg (fun F : Γ.Face => F.1.1.val) h
          simp only [hFjt] at this; omega
        rcases hC hFjC hHC hne with h | h
        · exact h
        · have := Fin.le_iff_val_le_val.mp h.1; rw [hFjt] at this; omega
      rw [hFj, hHy, le_def] at hle
      obtain ⟨w, hwz, hwy⟩ := hle.2
      have hzw : z⁻¹ * w ∈ Γ.sub j := (mem_leftCoset_iff z).mp hwz
      obtain ⟨a, ha, b, hb, hab, hcomm⟩ := Γ.sub_factor hzw
      have hbg : b ∈ Γ.group := Γ.parabolic_le_group _ hb
      have hzb : z * b ∈ Γ.group := Γ.group.mul_mem hz hbg
      refine ⟨z * b, hzb, fun F hF hlt => ?_⟩
      by_cases hFm : F.1.1.val = m
      · rw [htop F hF hFm, hHy, face_eq_iff]
        refine ⟨rfl, ?_⟩
        have haM : a ∈ Γ.sub H.1.1 := Γ.parabolic_le_sub (by
          intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi; omega) ha
        have hyw : y⁻¹ * w ∈ Γ.sub H.1.1 := (mem_leftCoset_iff y).mp hwy
        have hw : w = z * (b * a) := by rw [← hcomm, ← hab]; group
        have : y⁻¹ * (z * b) = (y⁻¹ * w) * a⁻¹ := by rw [hw]; group
        rw [this]
        exact Γ.sub _ |>.mul_mem hyw (Γ.sub _ |>.inv_mem haM)
      · have hFT : F.1.1 ∈ T := by
          simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨by omega, F, hF, rfl⟩
        have hFj' : F.1.1 ≤ j := T.le_max' _ hFT
        rw [hzC F hF (by omega)]
        refine (Γ.face_mul _ hz hzb (Γ.parabolic_le_sub ?_ hb)).symm
        intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        have := Fin.le_iff_val_le_val.mp hFj'; omega

/-! ### Flags -/

/-- The flag `Φ_z = {z Γ_k}`. -/
def flagSet {z : G} (hz : z ∈ Γ.group) : Set Γ.Face := Set.range fun k => Γ.face k hz

lemma isChain_flagSet {z : G} (hz : z ∈ Γ.group) : IsChain (· ≤ ·) (Γ.flagSet hz) := by
  rintro _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ -
  rcases le_total j k with h | h
  · exact Or.inl (Γ.face_le_face h hz)
  · exact Or.inr (Γ.face_le_face h hz)

/-- `Φ_z` as a flag. -/
def flagOf {z : G} (hz : z ∈ Γ.group) : Flag Γ.Face where
  carrier := Γ.flagSet hz
  Chain' := Γ.isChain_flagSet hz
  max_chain' := by
    intro s hs hsub
    apply le_antisymm hsub
    intro F hF
    obtain ⟨x, hx, hFx⟩ := Γ.exists_face F
    have hk : Γ.face F.1.1 hz ∈ s := hsub ⟨F.1.1, rfl⟩
    refine ⟨F.1.1, ?_⟩
    exact Γ.chain_type_eq hs hk hF rfl

lemma coe_flagOf {z : G} (hz : z ∈ Γ.group) : (Γ.flagOf hz : Set Γ.Face) = Γ.flagSet hz := rfl

lemma flagOf_congr {x y : G} (hx : x ∈ Γ.group) (hy : y ∈ Γ.group) (h : x = y) :
    Γ.flagOf hx = Γ.flagOf hy := by subst h; rfl

/-- Every flag is some `Φ_z`. -/
theorem exists_flagOf (Φ : Flag Γ.Face) : ∃ z, ∃ hz : z ∈ Γ.group, Φ = Γ.flagOf hz := by
  obtain ⟨z, hz, h⟩ := Γ.chain_common Φ.chain_le
  refine ⟨z, hz, ?_⟩
  have hsub : (Φ : Set Γ.Face) ⊆ Γ.flagSet hz := fun F hF => ⟨F.1.1, (h F hF).symm⟩
  exact SetLike.coe_injective (Φ.max_chain' (Γ.isChain_flagSet hz) hsub)

lemma face_injective {z : G} (hz : z ∈ Γ.group) : Function.Injective fun k => Γ.face k hz :=
  fun j k h => ((Γ.face_eq_iff hz hz).mp h).1

theorem flag_ncard (Φ : Flag Γ.Face) : (Φ : Set Γ.Face).ncard = n + 2 := by
  obtain ⟨z, hz, rfl⟩ := Γ.exists_flagOf Φ
  rw [coe_flagOf, flagSet, Set.ncard_range_of_injective (Γ.face_injective hz)]
  simp

/-! ### The diamond condition -/

/-- The faces strictly between `z Γ_j` and `z Γ_{j+2}` are `z Γ_{j+1}` and `z ρ_j Γ_{j+1}`. -/
theorem between_eq {j : ℕ} (hj : j + 2 < n + 2) {z : G} (hz : z ∈ Γ.group)
    (hzr : z * Γ.ρ ⟨j, by omega⟩ ∈ Γ.group) :
    {H | Γ.face ⟨j, by omega⟩ hz < H ∧ H < Γ.face ⟨j + 2, hj⟩ hz} =
      {Γ.face ⟨j + 1, by omega⟩ hz, Γ.face ⟨j + 1, by omega⟩ hzr} := by
  let i : Fin n := ⟨j, by omega⟩
  have hρj : Γ.ρ i ∈ Γ.sub ⟨j, by omega⟩ := Γ.rho_mem_sub (by simp [i])
  have hρj2 : Γ.ρ i ∈ Γ.sub ⟨j + 2, hj⟩ := Γ.rho_mem_sub (by simp [i])
  have hne : Γ.face ⟨j + 1, by omega⟩ hz ≠ Γ.face ⟨j + 1, by omega⟩ hzr := by
    rw [Ne, face_eq_iff]
    rintro ⟨-, h⟩
    exact Γ.rho_not_mem_sub i (k := ⟨j + 1, by omega⟩) rfl (by simpa using h)
  have hlt : ∀ {a b : Fin (n + 2)} {x y : G} (hx : x ∈ Γ.group) (hy : y ∈ Γ.group),
      a < b → (x • (Γ.sub a : Set G) ∩ y • (Γ.sub b : Set G)).Nonempty →
        Γ.face a hx < Γ.face b hy := fun hx hy hab hn =>
    lt_of_le_of_ne ⟨hab.le, hn⟩ (fun h => hab.ne ((Γ.face_eq_iff hx hy).mp h).1)
  ext H
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have hC : IsChain (· ≤ ·) ({Γ.face ⟨j, by omega⟩ hz, H, Γ.face ⟨j + 2, hj⟩ hz} :
        Set Γ.Face) := by
      have h3 := h1.le.trans h2.le
      intro a ha b hb _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        simp only [le_refl, true_or, h1.le, h2.le, h3, or_true]
    obtain ⟨z', hz', hc⟩ := Γ.chain_common hC
    have hF := hc _ (Set.mem_insert _ _)
    have hH := hc H (by simp)
    have hK := hc (Γ.face ⟨j + 2, hj⟩ hz) (by simp)
    simp only [face_type] at hF hK
    rw [face_eq_iff] at hF hK
    have htype : H.1.1 = ⟨j + 1, by omega⟩ := by
      have a : j < H.1.1.val := Γ.type_lt_of_lt h1
      have b : H.1.1.val < j + 2 := Γ.type_lt_of_lt h2
      exact Fin.ext (show H.1.1.val = j + 1 by omega)
    have hw : z⁻¹ * z' ∈ parabolic Γ.ρ
        ((Finset.univ.filter fun i' : Fin n => i'.val + 1 ≠ j ∧ i'.val + 1 ≠ j + 2 ∧ i' ≠ i) ∪
          {i}) := by
      have := (Γ.ip _ _).le ⟨hF.2, hK.2⟩
      convert this using 2
      ext i'
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton, Finset.mem_inter, i]
      constructor
      · rintro (⟨h1, h2, -⟩ | rfl)
        · exact ⟨h1, h2⟩
        · exact ⟨fun h => by simp [i] at h, fun h => by simp [i] at h⟩
      · rintro ⟨ha, hb⟩
        by_cases h : i' = ⟨j, by omega⟩
        · exact Or.inr h
        · exact Or.inl ⟨ha, hb, h⟩
    obtain ⟨a, ha, b, hb, hab, hcomm⟩ := Γ.mem_union_factor (by
      intro i' hi' k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hi' hk
      subst hk
      have : i'.val ≠ j := fun h => hi'.2.2 (Fin.ext h)
      exact Γ.commute_rho (by simp only [i]; omega)) hw
    have haS : a ∈ Γ.sub ⟨j + 1, by omega⟩ := Γ.parabolic_le_sub (by
      intro i' hi'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi'
      have : i'.val ≠ j := fun h => hi'.2.2 (Fin.ext h)
      simp only; omega) ha
    rw [hH, Γ.face_congr _ _ hz' rfl]
    have hz'eq : z' = z * b * a := by
      rw [mul_assoc, ← hcomm, ← hab]; group
    rcases Γ.mem_parabolic_singleton hb with rfl | rfl
    · left
      rw [face_eq_iff]
      refine ⟨htype, ?_⟩
      rw [htype, hz'eq]; simpa using Γ.sub _ |>.inv_mem haS
    · right
      rw [face_eq_iff]
      refine ⟨htype, ?_⟩
      rw [htype, hz'eq]
      have e : (z * Γ.ρ i * a)⁻¹ * (z * Γ.ρ ⟨j, by omega⟩) = a⁻¹ := by simp only [i]; group
      rw [e]; exact Γ.sub _ |>.inv_mem haS
  · rintro (rfl | rfl)
    · exact ⟨hlt hz hz (by simp [Fin.lt_def]) ⟨z, mem_self_coset _ z,
        mem_self_coset _ z⟩, hlt hz hz (by simp [Fin.lt_def])
          ⟨z, mem_self_coset _ z, mem_self_coset _ z⟩⟩
    · refine ⟨hlt hz hzr (by simp [Fin.lt_def]) ⟨z * Γ.ρ i, ?_,
        mem_self_coset _ _⟩, hlt hzr hz (by simp [Fin.lt_def])
          ⟨z * Γ.ρ i, mem_self_coset _ _, ?_⟩⟩
      · rw [mem_leftCoset_iff]; simpa using hρj
      · rw [mem_leftCoset_iff]; simpa using hρj2

end StringCGroup

end P16c
