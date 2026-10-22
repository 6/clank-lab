import Mathlib
import P16c.CosetFlags

/-! # `P(Γ)` is a polytope (ARP 2E11, first part) -/

namespace P16c

open scoped Pointwise

namespace StringCGroup

variable {G : Type*} [Group G] {n : ℕ} (Γ : StringCGroup G n)

lemma mem_group_of_mem (F : Γ.Face) {w : G} (hw : w ∈ F.1.2) : w ∈ Γ.group := by
  obtain ⟨x, hx, hF⟩ := F.2
  rw [hF, mem_leftCoset_iff] at hw
  have := Γ.group.mul_mem hx (Γ.sub_le_group _ hw)
  simpa using this

lemma sub_eq_group {k : Fin (n + 2)} (hk : k.val = 0 ∨ k.val = n + 1) : Γ.sub k = Γ.group := by
  unfold sub group
  congr 1
  apply Finset.filter_true_of_mem
  intro i _; omega

/-- Adjacent flags: `Φ_z` and `Φ_{zρ_i}` differ exactly in the face of type `i + 1`. -/
lemma flagOf_diff (i : Fin n) {z : G} (hz : z ∈ Γ.group) (hzr : z * Γ.ρ i ∈ Γ.group) :
    (Γ.flagOf hz : Set Γ.Face) \ Γ.flagOf hzr = {Γ.face ⟨i.val + 1, by omega⟩ hz} := by
  ext F
  simp only [coe_flagOf, flagSet, Set.mem_sdiff, Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨k, rfl⟩, hnot⟩
    by_contra hk
    apply hnot
    refine ⟨k, Γ.face_mul k hz hzr (Γ.rho_mem_sub ?_)⟩
    intro h
    have : k = ⟨i.val + 1, by omega⟩ := Fin.ext h.symm
    rw [this] at hk
    exact hk rfl
  · rintro rfl
    refine ⟨⟨_, rfl⟩, ?_⟩
    rintro ⟨k, hk⟩
    obtain ⟨rfl, h⟩ := (Γ.face_eq_iff hzr hz).mp hk
    exact Γ.rho_not_mem_sub i rfl (by simpa using h)

lemma flagOf_adjacent (i : Fin n) {z : G} (hz : z ∈ Γ.group) (hzr : z * Γ.ρ i ∈ Γ.group) :
    FlagAdjacent (Γ.flagOf hz) (Γ.flagOf hzr) :=
  ⟨_, Γ.flagOf_diff i hz hzr⟩

/-- The walk along the prefixes of a word in `ρ_i`, `i ∈ S`, keeps every face whose
type is fixed by all of these generators. -/
lemma path (S : Finset (Fin n)) {z : G} (hz : z ∈ Γ.group) {w : G}
    (hw : w ∈ Subgroup.closure (Γ.ρ '' (S : Set (Fin n)))) :
    Relation.ReflTransGen (fun A B : Flag Γ.Face => FlagAdjacent A B ∧
        ∀ k : Fin (n + 2), (∀ i ∈ S, i.val + 1 ≠ k.val) → Γ.face k hz ∈ B)
      (Γ.flagOf hz) (Γ.flagOf (Γ.group.mul_mem hz (Γ.parabolic_le_group S hw))) := by
  have step : ∀ x (hx : x ∈ Subgroup.closure (Γ.ρ '' (S : Set (Fin n)))) (i : Fin n),
      i ∈ S → ∀ t (ht : t ∈ Γ.group), t = z * (x * Γ.ρ i) →
      Relation.ReflTransGen (fun A B : Flag Γ.Face => FlagAdjacent A B ∧
        ∀ k : Fin (n + 2), (∀ i ∈ S, i.val + 1 ≠ k.val) → Γ.face k hz ∈ B)
        (Γ.flagOf hz) (Γ.flagOf (Γ.group.mul_mem hz (Γ.parabolic_le_group S hx))) →
      Relation.ReflTransGen (fun A B : Flag Γ.Face => FlagAdjacent A B ∧
        ∀ k : Fin (n + 2), (∀ i ∈ S, i.val + 1 ≠ k.val) → Γ.face k hz ∈ B)
        (Γ.flagOf hz) (Γ.flagOf ht) := by
    intro x hx i hi t ht hte ih
    have hzx : z * x ∈ Γ.group := Γ.group.mul_mem hz (Γ.parabolic_le_group S hx)
    have hzxr : z * x * Γ.ρ i ∈ Γ.group := Γ.group.mul_mem hzx (Γ.rho_mem_group i)
    refine ih.tail ⟨?_, ?_⟩
    · rw [Γ.flagOf_congr ht hzxr (by rw [hte, mul_assoc])]
      exact Γ.flagOf_adjacent i hzx hzxr
    · intro k hk
      have hxr : x * Γ.ρ i ∈ Γ.sub k := Γ.parabolic_le_sub hk
        ((parabolic Γ.ρ S).mul_mem hx (Γ.rho_mem_parabolic hi))
      refine ⟨k, ?_⟩
      have := Γ.face_mul k hz (by rw [← mul_assoc]; exact hzxr) hxr
      rw [← this]
      exact Γ.face_congr k _ _ hte
  induction hw using Subgroup.closure_induction_right with
  | one => rw [Γ.flagOf_congr _ hz (mul_one z)]
  | mul_right x hx y hy ih =>
    obtain ⟨i, hi, rfl⟩ := hy
    exact step x hx i hi _ _ rfl ih
  | mul_inv_cancel x hx y hy ih =>
    obtain ⟨i, hi, rfl⟩ := hy
    exact step x hx i hi _ _ (by rw [Γ.rho_inv]) ih

/-- (P3) Strong flag-connectedness, from the intersection property. -/
theorem strongly_flag_connected (Φ Ψ : Flag Γ.Face) :
    Relation.ReflTransGen
      (fun A B : Flag Γ.Face => FlagAdjacent A B ∧ (Φ : Set Γ.Face) ∩ Ψ ⊆ B) Φ Ψ := by
  classical
  obtain ⟨x, hx, rfl⟩ := Γ.exists_flagOf Φ
  obtain ⟨y, hy, rfl⟩ := Γ.exists_flagOf Ψ
  let K : Finset (Fin (n + 2)) := Finset.univ.filter fun k => x⁻¹ * y ∈ Γ.sub k
  have hxy : x⁻¹ * y ∈ Γ.group := Γ.group.mul_mem (Γ.group.inv_mem hx) hy
  have hw := Γ.mem_parabolic_filter K hxy (fun k hk => (Finset.mem_filter.mp hk).2)
  have hp := Γ.path _ hx hw
  have e : Γ.flagOf (Γ.group.mul_mem hx (Γ.parabolic_le_group _ hw)) = Γ.flagOf hy :=
    Γ.flagOf_congr _ _ (by group)
  rw [e] at hp
  refine Relation.ReflTransGen.mono ?_ _ _ hp
  rintro A B ⟨hadj, hB⟩
  refine ⟨hadj, ?_⟩
  rintro F ⟨⟨k, rfl⟩, ⟨k', hk'⟩⟩
  obtain ⟨rfl, h⟩ := (Γ.face_eq_iff hy hx).mp hk'
  apply hB k'
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  apply hi k'
  simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
  simpa using (Γ.sub k').inv_mem h

/-- (P4) The diamond condition. -/
theorem diamond (F K : Γ.Face) (hFK : F < K) (hr : Γ.rank K = Γ.rank F + 2) :
    {H | F < H ∧ H < K}.ncard = 2 := by
  obtain ⟨w, hwF, hwK⟩ := hFK.le.2
  have hw := Γ.mem_group_of_mem F hwF
  have hF := Γ.face_eq_of_mem F hwF hw
  have hK := Γ.face_eq_of_mem K hwK hw
  have hjk : K.1.1.val = F.1.1.val + 2 := by unfold rank at hr; omega
  obtain ⟨j, hj⟩ : ∃ j, F.1.1.val = j := ⟨_, rfl⟩
  have hj2 : j + 2 < n + 2 := by have := K.1.1.isLt; omega
  have hj0 : j < n + 2 := by omega
  have hj1 : j + 1 < n + 2 := by omega
  have hjn : j < n := by omega
  have hFj : F.1.1 = ⟨j, hj0⟩ := Fin.ext hj
  have hKj : K.1.1 = ⟨j + 2, hj2⟩ := Fin.ext (by simp only; omega)
  rw [hFj] at hF; rw [hKj] at hK
  have hwr : w * Γ.ρ ⟨j, hjn⟩ ∈ Γ.group := Γ.group.mul_mem hw (Γ.rho_mem_group _)
  have hset : {H | F < H ∧ H < K} =
      {H | Γ.face ⟨j, hj0⟩ hw < H ∧ H < Γ.face ⟨j + 2, hj2⟩ hw} := by
    ext H; simp only [Set.mem_setOf_eq]; rw [← hF, ← hK]
  rw [hset, Γ.between_eq hj2 hw hwr]
  apply Set.ncard_pair
  rw [Ne, face_eq_iff]
  rintro ⟨-, h⟩
  exact Γ.rho_not_mem_sub ⟨j, hjn⟩ (k := ⟨j + 1, hj1⟩) rfl (by simpa using h)

/-- The least face `Γ = F_{-1}`. -/
def bot : Γ.Face := Γ.face 0 Γ.group.one_mem

/-- The greatest face `Γ = F_n`. -/
def top : Γ.Face := Γ.face (Fin.last (n + 1)) Γ.group.one_mem

lemma bot_le (F : Γ.Face) : Γ.bot ≤ F := by
  obtain ⟨x, hx, hF⟩ := Γ.exists_face F
  rw [hF]
  refine ⟨Fin.zero_le _, x, ?_, mem_self_coset _ x⟩
  simp only [bot, face_set, Γ.sub_eq_group (k := 0) (Or.inl rfl), one_smul]
  exact hx

lemma le_top (F : Γ.Face) : F ≤ Γ.top := by
  obtain ⟨x, hx, hF⟩ := Γ.exists_face F
  rw [hF]
  refine ⟨Fin.le_last _, x, mem_self_coset _ x, ?_⟩
  simp only [top, face_set, Γ.sub_eq_group (k := Fin.last (n + 1)) (Or.inr rfl), one_smul]
  exact hx

/-- **ARP 2E11 (polytope part).** The coset poset of a string C-group of rank `n`
is an abstract polytope of rank `n`. -/
theorem isPolytope : IsPolytope Γ.Face n Γ.rank where
  rank_strictMono F H h := by
    have := Fin.lt_def.mp (Γ.type_lt_of_lt h)
    unfold rank; omega
  rank_mem F := by
    have := F.1.1.isLt
    unfold rank; constructor <;> omega
  exists_least := ⟨Γ.bot, Γ.bot_le⟩
  exists_greatest := ⟨Γ.top, Γ.le_top⟩
  flag_ncard := Γ.flag_ncard
  strongly_flag_connected := Γ.strongly_flag_connected
  diamond := Γ.diamond

end StringCGroup

end P16c
