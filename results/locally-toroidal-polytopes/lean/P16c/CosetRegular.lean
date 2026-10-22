import Mathlib
import P16c.CosetPolytope
import P16c.PolytopeTheory

/-! # `P(Γ)` is regular with group `Γ` (ARP 2E11) -/

namespace P16c

open scoped Pointwise

namespace StringCGroup

variable {G : Type*} [Group G] {n : ℕ} (Γ : StringCGroup G n)

/-- Left multiplication by `g ∈ Γ` on faces. -/
def actFun (g : Γ.group) (F : Γ.Face) : Γ.Face :=
  ⟨(F.1.1, (g : G) • F.1.2), by
    obtain ⟨x, hx, h⟩ := F.2
    exact ⟨g * x, Γ.group.mul_mem g.2 hx, by rw [h, smul_smul]⟩⟩

lemma actFun_mul (g h : Γ.group) (F : Γ.Face) :
    Γ.actFun (g * h) F = Γ.actFun g (Γ.actFun h F) :=
  Subtype.ext (Prod.ext rfl (by simp [actFun, smul_smul]))

lemma actFun_one (F : Γ.Face) : Γ.actFun 1 F = F :=
  Subtype.ext (Prod.ext rfl (by simp [actFun]))

lemma actFun_le_iff (g : Γ.group) (F H : Γ.Face) :
    Γ.actFun g F ≤ Γ.actFun g H ↔ F ≤ H := by
  simp only [le_def, actFun, ← Set.smul_set_inter, Set.smul_set_nonempty]

/-- The action of `Γ` on `P(Γ)` by order automorphisms. -/
def act : Γ.group →* (Γ.Face ≃o Γ.Face) where
  toFun g :=
    { toFun := Γ.actFun g
      invFun := Γ.actFun g⁻¹
      left_inv := fun F => by rw [← actFun_mul, inv_mul_cancel, actFun_one]
      right_inv := fun F => by rw [← actFun_mul, mul_inv_cancel, actFun_one]
      map_rel_iff' := Γ.actFun_le_iff g _ _ }
  map_one' := RelIso.ext fun F => Γ.actFun_one F
  map_mul' g h := RelIso.ext fun F => Γ.actFun_mul g h F

lemma act_apply (g : Γ.group) (F : Γ.Face) : Γ.act g F = Γ.actFun g F := rfl

lemma act_face (g : Γ.group) (k : Fin (n + 2)) {x : G} (hx : x ∈ Γ.group) :
    Γ.act g (Γ.face k hx) = Γ.face k (Γ.group.mul_mem g.2 hx) :=
  Subtype.ext (Prod.ext rfl (by simp [act_apply, actFun, face, smul_smul]))

lemma map_flagOf (g : Γ.group) {x : G} (hx : x ∈ Γ.group) :
    Flag.map (Γ.act g) (Γ.flagOf hx) = Γ.flagOf (Γ.group.mul_mem g.2 hx) := by
  apply SetLike.coe_injective
  rw [Flag.coe_map, coe_flagOf, coe_flagOf, flagSet, flagSet, ← Set.range_comp]
  congr 1
  funext k
  exact Γ.act_face g k hx

lemma flagOf_inj {a b : G} (ha : a ∈ Γ.group) (hb : b ∈ Γ.group)
    (h : Γ.flagOf ha = Γ.flagOf hb) : a = b := by
  classical
  have hk : ∀ k, b⁻¹ * a ∈ Γ.sub k := by
    intro k
    have hmem : Γ.face k ha ∈ (Γ.flagOf hb : Set Γ.Face) := by
      rw [← h]; exact ⟨k, rfl⟩
    obtain ⟨k', hk'⟩ := hmem
    obtain ⟨rfl, h'⟩ := (Γ.face_eq_iff hb ha).mp hk'
    exact h'
  have hm := Γ.mem_parabolic_filter Finset.univ
    (Γ.group.mul_mem (Γ.group.inv_mem hb) ha) (fun k _ => hk k)
  have hempty : (Finset.univ.filter fun i : Fin n =>
      ∀ k ∈ (Finset.univ : Finset (Fin (n + 2))), i.val + 1 ≠ k.val) = ∅ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
      not_forall]
    exact ⟨⟨i.val + 1, by omega⟩, trivial, by simp⟩
  rw [hempty, parabolic_empty, Subgroup.mem_bot] at hm
  exact (inv_mul_eq_one.mp hm).symm

/-- **ARP 2E11 (regularity).** `Γ` acts simply transitively on the flags of `P(Γ)`. -/
theorem act_simply_transitive (Φ Ψ : Flag Γ.Face) :
    ∃! g : Γ.group, Flag.map (Γ.act g) Φ = Ψ := by
  obtain ⟨x, hx, rfl⟩ := Γ.exists_flagOf Φ
  obtain ⟨y, hy, rfl⟩ := Γ.exists_flagOf Ψ
  refine ⟨⟨y * x⁻¹, Γ.group.mul_mem hy (Γ.group.inv_mem hx)⟩, ?_, ?_⟩
  · beta_reduce; rw [map_flagOf]; exact Γ.flagOf_congr _ _ (by simp)
  · intro g hg
    rw [map_flagOf] at hg
    have := Γ.flagOf_inj _ _ hg
    apply Subtype.ext
    simp only
    rw [← this]; group

theorem isRegular : IsRegular Γ.Face := fun Φ Ψ =>
  let ⟨g, hg, _⟩ := Γ.act_simply_transitive Φ Ψ
  ⟨Γ.act g, hg⟩

/-- **ARP 2E11 (group).** Every automorphism of `P(Γ)` is the action of a unique
element of `Γ`: `Γ(P(Γ)) ≅ Γ`. -/
theorem act_bijective : Function.Bijective Γ.act := by
  have hP := Γ.isPolytope
  constructor
  · intro g h e
    obtain ⟨_, -, huniq⟩ := Γ.act_simply_transitive (Γ.flagOf Γ.group.one_mem)
      (Flag.map (Γ.act g) (Γ.flagOf Γ.group.one_mem))
    exact (huniq g rfl).trans (huniq h (by rw [e])).symm
  · intro σ
    obtain ⟨x, hx, hσ⟩ := Γ.exists_flagOf (Flag.map σ (Γ.flagOf Γ.group.one_mem))
    refine ⟨⟨x, hx⟩, ?_⟩
    have hfix : ∀ F ∈ Γ.flagOf Γ.group.one_mem, ((Γ.act ⟨x, hx⟩)⁻¹ * σ) F = F := by
      rintro F ⟨k, rfl⟩
      have hmem : σ (Γ.face k Γ.group.one_mem) ∈ (Γ.flagOf hx : Set Γ.Face) := by
        rw [← hσ, Flag.coe_map]; exact ⟨_, ⟨k, rfl⟩, rfl⟩
      obtain ⟨k', hk'⟩ := hmem
      have hr := hP.rank_map hP σ (Γ.face k Γ.group.one_mem)
      rw [← hk'] at hr
      have hkk : k' = k := by
        unfold rank at hr; simp only [face_type] at hr; exact Fin.ext (by omega)
      subst hkk
      rw [RelIso.mul_apply, ← hk', ← map_inv, act_face]
      exact Γ.face_congr _ _ _ (by simp)
    have := hP.eq_one_of_fix _ _ hfix
    rw [inv_mul_eq_one] at this
    exact this

end StringCGroup

end P16c
