import Mathlib
import P16c.CosetRegular
import P16c.StringCTransfer

/-! # Facets and vertex-figures of `P(Γ)` (ARP 2E12(a)), and isomorphic C-groups

The facet of `P(Γ)` at the base flag is `P(⟨ρ_0, …, ρ_{n-2}⟩)` and its
vertex-figure is `P(⟨ρ_1, …, ρ_{n-1}⟩)`; by regularity, so is every facet and
every vertex-figure. A generator-preserving isomorphism of C-groups gives
isomorphic coset posets. -/

namespace P16c

open scoped Pointwise

namespace StringCGroup

variable {G : Type*} [Group G] {n : ℕ} (Γ : StringCGroup G n)

/-- The string C-group on the generators `ρ (f i)`, for `f` preserving the string
pattern. -/
def restrict {m : ℕ} (f : Fin m → Fin n) (hf : Function.Injective f)
    (hstr : ∀ i j : Fin m, i.val + 2 ≤ j.val → (f i).val + 2 ≤ (f j).val) :
    StringCGroup G m where
  ρ i := Γ.ρ (f i)
  stringC := by
    classical
    refine ⟨fun i => Γ.rho_sq _, fun i j h => Γ.stringC.2.1 _ _ (hstr i j h), fun I J => ?_⟩
    change parabolic (fun i => Γ.ρ (f i)) I ⊓ parabolic (fun i => Γ.ρ (f i)) J =
      parabolic (fun i => Γ.ρ (f i)) (I ∩ J)
    rw [parabolic_reindex Γ.ρ f I, parabolic_reindex Γ.ρ f J, parabolic_reindex Γ.ρ f (I ∩ J),
      Finset.image_inter _ _ hf]
    exact Γ.ip _ _
  ne_one i := Γ.ne_one _

/-! ### A generic section embedding -/

section Section

variable {m : ℕ} (f : Fin m → Fin n) (hf : Function.Injective f)
  (hstr : ∀ i j : Fin m, i.val + 2 ≤ j.val → (f i).val + 2 ≤ (f j).val)
  (t : Fin (m + 2) → Fin (n + 2)) (ht : StrictMono t)
  (hft : ∀ (i : Fin m) (k : Fin (m + 2)), (f i).val + 1 = (t k).val ↔ i.val + 1 = k.val)
  (c : Fin (n + 2)) (hc : (Γ.restrict f hf hstr).group = Γ.sub c)
  (hsub : ∀ k, Γ.sub (t k) ⊓ Γ.sub c = (Γ.restrict f hf hstr).sub k)

include hft in
lemma restrict_sub_le (k : Fin (m + 2)) : (Γ.restrict f hf hstr).sub k ≤ Γ.sub (t k) := by
  change parabolic (fun i => Γ.ρ (f i)) _ ≤ _
  rw [parabolic_reindex Γ.ρ f]
  apply parabolic_mono
  intro i hi
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  obtain ⟨i', hi', rfl⟩ := hi
  exact fun h => hi' ((hft i' k).mp h)

lemma restrict_group_le : (Γ.restrict f hf hstr).group ≤ Γ.group := by
  change parabolic (fun i => Γ.ρ (f i)) _ ≤ _
  rw [parabolic_reindex Γ.ρ f]; exact Γ.parabolic_le_group _

/-- The face of `P(Γ)` attached to the face `x Γ'_k` of the section's poset. -/
def secFace (k : Fin (m + 2)) {x : G} (hx : x ∈ (Γ.restrict f hf hstr).group) : Γ.Face :=
  Γ.face (t k) (Γ.restrict_group_le f hf hstr hx)

include hc in
lemma secFace_comparable (k : Fin (m + 2)) {x : G} (hx : x ∈ (Γ.restrict f hf hstr).group) :
    Γ.secFace f hf hstr t k hx ≤ Γ.face c Γ.group.one_mem ∨
      Γ.face c Γ.group.one_mem ≤ Γ.secFace f hf hstr t k hx := by
  have hxc : x ∈ (1 : G) • (Γ.sub c : Set G) := by
    rw [one_smul]; exact hc ▸ hx
  rcases le_total (t k) c with h | h
  · exact Or.inl ⟨h, x, mem_self_coset _ x, hxc⟩
  · exact Or.inr ⟨h, x, hxc, mem_self_coset _ x⟩

include ht hft hc hsub in
lemma secFace_le_iff {k l : Fin (m + 2)} {x y : G} (hx : x ∈ (Γ.restrict f hf hstr).group)
    (hy : y ∈ (Γ.restrict f hf hstr).group) :
    Γ.secFace f hf hstr t k hx ≤ Γ.secFace f hf hstr t l hy ↔
      (Γ.restrict f hf hstr).face k hx ≤ (Γ.restrict f hf hstr).face l hy := by
  constructor
  · intro h
    have hkl : k ≤ l := ht.le_iff_le.mp h.1
    have hC : IsChain (· ≤ ·) ({Γ.secFace f hf hstr t k hx, Γ.secFace f hf hstr t l hy,
        Γ.face c Γ.group.one_mem} : Set Γ.Face) := by
      have h1 := Γ.secFace_comparable f hf hstr t c hc k hx
      have h2 := Γ.secFace_comparable f hf hstr t c hc l hy
      intro a ha b hb _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> beta_reduce <;>
        first | exact Or.inl le_rfl | exact Or.inl h | exact Or.inr h | exact h1 | exact h2 | exact Or.symm h1 | exact Or.symm h2
    obtain ⟨z, hz, hzc⟩ := Γ.chain_common hC
    have e1 := hzc _ (Set.mem_insert _ _)
    have e2 := hzc (Γ.secFace f hf hstr t l hy) (by simp)
    have e3 := hzc (Γ.face c Γ.group.one_mem) (by simp)
    simp only [secFace, face_type] at e1 e2 e3
    rw [face_eq_iff] at e1 e2 e3
    have hzc' : z ∈ Γ.sub c := by simpa using e3.2
    have hzR : z ∈ (Γ.restrict f hf hstr).group := hc ▸ hzc'
    have hxc : x ∈ Γ.sub c := hc ▸ hx
    have hyc : y ∈ Γ.sub c := hc ▸ hy
    refine ⟨hkl, z, ?_, ?_⟩
    · rw [face_set, mem_leftCoset_iff, ← hsub]
      exact ⟨e1.2, (Γ.sub c).mul_mem ((Γ.sub c).inv_mem hxc) hzc'⟩
    · rw [face_set, mem_leftCoset_iff, ← hsub]
      exact ⟨e2.2, (Γ.sub c).mul_mem ((Γ.sub c).inv_mem hyc) hzc'⟩
  · rintro ⟨hkl, w, hw1, hw2⟩
    refine ⟨ht.monotone hkl, w, ?_, ?_⟩
    · simp only [secFace, face_set, mem_leftCoset_iff] at hw1 ⊢
      exact Γ.restrict_sub_le f hf hstr t hft k hw1
    · simp only [secFace, face_set, mem_leftCoset_iff] at hw2 ⊢
      exact Γ.restrict_sub_le f hf hstr t hft l hw2

include ht hft hc hsub in
lemma secFace_eq_iff {k l : Fin (m + 2)} {x y : G} (hx : x ∈ (Γ.restrict f hf hstr).group)
    (hy : y ∈ (Γ.restrict f hf hstr).group) :
    Γ.secFace f hf hstr t k hx = Γ.secFace f hf hstr t l hy ↔
      (Γ.restrict f hf hstr).face k hx = (Γ.restrict f hf hstr).face l hy := by
  simp only [le_antisymm_iff, Γ.secFace_le_iff f hf hstr t ht hft c hc hsub]

/-- The section map on faces. -/
noncomputable def secMap (F : (Γ.restrict f hf hstr).Face) : Γ.Face :=
  Γ.secFace f hf hstr t F.1.1 ((Γ.restrict f hf hstr).exists_face F).choose_spec.choose

include ht hft hc hsub in
lemma secMap_face (k : Fin (m + 2)) {x : G} (hx : x ∈ (Γ.restrict f hf hstr).group) :
    Γ.secMap f hf hstr t ((Γ.restrict f hf hstr).face k hx) = Γ.secFace f hf hstr t k hx := by
  unfold secMap
  rw [Γ.secFace_eq_iff f hf hstr t ht hft c hc hsub]
  exact ((Γ.restrict f hf hstr).exists_face _).choose_spec.choose_spec.symm

/-- The section embedding `P(Γ') ↪o P(Γ)`. -/
noncomputable def secEmb : (Γ.restrict f hf hstr).Face ↪o Γ.Face :=
  OrderEmbedding.ofMapLEIff (Γ.secMap f hf hstr t) (fun F H => by
    obtain ⟨x, hx, hF⟩ := (Γ.restrict f hf hstr).exists_face F
    obtain ⟨y, hy, hH⟩ := (Γ.restrict f hf hstr).exists_face H
    rw [hF, hH, Γ.secMap_face f hf hstr t ht hft c hc hsub,
      Γ.secMap_face f hf hstr t ht hft c hc hsub, Γ.secFace_le_iff f hf hstr t ht hft c hc hsub])

include ht hft hc hsub in
lemma range_secEmb : Set.range (Γ.secEmb f hf hstr t ht hft c hc hsub) =
    {F | (F ≤ Γ.face c Γ.group.one_mem ∨ Γ.face c Γ.group.one_mem ≤ F) ∧
      F.1.1 ∈ Set.range t} := by
  ext F
  constructor
  · rintro ⟨F', rfl⟩
    obtain ⟨x, hx, hF⟩ := (Γ.restrict f hf hstr).exists_face F'
    change Γ.secMap f hf hstr t F' ∈ _
    rw [hF, Γ.secMap_face f hf hstr t ht hft c hc hsub]
    exact ⟨Γ.secFace_comparable f hf hstr t c hc _ hx, _, rfl⟩
  · rintro ⟨hcomp, k, hk⟩
    have hne : (F.1.2 ∩ (Γ.face c Γ.group.one_mem).1.2).Nonempty := by
      rcases hcomp with h | h
      · exact h.2
      · rw [Set.inter_comm]; exact h.2
    obtain ⟨w, hwF, hwc⟩ := hne
    have hwc' : w ∈ Γ.sub c := by simpa [mem_leftCoset_iff] using hwc
    have hwR : w ∈ (Γ.restrict f hf hstr).group := hc ▸ hwc'
    refine ⟨(Γ.restrict f hf hstr).face k hwR, ?_⟩
    change Γ.secMap f hf hstr t _ = F
    rw [Γ.secMap_face f hf hstr t ht hft c hc hsub, Γ.face_eq_of_mem F hwF
      (Γ.restrict_group_le f hf hstr hwR)]
    simp only [secFace, hk]

end Section

/-! ### Isomorphic C-groups have isomorphic coset posets -/

section Transfer

variable {H : Type*} [Group H] {m : ℕ} (Δ : StringCGroup H m) (Γ' : StringCGroup G m)
  (φ : H →* G) (hφ : Function.Injective φ) (hρ : ∀ i, φ (Δ.ρ i) = Γ'.ρ i)

include hρ in
lemma image_sub (k : Fin (m + 2)) : φ '' (Δ.sub k : Set H) = Γ'.sub k := by
  rw [← Subgroup.coe_map, sub, sub, parabolic_map]
  simp only [hρ]

include hρ in
lemma image_group : (Δ.group).map φ = Γ'.group := by
  rw [group, group, parabolic_map]; simp only [hρ]

/-- The face map of a generator-preserving homomorphism. -/
def transferFun (F : Δ.Face) : Γ'.Face :=
  ⟨(F.1.1, φ '' F.1.2), by
    obtain ⟨x, hx, h⟩ := F.2
    refine ⟨φ x, image_group Δ Γ' φ hρ ▸ ⟨x, hx, rfl⟩, ?_⟩
    rw [h, Set.image_smul_distrib, image_sub Δ Γ' φ hρ]⟩

include hφ in
lemma transferFun_le_iff (F F' : Δ.Face) :
    transferFun Δ Γ' φ hρ F ≤ transferFun Δ Γ' φ hρ F' ↔ F ≤ F' := by
  simp only [le_def, transferFun, ← Set.image_inter hφ, Set.image_nonempty]

/-- **A generator-preserving injective homomorphism gives `P(Δ) ≃o P(Γ')`.** -/
noncomputable def transfer : Δ.Face ≃o Γ'.Face :=
  RelIso.ofSurjective
    (OrderEmbedding.ofMapLEIff (transferFun Δ Γ' φ hρ) (transferFun_le_iff Δ Γ' φ hφ hρ))
    (by
      intro F
      obtain ⟨y, hy, hF⟩ := Γ'.exists_face F
      rw [← image_group Δ Γ' φ hρ] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      refine ⟨Δ.face F.1.1 hx, ?_⟩
      rw [hF]
      change transferFun Δ Γ' φ hρ _ = _
      refine Subtype.ext (Prod.ext rfl ?_)
      simp only [transferFun, face_set, Set.image_smul_distrib, image_sub Δ Γ' φ hρ, face_type])

end Transfer

end StringCGroup

end P16c
