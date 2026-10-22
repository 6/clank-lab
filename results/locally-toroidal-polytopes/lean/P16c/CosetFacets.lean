import Mathlib
import P16c.CosetSections

/-! # ARP 2E12(a): every facet of `P(Γ)` is `P(⟨ρ_0, …, ρ_{n-2}⟩)` and every
vertex-figure is `P(⟨ρ_1, …, ρ_{n-1}⟩)` -/

namespace P16c

open scoped Pointwise

/-- An automorphism maps the section below `F` onto the section below `σ F`. -/
def isoIic {P : Type*} [PartialOrder P] (σ : P ≃o P) (F : P) :
    Set.Iic F ≃o Set.Iic (σ F) where
  toEquiv := σ.toEquiv.subtypeEquiv (fun _ => σ.le_iff_le.symm)
  map_rel_iff' := σ.le_iff_le

/-- An automorphism maps the section above `F` onto the section above `σ F`. -/
def isoIci {P : Type*} [PartialOrder P] (σ : P ≃o P) (F : P) :
    Set.Ici F ≃o Set.Ici (σ F) where
  toEquiv := σ.toEquiv.subtypeEquiv (fun _ => σ.le_iff_le.symm)
  map_rel_iff' := σ.le_iff_le

namespace StringCGroup

variable {G : Type*} [Group G] {m : ℕ} (Γ : StringCGroup G (m + 1))

/-- The facet group `⟨ρ_0, …, ρ_{n-2}⟩` (here `n = m + 1`). -/
def facetGroup : StringCGroup G m :=
  Γ.restrict Fin.castSucc (Fin.castSucc_injective _) (fun i j h => by simpa using h)

/-- The vertex-figure group `⟨ρ_1, …, ρ_{n-1}⟩`. -/
def vertexGroup : StringCGroup G m :=
  Γ.restrict Fin.succ (Fin.succ_injective _) (fun i j h => by simp only [Fin.val_succ]; omega)

/-- The type of the facets (rank `n - 1`). -/
def facetType (m : ℕ) : Fin (m + 3) := ⟨m + 1, by omega⟩

/-- The type of the vertices (rank `0`). -/
def vertexType (m : ℕ) : Fin (m + 3) := ⟨1, by omega⟩

lemma facet_hft (i : Fin m) (k : Fin (m + 2)) :
    (Fin.castSucc i).val + 1 = (Fin.castSucc k).val ↔ i.val + 1 = k.val := by simp

lemma vertex_hft (i : Fin m) (k : Fin (m + 2)) :
    (Fin.succ i).val + 1 = (Fin.succ k).val ↔ i.val + 1 = k.val := by
  simp only [Fin.val_succ]; omega

lemma facet_hc : Γ.facetGroup.group = Γ.sub (facetType m) := by
  change parabolic (fun i => Γ.ρ (Fin.castSucc i)) _ = _
  rw [parabolic_reindex Γ.ρ Fin.castSucc]
  unfold sub facetType
  congr 1
  ext i
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨a, rfl⟩; simp only [Fin.val_castSucc]; omega
  · intro h; exact ⟨⟨i.val, by omega⟩, Fin.ext rfl⟩

lemma vertex_hc : Γ.vertexGroup.group = Γ.sub (vertexType m) := by
  change parabolic (fun i => Γ.ρ (Fin.succ i)) _ = _
  rw [parabolic_reindex Γ.ρ Fin.succ]
  unfold sub vertexType
  congr 1
  ext i
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨a, rfl⟩; simp only [Fin.val_succ]; omega
  · intro h; exact ⟨⟨i.val - 1, by omega⟩, Fin.ext (by simp only [Fin.val_succ]; omega)⟩

lemma facet_hsub (k : Fin (m + 2)) :
    Γ.sub (Fin.castSucc k) ⊓ Γ.sub (facetType m) = Γ.facetGroup.sub k := by
  rw [sub, sub, Γ.ip]
  change _ = parabolic (fun i => Γ.ρ (Fin.castSucc i)) _
  rw [parabolic_reindex Γ.ρ Fin.castSucc]
  congr 1
  ext i
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, Finset.mem_inter,
    facetType, Fin.val_castSucc]
  constructor
  · intro h; exact ⟨⟨i.val, by omega⟩, by simp only; omega, Fin.ext rfl⟩
  · rintro ⟨a, ha, rfl⟩; simp only [Fin.val_castSucc]; omega

lemma vertex_hsub (k : Fin (m + 2)) :
    Γ.sub (Fin.succ k) ⊓ Γ.sub (vertexType m) = Γ.vertexGroup.sub k := by
  rw [sub, sub, Γ.ip]
  change _ = parabolic (fun i => Γ.ρ (Fin.succ i)) _
  rw [parabolic_reindex Γ.ρ Fin.succ]
  congr 1
  ext i
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, Finset.mem_inter,
    vertexType, Fin.val_succ]
  constructor
  · intro h
    exact ⟨⟨i.val - 1, by omega⟩, by simp only; omega, Fin.ext (by simp only [Fin.val_succ]; omega)⟩
  · rintro ⟨a, ha, rfl⟩; simp only [Fin.val_succ]; omega

/-- The base facet section is `P(facet group)`. -/
noncomputable def baseFacetIso :
    Set.Iic (Γ.face (facetType m) Γ.group.one_mem) ≃o Γ.facetGroup.Face := by
  refine (OrderIso.setCongr _ _ ?_).trans
    (Γ.secEmb Fin.castSucc (Fin.castSucc_injective _) (fun i j h => by simpa using h)
      Fin.castSucc Fin.strictMono_castSucc facet_hft (facetType m) Γ.facet_hc
      Γ.facet_hsub).orderIso.symm
  rw [range_secEmb]
  ext F
  simp only [Set.mem_Iic, Set.mem_setOf_eq, Set.mem_range]
  constructor
  · intro h
    have h1 : F.1.1.val ≤ m + 1 := by have := h.1; simpa [facetType, Fin.le_def] using this
    exact ⟨Or.inl h, ⟨F.1.1.val, by omega⟩, Fin.ext rfl⟩
  · rintro ⟨h | h, k, hk⟩
    · exact h
    · have hle : F.1.1.val ≤ m + 1 := by rw [← hk]; simp only [Fin.val_castSucc]; omega
      have := Γ.eq_of_le_of_type_eq h (Fin.ext (by
        have := h.1; simp only [facetType, face_type, Fin.le_def] at this ⊢; omega))
      exact this ▸ le_rfl

/-- The base vertex-figure section is `P(vertex-figure group)`. -/
noncomputable def baseVertexIso :
    Set.Ici (Γ.face (vertexType m) Γ.group.one_mem) ≃o Γ.vertexGroup.Face := by
  refine (OrderIso.setCongr _ _ ?_).trans
    (Γ.secEmb Fin.succ (Fin.succ_injective _)
      (fun i j h => by simp only [Fin.val_succ]; omega)
      Fin.succ (Fin.strictMono_succ) vertex_hft (vertexType m) Γ.vertex_hc
      Γ.vertex_hsub).orderIso.symm
  rw [range_secEmb]
  ext F
  simp only [Set.mem_Ici, Set.mem_setOf_eq, Set.mem_range]
  constructor
  · intro h
    have h1 : 1 ≤ F.1.1.val := by have := h.1; simpa [vertexType, Fin.le_def] using this
    exact ⟨Or.inr h, ⟨F.1.1.val - 1, by have := F.1.1.isLt; omega⟩,
      Fin.ext (by simp only [Fin.val_succ]; omega)⟩
  · rintro ⟨h | h, k, hk⟩
    · have := Γ.eq_of_le_of_type_eq h (Fin.ext (by
        have := h.1; rw [← hk] at this ⊢
        simp only [vertexType, face_type, Fin.le_def, Fin.val_succ] at this ⊢; omega))
      exact this ▸ le_rfl
    · exact h

lemma rank_eq_iff_type (F : Γ.Face) (j : ℕ) : Γ.rank F = j ↔ F.1.1.val = j + 1 := by
  unfold rank; omega

/-- **ARP 2E12(a), facets.** Every facet of `P(Γ)` is isomorphic to `P(⟨ρ_0, …, ρ_{n-2}⟩)`. -/
theorem facet_iso (F : Γ.Face) (hF : Γ.rank F = m) : Nonempty (Set.Iic F ≃o Γ.facetGroup.Face) := by
  obtain ⟨x, hx, rfl⟩ : ∃ x, ∃ hx : x ∈ Γ.group, F = Γ.face (facetType m) hx := by
    obtain ⟨x, hx, h⟩ := Γ.exists_face F
    refine ⟨x, hx, h.trans ?_⟩
    congr 1
    exact Fin.ext ((Γ.rank_eq_iff_type F m).mp hF)
  have e := Γ.act_face ⟨x, hx⟩ (facetType m) Γ.group.one_mem
  rw [Γ.face_congr _ _ hx (mul_one x)] at e
  exact ⟨(e ▸ isoIic (Γ.act ⟨x, hx⟩) _).symm.trans Γ.baseFacetIso⟩

/-- **ARP 2E12(a), vertex-figures.** Every vertex-figure of `P(Γ)` is isomorphic to
`P(⟨ρ_1, …, ρ_{n-1}⟩)`. -/
theorem vertexFigure_iso (v : Γ.Face) (hv : Γ.rank v = 0) :
    Nonempty (Set.Ici v ≃o Γ.vertexGroup.Face) := by
  obtain ⟨x, hx, rfl⟩ : ∃ x, ∃ hx : x ∈ Γ.group, v = Γ.face (vertexType m) hx := by
    obtain ⟨x, hx, h⟩ := Γ.exists_face v
    refine ⟨x, hx, h.trans ?_⟩
    congr 1
    exact Fin.ext ((Γ.rank_eq_iff_type v 0).mp (by exact_mod_cast hv))
  have e := Γ.act_face ⟨x, hx⟩ (vertexType m) Γ.group.one_mem
  rw [Γ.face_congr _ _ hx (mul_one x)] at e
  exact ⟨(e ▸ isoIci (Γ.act ⟨x, hx⟩) _).symm.trans Γ.baseVertexIso⟩

end StringCGroup

end P16c
