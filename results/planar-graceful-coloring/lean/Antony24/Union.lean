import Antony24.Basic

/-! Disjoint union and isomorphism lemmas.
All index and vertex types are unrestricted; in particular they may be empty. -/
namespace Antony24

variable {I : Type*} {V : I → Type*} (G : ∀ i, SimpleGraph (V i))

@[simp] theorem union_adj_same (i : I) (x y : V i) :
    (Union G).Adj ⟨i, x⟩ ⟨i, y⟩ ↔ (G i).Adj x y := by
  constructor
  · rintro ⟨h, hxy⟩
    simpa using hxy
  · intro hxy
    exact ⟨rfl, hxy⟩

theorem graceful4_union_iff : Graceful4 (Union G) ↔ ∀ i, Graceful4 (G i) := by
  classical
  constructor
  · rintro ⟨c, hproper, hdiff⟩ i
    refine ⟨fun v => c ⟨i, v⟩, ?_, ?_⟩
    · intro u v huv
      exact hproper ((union_adj_same G i u v).2 huv)
    · intro v u w hvu hvw huw
      apply hdiff ((union_adj_same G i v u).2 hvu)
        ((union_adj_same G i v w).2 hvw)
      intro h
      exact huw (Sigma.mk.inj_iff.mp h).2.eq
  · intro h
    choose c hc using h
    refine ⟨fun v => c v.1 v.2, ?_, ?_⟩
    · rintro ⟨i, u⟩ ⟨j, v⟩ ⟨hij, huv⟩
      cases hij
      exact (hc i).1 huv
    · rintro ⟨i, v⟩ ⟨j, u⟩ ⟨k, w⟩ ⟨hij, hvu⟩ ⟨hik, hvw⟩ huw
      cases hij
      cases hik
      apply (hc i).2 hvu hvw
      intro h
      apply huw
      cases h
      rfl

theorem pmc_union_iff : PMC (Union G) ↔ ∀ i, PMC (G i) := by
  classical
  constructor
  · rintro ⟨side, hs⟩ i
    refine ⟨fun v => side ⟨i, v⟩, ?_⟩
    intro v
    obtain ⟨⟨j, w⟩, ⟨⟨hij, hvw⟩, hside⟩, hu⟩ := hs ⟨i, v⟩
    cases hij
    refine ⟨w, ⟨hvw, hside⟩, ?_⟩
    intro z hz
    have he := hu ⟨i, z⟩ ⟨(union_adj_same G i v z).2 hz.1, hz.2⟩
    exact (Sigma.mk.inj_iff.mp he).2.eq
  · intro h
    choose side hs using h
    refine ⟨fun v => side v.1 v.2, ?_⟩
    rintro ⟨i, v⟩
    obtain ⟨w, hw, hu⟩ := hs i v
    refine ⟨⟨i, w⟩, ⟨(union_adj_same G i v w).2 hw.1, hw.2⟩, ?_⟩
    rintro ⟨j, z⟩ ⟨⟨hij, hvz⟩, hzside⟩
    cases hij
    have he := hu z ⟨hvz, hzside⟩
    cases he
    rfl

/-- Cubicity is preserved when source instances are aggregated. -/
theorem cubic_union (h : ∀ i, Cubic (G i)) : Cubic (Union G) := by
  rintro ⟨i, v⟩
  obtain ⟨a,b,c,hab,hac,hbc,hn⟩ := h i v
  have inj {x y : V i} (he : (Sigma.mk i x : Sigma V) = ⟨i,y⟩) : x = y :=
    (Sigma.mk.inj_iff.mp he).2.eq
  refine ⟨⟨i,a⟩,⟨i,b⟩,⟨i,c⟩,fun he => hab (inj he),
    fun he => hac (inj he),fun he => hbc (inj he),?_⟩
  rintro ⟨j,w⟩
  constructor
  · rintro ⟨he,hw⟩
    cases he
    rcases (hn w).mp hw with rfl|rfl|rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (he|he|he) <;> cases he
    · exact ⟨rfl,(hn a).mpr (Or.inl rfl)⟩
    · exact ⟨rfl,(hn b).mpr (Or.inr (Or.inl rfl))⟩
    · exact ⟨rfl,(hn c).mpr (Or.inr (Or.inr rfl))⟩

theorem graceful4_of_iso {A B : Type*} {H : SimpleGraph A} {K : SimpleGraph B}
    (f : H ≃g K) : Graceful4 K → Graceful4 H := by
  rintro ⟨c, hproper, hdiff⟩
  refine ⟨fun v => c (f v), ?_, ?_⟩
  · intro u v huv
    exact hproper (f.map_adj_iff.mpr huv)
  · intro v u w hvu hvw huw
    exact hdiff (f.map_adj_iff.mpr hvu) (f.map_adj_iff.mpr hvw)
      (fun h => huw (f.injective h))

theorem graceful4_iso_iff {A B : Type*} {H : SimpleGraph A} {K : SimpleGraph B}
    (f : H ≃g K) : Graceful4 H ↔ Graceful4 K :=
  ⟨graceful4_of_iso f.symm, graceful4_of_iso f⟩

/-- Insert one component's subdivided vertices into the subdivided union. -/
def subUnionInsert (i : I) : SubVertex (G i) → SubVertex (Union G)
  | .inl v => .inl ⟨i, v⟩
  | .inr d => .inr ⟨(⟨i, d.val.1⟩, ⟨i, d.val.2⟩), ⟨rfl, d.property⟩⟩

/-- Every subdivided-union vertex has a unique component, including the
internal vertices, because a union edge has both endpoints in one component. -/
noncomputable def subUnionEquiv : (Σ i, SubVertex (G i)) ≃ SubVertex (Union G) where
  toFun x := subUnionInsert G x.1 x.2
  invFun x := by
    cases x with
    | inl v => exact ⟨v.1, .inl v.2⟩
    | inr d =>
      rcases d with ⟨⟨⟨i, v⟩, ⟨j, w⟩⟩, ha⟩
      have h := Classical.choose ha
      have hvw := Classical.choose_spec ha
      cases h
      exact ⟨i, .inr ⟨(v, w), hvw⟩⟩
  left_inv := by
    rintro ⟨i, x⟩
    cases x <;> rfl
  right_inv := by
    intro x
    cases x with
    | inl v => rfl
    | inr d =>
      rcases d with ⟨⟨⟨i, v⟩, ⟨j, w⟩⟩, ⟨h, hvw⟩⟩
      cases h
      rfl

/-- S2 commutes with every dependent disjoint union, by an explicit
isomorphism; there are no finiteness or inhabitedness side conditions. -/
noncomputable def unionS2Iso : Union (fun i => S2 (G i)) ≃g S2 (Union G) where
  toEquiv := subUnionEquiv G
  map_rel_iff' := by
    rintro ⟨i, x⟩ ⟨j, y⟩
    by_cases hij : i = j
    · subst j
      cases x <;> cases y <;>
        simp [subUnionEquiv, subUnionInsert, S2, Union, Dart.rev,
          Subtype.ext_iff, Sigma.mk.inj_iff, Prod.ext_iff]
    · cases x <;> cases y <;>
        simp [subUnionEquiv, subUnionInsert, S2, Union, Dart.rev,
          Subtype.ext_iff, Sigma.mk.inj_iff, Prod.ext_iff, hij, Ne.symm hij]

noncomputable def s2UnionIso : S2 (Union G) ≃g Union (fun i => S2 (G i)) :=
  (unionS2Iso G).symm

theorem graceful4_s2_union_iff :
    Graceful4 (S2 (Union G)) ↔ ∀ i, Graceful4 (S2 (G i)) := by
  exact (graceful4_iso_iff (s2UnionIso G)).trans
    (graceful4_union_iff (fun i => S2 (G i)))

end Antony24
