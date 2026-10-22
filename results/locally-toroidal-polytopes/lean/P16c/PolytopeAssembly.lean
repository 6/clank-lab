import Mathlib
import StatementGroupForm
import P16c.CosetFacets
import P16c.SectionRelations
import P16c.Covering

/-! # The P16c polytope: assembly

`Γ(s,u)` and the toroid groups `[4,4]_(s,0)` as string C-groups; the facets and
vertex-figures of `P(Γ(s,u))` are the toroidal maps; and every regular
4-polytope with these facets and vertex-figures has a group that is a quotient
of `Γ(s,u)` under its distinguished generators. -/

namespace P16c

open Universal

lemma ne_one_of_orderOf {G : Type*} [Group G] {a b : G} (hb : b ^ 2 = 1)
    (h : orderOf (a * b) = 4) : a ≠ 1 := by
  rintro rfl
  rw [one_mul] at h
  have := orderOf_dvd_of_pow_eq_one hb
  rw [h] at this
  omega

lemma ne_one_of_orderOf' {G : Type*} [Group G] {a b : G} (ha : a ^ 2 = 1)
    (h : orderOf (a * b) = 4) : b ≠ 1 := by
  rintro rfl
  rw [mul_one] at h
  have := orderOf_dvd_of_pow_eq_one ha
  rw [h] at this
  omega

lemma odd_add_two {s : ℕ} (hs : Odd s) : Odd (s + 2) := hs.add_even even_two

section Gamma

variable {s u : ℕ} (hs : Odd s) (hu : Odd u) (hs3 : 3 ≤ s) (hu3 : 3 ≤ u) (hsu : s ≠ u)
include hs hu hs3 hu3 hsu

lemma gamma_r_ne_one (i : Fin 4) : Universal.r s u i ≠ 1 := by
  obtain ⟨k, l, m, hl, hm⟩ := fields_exist s u hs hu
  have hc := core_for_parameters s u hs hu hs3 hu3 hsu l m hl hm
  set g := generators (aParam l m) (bParam l m) (parameters s u hs3 hu3 hsu l m hl hm).2.2.1
  intro h
  have hg : g i = 1 := by rw [← coreMap_r g s u hc i, h, map_one]
  fin_cases i
  · exact ne_one_of_orderOf (hc.1 1) hc.2.1 hg
  · exact ne_one_of_orderOf' (hc.1 0) hc.2.1 hg
  · exact ne_one_of_orderOf' (hc.1 1) hc.2.2.1 hg
  · exact ne_one_of_orderOf' (hc.1 2) hc.2.2.2.1 hg

lemma local_injective :
    Function.Injective (facetMap s u) ∧ Function.Injective (vertexMap s u) := by
  obtain ⟨k, l, m, hl, hm⟩ := fields_exist s u hs hu
  exact local_maps_injective _ s u (by omega) (by omega)
    (core_for_parameters s u hs hu hs3 hu3 hsu l m hl hm)

omit hs hu hs3 hu3 hsu in
/-- `Γ(s,u)` with its distinguished generators, a string C-group of rank 4. -/
def gammaC (s u : ℕ) (hs : Odd s) (hu : Odd u) (hs3 : 3 ≤ s) (hu3 : 3 ≤ u) (hsu : s ≠ u) :
    StringCGroup (Gamma s u) 4 where
  ρ := Universal.r s u
  stringC := (p16c_universal_stringC s u hs hu hs3 hu3 hsu).1
  ne_one := gamma_r_ne_one hs hu hs3 hu3 hsu

end Gamma

lemma gammaC_group (s u : ℕ) (hs : Odd s) (hu : Odd u) (hs3 : 3 ≤ s) (hu3 : 3 ≤ u)
    (hsu : s ≠ u) : (gammaC s u hs hu hs3 hu3 hsu).group = ⊤ := by
  change Subgroup.closure (Universal.r s u '' ((Finset.univ : Finset (Fin 4)) : Set (Fin 4))) = ⊤
  rw [Finset.coe_univ, Set.image_univ]
  exact PresentedGroup.closure_range_of _

/-- The toroid group `[4,4]_(s,0)` (Coxeter–Moser §8.3) with its distinguished
generators, a string C-group of rank 3 for odd `s ≥ 3` (via `Γ(s, s+2)`). -/
def toroidC (s : ℕ) (hs : Odd s) (hs3 : 3 ≤ s) : StringCGroup (Toroid.G s) 3 where
  ρ := Toroid.r s
  stringC := IsStringCGroup.of_injective (Toroid.r s) (facetMap s (s + 2))
    (local_injective hs (odd_add_two hs) hs3 (by omega)
      (by omega)).1
    (by
      have := ((gammaC s (s + 2) hs (odd_add_two hs) hs3
        (by omega) (by omega)).facetGroup).stringC
      simpa [StringCGroup.facetGroup, StringCGroup.restrict, gammaC] using this)
  ne_one i h := gamma_r_ne_one hs (odd_add_two hs) hs3
    (by omega) (by omega) i.castSucc (by rw [← facetMap_r, h, map_one])

/-- The toroidal map `{4,4}_(s,0)`: the regular 3-polytope `P([4,4]_(s,0))`. -/
abbrev ToroidalMap (s : ℕ) (hs : Odd s) (hs3 : 3 ≤ s) := (toroidC s hs hs3).Face

section Assembly

variable {s u : ℕ} (hs : Odd s) (hu : Odd u) (hs3 : 3 ≤ s) (hu3 : 3 ≤ u) (hsu : s ≠ u)
include hs hu hs3 hu3 hsu

/-- `P(Γ(s,u))`'s facets are `{4,4}_(s,0)`. -/
theorem gamma_facets (F : (gammaC s u hs hu hs3 hu3 hsu).Face)
    (hF : (gammaC s u hs hu hs3 hu3 hsu).rank F = 3) :
    Nonempty (Set.Iic F ≃o ToroidalMap s hs hs3) := by
  obtain ⟨e⟩ := (gammaC s u hs hu hs3 hu3 hsu).facet_iso F hF
  exact ⟨e.trans (StringCGroup.transfer (toroidC s hs hs3)
    (gammaC s u hs hu hs3 hu3 hsu).facetGroup (facetMap s u)
    (local_injective hs hu hs3 hu3 hsu).1 (fun i => facetMap_r s u i)).symm⟩

/-- `P(Γ(s,u))`'s vertex-figures are `{4,4}_(u,0)`. -/
theorem gamma_vertexFigures (v : (gammaC s u hs hu hs3 hu3 hsu).Face)
    (hv : (gammaC s u hs hu hs3 hu3 hsu).rank v = 0) :
    Nonempty (Set.Ici v ≃o ToroidalMap u hu hu3) := by
  obtain ⟨e⟩ := (gammaC s u hs hu hs3 hu3 hsu).vertexFigure_iso v hv
  exact ⟨e.trans (StringCGroup.transfer (toroidC u hu hu3)
    (gammaC s u hs hu hs3 hu3 hsu).vertexGroup (vertexMap s u)
    (local_injective hs hu hs3 hu3 hsu).2 (fun i => vertexMap_r s u i)).symm⟩

/-- **Universality (ARP 4A2).** Every regular 4-polytope `Q` whose facets
are all `{4,4}_(s,0)` and vertex-figures all `{4,4}_(u,0)` has a group that is a
quotient of `Γ(s,u)`, with `r_i` mapped to the distinguished generators for a
base flag `Φ` (the automorphism fixing every face of `Φ` except the `i`-face),
and `P(Γ(s,u))` covers `Q`. -/
theorem gamma_universal {Q : Type*} [PartialOrder Q] {rank : Q → ℤ}
    (hQ : IsPolytope Q 4 rank) (hreg : IsRegular Q)
    (hfac : ∀ F : Q, rank F = 3 → Nonempty (Set.Iic F ≃o ToroidalMap s hs hs3))
    (hvf : ∀ v : Q, rank v = 0 → Nonempty (Set.Ici v ≃o ToroidalMap u hu hu3)) :
    ∃ π : Gamma s u →* (Q ≃o Q), Function.Surjective π ∧
      (∃ Φ : Flag Q, ∀ i : Fin 4, ∀ F ∈ Φ, (π (Universal.r s u i) F = F ↔ rank F ≠ i)) ∧
      ∃ c : (gammaC s u hs hu hs3 hu3 hsu).Face → Q,
        IsCovering (gammaC s u hs hu hs3 hu3 hsu).rank rank c := by
  obtain ⟨B, hB⟩ := hQ.exists_least
  obtain ⟨Φ, -⟩ := exists_flag_mem B
  obtain ⟨D, rfl⟩ := hQ.exists_distinguished hreg Φ
  have hσ2 : ∀ i : Fin 4, D.σ i ^ 2 = 1 := fun i =>
    D.σ_sq hQ i (by omega) (by have := i.isLt; omega)
  have hcomm : ∀ i j : Fin 4, i.val + 2 ≤ j.val → (D.σ i * D.σ j) ^ 2 = 1 := fun i j h =>
    D.σ_comm hQ i j (by omega) (by have := i.isLt; omega) (by omega)
      (by have := j.isLt; omega) (by omega)
  have hlt : ∀ j k : ℤ, -1 ≤ j → j < k → k ≤ 4 → D.φ j < D.φ k := fun j k h1 h2 h3 =>
    D.φ_lt hQ h1 h2 (by exact_mod_cast h3)
  have hbot : ∀ G, D.φ (-1) ≤ G := fun G => by
    have := hB G
    have hBφ : B = D.φ (-1) := hQ.flag_eq_of_rank_eq D.Φ
      (IsPolytope.mem_flag_of_comparable D.Φ (fun G _ => Or.inl (hB G)))
      (D.φ_mem _ le_rfl (by omega)) (by rw [hQ.least_rank hB, D.φ_rank _ le_rfl (by omega)])
    rwa [← hBφ]
  obtain ⟨T, hT⟩ := hQ.exists_greatest
  have htop : ∀ G, G ≤ D.φ 4 := fun G => by
    have hTφ : T = D.φ 4 := hQ.flag_eq_of_rank_eq D.Φ
      (IsPolytope.mem_flag_of_comparable D.Φ (fun G _ => Or.inr (hT G)))
      (D.φ_mem 4 (by omega) (by norm_num))
      (by rw [hQ.greatest_rank hT, D.φ_rank 4 (by omega) (by norm_num)]; norm_num)
    rw [← hTφ]; exact hT G
  -- the facet relations
  obtain ⟨eF⟩ := hfac (D.φ 3) (D.φ_rank 3 (by omega) (by omega))
  have eF' : Set.Icc (D.φ (-1)) (D.φ (-1 + (3 : ℕ) + 1)) ≃o (toroidC s hs hs3).Face :=
    (OrderIso.setCongr _ _ (by
      ext G; simp only [Set.mem_Icc, Set.mem_Iic]
      norm_num; exact fun _ => hbot G)).trans eF
  have hfacet : ∀ w : FreeGroup (Fin 3), FreeGroup.lift (Toroid.r s) w = 1 →
      FreeGroup.lift (fun i : Fin 3 => D.σ (-1 + 1 + i)) w = 1 := fun w hw =>
    D.section_relation hQ (toroidC s hs hs3) (-1) le_rfl (by omega) (by norm_num)
      (by norm_num) eF' w hw
  -- the vertex-figure relations
  obtain ⟨eV⟩ := hvf (D.φ 0) (D.φ_rank 0 (by omega) (by omega))
  have eV' : Set.Icc (D.φ 0) (D.φ (0 + (3 : ℕ) + 1)) ≃o (toroidC u hu hu3).Face :=
    (OrderIso.setCongr _ _ (by
      ext G; simp only [Set.mem_Icc, Set.mem_Ici]
      norm_num; exact fun _ => htop G)).trans eV
  have hvertex : ∀ w : FreeGroup (Fin 3), FreeGroup.lift (Toroid.r u) w = 1 →
      FreeGroup.lift (fun i : Fin 3 => D.σ (0 + 1 + i)) w = 1 := fun w hw =>
    D.section_relation hQ (toroidC u hu hu3) 0 (by omega) le_rfl (by norm_num)
      (by norm_num) eV' w hw
  have tr := Toroid.relations s
  have tv := Toroid.relations u
  have h01 : (D.σ ((0 : Fin 4) : ℤ) * D.σ ((1 : Fin 4) : ℤ)) ^ 4 = 1 := by
    have := hfacet ((FreeGroup.of 0 * FreeGroup.of 1) ^ 4) (by simpa [Toroid.r] using tr.2.1)
    simpa using this
  have h12 : (D.σ ((1 : Fin 4) : ℤ) * D.σ ((2 : Fin 4) : ℤ)) ^ 4 = 1 := by
    have := hfacet ((FreeGroup.of 1 * FreeGroup.of 2) ^ 4) (by simpa [Toroid.r] using tr.2.2.1)
    simpa using this
  have ht : (D.σ ((0 : Fin 4) : ℤ) * D.σ ((1 : Fin 4) : ℤ) * D.σ ((2 : Fin 4) : ℤ) *
      D.σ ((1 : Fin 4) : ℤ)) ^ s = 1 := by
    have := hfacet ((FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 2 * FreeGroup.of 1) ^ s)
      (by simpa [Toroid.r] using tr.2.2.2.2)
    simpa using this
  have h23 : (D.σ ((2 : Fin 4) : ℤ) * D.σ ((3 : Fin 4) : ℤ)) ^ 4 = 1 := by
    have := hvertex ((FreeGroup.of 1 * FreeGroup.of 2) ^ 4) (by simpa [Toroid.r] using tv.2.2.1)
    simpa using this
  have hv : (D.σ ((1 : Fin 4) : ℤ) * D.σ ((2 : Fin 4) : ℤ) * D.σ ((3 : Fin 4) : ℤ) *
      D.σ ((2 : Fin 4) : ℤ)) ^ u = 1 := by
    have := hvertex ((FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 2 * FreeGroup.of 1) ^ u)
      (by simpa [Toroid.r] using tv.2.2.2.2)
    simpa using this
  let π := toGroup s u (fun i : Fin 4 => D.σ i) hσ2 h01 h12 h23 (hcomm 0 2 (by decide))
    (hcomm 0 3 (by decide)) (hcomm 1 3 (by decide)) ht hv
  have hπ : ∀ i : Fin 4, π ((gammaC s u hs hu hs3 hu3 hsu).ρ i) = D.σ i := fun i =>
    toGroup_r ..
  have hsurj : Function.Surjective π := by
    intro τ
    have hle : Subgroup.closure (Set.range fun i : Fin 4 => D.σ i) ≤ π.range := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨Universal.r s u i, toGroup_r ..⟩
    obtain ⟨g, hg⟩ := hle (D.mem_closure hQ τ)
    exact ⟨g, hg⟩
  refine ⟨π, hsurj, ⟨D.Φ, ?_⟩, (gammaC s u hs hu hs3 hu3 hsu).cov D π,
    (gammaC s u hs hu hs3 hu3 hsu).isCovering_cov hQ D π hπ (fun τ => ?_) hreg⟩
  · intro i F hF
    rw [show π (Universal.r s u i) = D.σ i from toGroup_r ..]
    have hFr := hQ.rank_mem F
    rw [D.mem_Φ hQ hF]
    rw [D.φ_rank _ hFr.1 hFr.2]
    by_cases h : rank F = i
    · rw [h, D.σ_φi _ (by omega) (by have := i.isLt; omega)]
      exact ⟨fun e => absurd e (D.φ'_ne _ (by omega) (by have := i.isLt; omega)),
        fun e => absurd rfl e⟩
    · rw [D.σ_φ _ (by omega) (by have := i.isLt; omega) _ hFr.1 hFr.2 h]
      exact ⟨fun _ => h, fun _ => rfl⟩
  · obtain ⟨x, rfl⟩ := hsurj τ
    exact ⟨x, by rw [gammaC_group]; trivial, rfl⟩

end Assembly

end P16c

namespace P16c

open Universal

universe v

theorem p16c_polytope_proof (s u : ℕ) (hs : Odd s) (hu : Odd u) (hs3 : 3 ≤ s) (hu3 : 3 ≤ u)
    (hsu : s ≠ u) :
    (IsPolytope (ToroidalMap s hs hs3) 3 (toroidC s hs hs3).rank ∧
      IsRegular (ToroidalMap s hs hs3)) ∧
    (IsPolytope (ToroidalMap u hu hu3) 3 (toroidC u hu hu3).rank ∧
      IsRegular (ToroidalMap u hu hu3)) ∧
    (IsPolytope (gammaC s u hs hu hs3 hu3 hsu).Face 4 (gammaC s u hs hu hs3 hu3 hsu).rank ∧
      IsRegular (gammaC s u hs hu hs3 hu3 hsu).Face ∧
      (∀ F, (gammaC s u hs hu hs3 hu3 hsu).rank F = 3 →
        Nonempty (Set.Iic F ≃o ToroidalMap s hs hs3)) ∧
      (∀ v, (gammaC s u hs hu hs3 hu3 hsu).rank v = 0 →
        Nonempty (Set.Ici v ≃o ToroidalMap u hu hu3)) ∧
      ∃ e : Gamma s u ≃* ((gammaC s u hs hu hs3 hu3 hsu).Face ≃o
          (gammaC s u hs hu hs3 hu3 hsu).Face),
        ∀ (g : Gamma s u) (hg : g ∈ (gammaC s u hs hu hs3 hu3 hsu).group),
          e g = (gammaC s u hs hu hs3 hu3 hsu).act ⟨g, hg⟩) ∧
    ∀ (Q : Type v) [PartialOrder Q] (rank : Q → ℤ), IsPolytope Q 4 rank → IsRegular Q →
      (∀ F : Q, rank F = 3 → Nonempty (Set.Iic F ≃o ToroidalMap s hs hs3)) →
      (∀ v : Q, rank v = 0 → Nonempty (Set.Ici v ≃o ToroidalMap u hu hu3)) →
      ∃ π : Gamma s u →* (Q ≃o Q), Function.Surjective π ∧
        (∃ Φ : Flag Q, ∀ i : Fin 4, ∀ F ∈ Φ, (π (Universal.r s u i) F = F ↔ rank F ≠ i)) ∧
        ∃ c : (gammaC s u hs hu hs3 hu3 hsu).Face → Q,
          IsCovering (gammaC s u hs hu hs3 hu3 hsu).rank rank c := by
  set Γ := gammaC s u hs hu hs3 hu3 hsu
  have htop := gammaC_group s u hs hu hs3 hu3 hsu
  refine ⟨⟨(toroidC s hs hs3).isPolytope, (toroidC s hs hs3).isRegular⟩,
    ⟨(toroidC u hu hu3).isPolytope, (toroidC u hu hu3).isRegular⟩,
    ⟨Γ.isPolytope, Γ.isRegular, gamma_facets hs hu hs3 hu3 hsu,
      gamma_vertexFigures hs hu hs3 hu3 hsu, ?_⟩,
    fun Q _ rank hQ hreg hfac hvf => gamma_universal hs hu hs3 hu3 hsu hQ hreg hfac hvf⟩
  refine ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans
    (MulEquiv.ofBijective Γ.act Γ.act_bijective), fun g hg => rfl⟩

end P16c
