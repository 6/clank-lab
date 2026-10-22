import Mathlib
import P16c.StringC
import P16c.StringCCross

namespace P16c

variable {G H : Type*} [Group G] [Group H] {n : ℕ}

/-- The intersection property restricted to subsets of `S`, in the ambient group. -/
def IntersectionOn (g : Fin n → G) (S : Finset (Fin n)) : Prop :=
  ∀ I J : Finset (Fin n), I ⊆ S → J ⊆ S →
    parabolic g I ⊓ parabolic g J = parabolic g (I ∩ J)

lemma parabolic_mono (g : Fin n → G) {I J : Finset (Fin n)} (h : I ⊆ J) :
    parabolic g I ≤ parabolic g J := by
  apply Subgroup.closure_mono
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨i, h hi, rfl⟩

@[simp] lemma parabolic_empty (g : Fin n → G) : parabolic g ∅ = ⊥ := by
  simp [parabolic]

lemma intersectionOn_mono (g : Fin n → G) {S T : Finset (Fin n)}
    (h : S ⊆ T) (hT : IntersectionOn g T) : IntersectionOn g S := by
  intro I J hI hJ
  exact hT I J (hI.trans h) (hJ.trans h)

/-- Checking maximal proper generator subsets suffices, also within a specified
set of indices. -/
theorem intersectionOn_of_maximal (g : Fin n → G) (S : Finset (Fin n))
    (hlocal : ∀ i ∈ S, IntersectionOn g (S.erase i))
    (hmeet : ∀ i ∈ S, ∀ j ∈ S,
      parabolic g (S.erase i) ⊓ parabolic g (S.erase j) =
        parabolic g ((S.erase i) ∩ (S.erase j))) : IntersectionOn g S := by
  intro I J hIS hJS
  classical
  by_cases hI : I = S
  · subst I
    simpa [Finset.inter_eq_right.mpr hJS] using inf_eq_right.mpr (parabolic_mono g hJS)
  by_cases hJ : J = S
  · subst J
    simpa [Finset.inter_eq_left.mpr hIS] using inf_eq_left.mpr (parabolic_mono g hIS)
  obtain ⟨i, hiS, hi⟩ : ∃ i, i ∈ S ∧ i ∉ I := by
    by_contra! h
    exact hI (Finset.Subset.antisymm hIS (by intro i hi; exact h i hi))
  obtain ⟨j, hjS, hj⟩ : ∃ j, j ∈ S ∧ j ∉ J := by
    by_contra! h
    exact hJ (Finset.Subset.antisymm hJS (by intro j hj; exact h j hj))
  have hIi : I ⊆ S.erase i := by
    intro a ha
    exact Finset.mem_erase.mpr ⟨by rintro rfl; exact hi ha, hIS ha⟩
  have hJj : J ⊆ S.erase j := by
    intro a ha
    exact Finset.mem_erase.mpr ⟨by rintro rfl; exact hj ha, hJS ha⟩
  apply le_antisymm
  · intro x hx
    have hxmax : x ∈ parabolic g ((S.erase i) ∩ (S.erase j)) := by
      rw [← hmeet i hiS j hjS]
      exact ⟨parabolic_mono g hIi hx.1, parabolic_mono g hJj hx.2⟩
    have hcut : x ∈ parabolic g (I ∩ (S.erase j)) := by
      have hloc := hlocal i hiS I ((S.erase i) ∩ (S.erase j)) hIi Finset.inter_subset_left
      have hx' : x ∈ parabolic g (I ∩ ((S.erase i) ∩ (S.erase j))) := by
        rw [← hloc]
        exact ⟨hx.1, hxmax⟩
      have heq : I ∩ ((S.erase i) ∩ (S.erase j)) = I ∩ (S.erase j) := by
        ext a
        simp only [Finset.mem_inter]
        exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hIi h.1, h.2⟩⟩
      rw [heq] at hx'
      exact hx'
    have heq : (I ∩ (S.erase j)) ∩ J = I ∩ J := by
      ext a
      simp only [Finset.mem_inter]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hJj h.2⟩, h.2⟩⟩
    rw [← heq, ← hlocal j hjS _ _ Finset.inter_subset_right hJj]
    exact ⟨hcut, hx.2⟩
  · exact le_inf (parabolic_mono g Finset.inter_subset_left)
      (parabolic_mono g Finset.inter_subset_right)

lemma intersectionOn_empty (g : Fin n → G) : IntersectionOn g ∅ := by
  intro I J hI hJ
  have : I = ∅ := Finset.subset_empty.mp hI
  subst I
  simp

lemma intersectionOn_singleton (g : Fin n → G) (i : Fin n) : IntersectionOn g {i} := by
  intro I J hI hJ
  obtain rfl | rfl := Finset.subset_singleton_iff.mp hI
  · simp
  obtain rfl | rfl := Finset.subset_singleton_iff.mp hJ
  · simp
  simp

lemma parabolic_union (g : Fin n → G) (A B : Finset (Fin n)) :
    parabolic g (A ∪ B) = parabolic g A ⊔ parabolic g B := by
  simp [parabolic, Set.image_union, Subgroup.closure_union]

lemma parabolic_le_centralizer (g : Fin n → G) (A B : Finset (Fin n))
    (hc : ∀ i ∈ A, ∀ j ∈ B, Commute (g i) (g j)) :
    parabolic g A ≤ Subgroup.centralizer (parabolic g B : Set G) := by
  simp only [parabolic, Subgroup.centralizer_closure]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
  exact (hc i hi j hj).eq.symm

/-- A commuting join has the elementary factorization expected of a direct
product; injectivity or trivial intersection is not required here. -/
lemma mem_sup_factor {A B : Subgroup G}
    (hc : A ≤ Subgroup.centralizer (B : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  change x ∈ (↑(A ⊔ B) : Set G) at hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A B
    (hc.trans (Subgroup.centralizer_le_normalizer _))] at hx
  exact hx

lemma commuting_sup_inf {A B C : Subgroup G}
    (hc : A ≤ Subgroup.centralizer (B : Set G)) (hAC : A ≤ C) :
    (A ⊔ B) ⊓ C = A ⊔ (B ⊓ C) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_factor hc hx.1
    have hbC : b ∈ C := by
      have := C.mul_mem (C.inv_mem (hAC ha)) hx.2
      simpa using this
    exact Subgroup.mul_mem_sup ha ⟨hb, hbC⟩
  · exact sup_le (le_inf le_sup_left hAC)
      (le_inf (inf_le_left.trans le_sup_right) inf_le_right)

lemma commuting_factors_unique {A B : Subgroup G} (hdis : A ⊓ B = ⊥)
    {a b c d : G} (ha : a ∈ A) (hb : b ∈ B) (hc : c ∈ A) (hd : d ∈ B)
    (heq : a * b = c * d) : a = c ∧ b = d := by
  have h : a⁻¹ * c = b * d⁻¹ := by
    calc
      a⁻¹ * c = a⁻¹ * (c * d) * d⁻¹ := by simp [mul_assoc]
      _ = a⁻¹ * (a * b) * d⁻¹ := by rw [heq]
      _ = b * d⁻¹ := by simp
  have hone : a⁻¹ * c = 1 := by
    have hmem : a⁻¹ * c ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem ha) hc, h ▸ B.mul_mem hb (B.inv_mem hd)⟩
    rw [hdis] at hmem
    exact hmem
  have hac : a = c := (inv_mul_eq_one.mp hone)
  refine ⟨hac, ?_⟩
  simpa [hac] using heq

/-- Disjoint commuting factors inherit the intersection property componentwise. -/
theorem intersectionOn_union (g : Fin n → G) (A B : Finset (Fin n))
    (hA : IntersectionOn g A) (hB : IntersectionOn g B)
    (hdis : parabolic g A ⊓ parabolic g B = ⊥)
    (hc : ∀ i ∈ A, ∀ j ∈ B, Commute (g i) (g j)) :
    IntersectionOn g (A ∪ B) := by
  intro I J hI hJ
  have hsplit (T : Finset (Fin n)) (hT : T ⊆ A ∪ B) : T = (T ∩ A) ∪ (T ∩ B) := by
    ext i
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro hi
      rcases Finset.mem_union.mp (hT hi) with h | h
      · exact Or.inl ⟨hi, h⟩
      · exact Or.inr ⟨hi, h⟩
    · tauto
  have hfactor (T : Finset (Fin n)) (hT : T ⊆ A ∪ B) {x : G}
      (hx : x ∈ parabolic g T) :
      ∃ a ∈ parabolic g (T ∩ A), ∃ b ∈ parabolic g (T ∩ B), a * b = x := by
    have heq : parabolic g T = parabolic g (T ∩ A) ⊔ parabolic g (T ∩ B) := by
      conv_lhs => rw [hsplit T hT]
      exact parabolic_union _ _ _
    rw [heq] at hx
    exact mem_sup_factor (parabolic_le_centralizer _ _ _
      (fun i hi j hj => hc i (Finset.mem_inter.mp hi).2 j (Finset.mem_inter.mp hj).2)) hx
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, b, hb, hab⟩ := hfactor I hI hx.1
    obtain ⟨c, hc', d, hd, hcd⟩ := hfactor J hJ hx.2
    obtain ⟨rfl, rfl⟩ := commuting_factors_unique hdis
      (parabolic_mono g Finset.inter_subset_right ha)
      (parabolic_mono g Finset.inter_subset_right hb)
      (parabolic_mono g Finset.inter_subset_right hc')
      (parabolic_mono g Finset.inter_subset_right hd) (hab.trans hcd.symm)
    have haIJ : a ∈ parabolic g ((I ∩ A) ∩ (J ∩ A)) := by
      rw [← hA _ _ Finset.inter_subset_right Finset.inter_subset_right]
      exact ⟨ha, hc'⟩
    have hbIJ : b ∈ parabolic g ((I ∩ B) ∩ (J ∩ B)) := by
      rw [← hB _ _ Finset.inter_subset_right Finset.inter_subset_right]
      exact ⟨hb, hd⟩
    rw [← hab]
    apply Subgroup.mul_mem
    · exact parabolic_mono g (by intro i hi; exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hi).1).1, (Finset.mem_inter.mp (Finset.mem_inter.mp hi).2).1⟩) haIJ
    · exact parabolic_mono g (by intro i hi; exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hi).1).1, (Finset.mem_inter.mp (Finset.mem_inter.mp hi).2).1⟩) hbIJ
  · exact le_inf (parabolic_mono g Finset.inter_subset_left)
      (parabolic_mono g Finset.inter_subset_right)

lemma parabolic_reindex {m : ℕ} (g : Fin n → G) (f : Fin m → Fin n)
    (I : Finset (Fin m)) :
    parabolic (fun i => g (f i)) I = parabolic g (I.image f) := by
  simp [parabolic, Finset.coe_image, Set.image_image]

lemma intersectionOn_reindex {m : ℕ} (g : Fin n → G) (f : Fin m → Fin n)
    (hf : Function.Injective f)
    (h : ∀ I J : Finset (Fin m),
      parabolic (fun i => g (f i)) I ⊓ parabolic (fun i => g (f i)) J =
        parabolic (fun i => g (f i)) (I ∩ J)) :
    IntersectionOn g (Finset.univ.image f) := by
  intro I J hI hJ
  classical
  have himage (T : Finset (Fin n)) (hT : T ⊆ Finset.univ.image f) :
      (T.preimage f hf.injOn).image f = T := by
    ext i
    simp only [Finset.mem_image, Finset.mem_preimage]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact hj
    · intro hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (hT hi)
      exact ⟨j, hi, rfl⟩
  have h' := h (I.preimage f hf.injOn) (J.preimage f hf.injOn)
  simp only [parabolic_reindex] at h'
  rw [Finset.image_inter _ _ hf, himage I hI, himage J hJ] at h'
  exact h'

lemma intersection_cross (g : Fin n → G) (F V : Finset (Fin n))
    (hF : IntersectionOn g F) (hV : IntersectionOn g V)
    (hmeet : parabolic g F ⊓ parabolic g V = parabolic g (F ∩ V))
    (A B : Finset (Fin n)) (hA : A ⊆ F) (hB : B ⊆ V) :
    parabolic g A ⊓ parabolic g B = parabolic g (A ∩ B) := by
  apply le_antisymm
  · intro x hx
    have hxM : x ∈ parabolic g (F ∩ V) := by
      rw [← hmeet]
      exact ⟨parabolic_mono g hA hx.1, parabolic_mono g hB hx.2⟩
    have hxA : x ∈ parabolic g (A ∩ (F ∩ V)) := by
      rw [← hF _ _ hA Finset.inter_subset_left]
      exact ⟨hx.1, hxM⟩
    have hxAB : x ∈ parabolic g ((A ∩ (F ∩ V)) ∩ B) := by
      rw [← hV _ _ (Finset.inter_subset_right.trans Finset.inter_subset_right) hB]
      exact ⟨hxA, hx.2⟩
    exact parabolic_mono g (by
      intro i hi
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hi).1).1,
        (Finset.mem_inter.mp hi).2⟩) hxAB
  · exact le_inf (parabolic_mono g Finset.inter_subset_left)
      (parabolic_mono g Finset.inter_subset_right)

lemma commute_of_involutions {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : (a * b) ^ 2 = 1) : Commute a b := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hb)
  have hab' : (a * b)⁻¹ = a * b :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hab)
  exact (by simpa [ha', hb'] using hab'.symm : a * b = b * a)

set_option maxHeartbeats 1200000 in
/-- The rank-three form of the facet/vertex intersection criterion. -/
theorem stringC_rank3 (g : Fin 3 → G)
    (hi : ∀ i, g i ^ 2 = 1)
    (hs : ∀ i j, i.val + 2 ≤ j.val → (g i * g j) ^ 2 = 1)
    (hF : IsStringCGroup (fun i : Fin 2 => g i.castSucc))
    (hV : IsStringCGroup (fun i : Fin 2 => g i.succ))
    (hmeet : parabolic g {0, 1} ⊓ parabolic g {1, 2} = parabolic g {1}) :
    IsStringCGroup g := by
  have hF' : IntersectionOn g {0, 1} := by
    have h := intersectionOn_reindex g Fin.castSucc (Fin.castSucc_injective 2) hF.2.2
    convert h using 1; decide
  have hV' : IntersectionOn g {1, 2} := by
    have h := intersectionOn_reindex g Fin.succ (Fin.succ_injective 2) hV.2.2
    convert h using 1; decide
  have hcross := intersection_cross g {0, 1} {1, 2} hF' hV'
    (by simpa using hmeet)
  have h02 : parabolic g {0} ⊓ parabolic g {2} = ⊥ := by
    simpa using hcross {0} {2} (by decide) (by decide)
  have hc02 : Commute (g 0) (g 2) := commute_of_involutions (hi 0) (hi 2) (hs 0 2 (by decide))
  have hE : IntersectionOn g {0, 2} := by
    have h := intersectionOn_union g {0} {2}
      (intersectionOn_singleton _ _) (intersectionOn_singleton _ _) h02
      (by simpa using hc02)
    simpa using h
  have hEF : parabolic g {0, 2} ⊓ parabolic g {0, 1} = parabolic g {0} := by
    have h20F : parabolic g {2} ⊓ parabolic g {0, 1} = ⊥ := by
      simpa [inf_comm] using hcross {0, 1} {2} (by decide) (by decide)
    have h := commuting_sup_inf (parabolic_le_centralizer g {0} {2}
      (by simpa using hc02)) (parabolic_mono g (by decide : ({0} : Finset (Fin 3)) ⊆ {0, 1}))
    rw [h20F] at h
    simpa [← parabolic_union] using h
  have hEV : parabolic g {0, 2} ⊓ parabolic g {1, 2} = parabolic g {2} := by
    have h0V : parabolic g {0} ⊓ parabolic g {1, 2} = ⊥ := by
      simpa using hcross {0} {1, 2} (by decide) (by decide)
    have h := commuting_sup_inf (parabolic_le_centralizer g {2} {0}
      (by simpa using hc02.symm)) (parabolic_mono g (by decide : ({2} : Finset (Fin 3)) ⊆ {1, 2}))
    rw [h0V] at h
    simpa [← parabolic_union, Finset.pair_comm] using h
  refine ⟨hi, hs, ?_⟩
  have hu : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  have hfull : IntersectionOn g Finset.univ := by
    apply intersectionOn_of_maximal
    · intro i _
      fin_cases i
      · simpa [hu, Finset.erase_insert_of_ne, Finset.inter_insert] using hV'
      · simpa [hu, Finset.erase_insert_of_ne, Finset.inter_insert] using hE
      · simpa [hu, Finset.erase_insert_of_ne, Finset.inter_insert] using hF'
    · intro i _ j _
      fin_cases i <;> fin_cases j <;> first
        | solve | simp [hu, Finset.erase_insert_of_ne]
        | simpa [hu, Finset.erase_insert_of_ne, Finset.inter_insert, inf_comm, Finset.pair_comm] using hEV
        | simpa [hu, Finset.erase_insert_of_ne, Finset.inter_insert, inf_comm, Finset.pair_comm] using hEF
        | simpa [hu, Finset.erase_insert_of_ne, Finset.inter_insert, inf_comm, Finset.pair_comm] using hmeet
  exact fun I J => hfull I J (Finset.subset_univ _) (Finset.subset_univ _)

set_option maxHeartbeats 2000000 in
/-- The rank-four facet/vertex criterion (ARP 2E16(a)), with every subset,
including the empty subset, in the resulting intersection property. -/
theorem stringC_rank4 (g : Fin 4 → G)
    (hi : ∀ i, g i ^ 2 = 1)
    (hs : ∀ i j, i.val + 2 ≤ j.val → (g i * g j) ^ 2 = 1)
    (hF : IsStringCGroup (fun i : Fin 3 => g i.castSucc))
    (hV : IsStringCGroup (fun i : Fin 3 => g i.succ))
    (hmeet : parabolic g {0, 1, 2} ⊓ parabolic g {1, 2, 3} = parabolic g {1, 2}) :
    IsStringCGroup g := by
  have hF' : IntersectionOn g {0, 1, 2} := by
    have h := intersectionOn_reindex g Fin.castSucc (Fin.castSucc_injective 3) hF.2.2
    convert h using 1; decide
  have hV' : IntersectionOn g {1, 2, 3} := by
    have h := intersectionOn_reindex g Fin.succ (Fin.succ_injective 3) hV.2.2
    convert h using 1; decide
  have hcross := intersection_cross g {0, 1, 2} {1, 2, 3} hF' hV'
    (by simpa [Finset.inter_insert] using hmeet)
  have hc (i j : Fin 4) (hij : i.val + 2 ≤ j.val) : Commute (g i) (g j) :=
    commute_of_involutions (hi i) (hi j) (hs i j hij)
  have hc0_23 : ∀ i ∈ ({0} : Finset (Fin 4)), ∀ j ∈ ({2, 3} : Finset (Fin 4)),
      Commute (g i) (g j) := by
    intro i hi j hj
    have hi' : i = 0 := by simpa [Finset.insert_comm] using hi
    subst i
    apply hc
    fin_cases j <;> simp_all
  have hc01_3 : ∀ i ∈ ({0, 1} : Finset (Fin 4)), ∀ j ∈ ({3} : Finset (Fin 4)),
      Commute (g i) (g j) := by
    intro i hi j hj
    have hj' : j = 3 := by simpa [Finset.insert_comm] using hj
    subst j
    apply hc
    fin_cases i <;> simp_all
  have hd0_23 : parabolic g {0} ⊓ parabolic g {2, 3} = ⊥ := by
    simpa [Finset.inter_insert] using hcross {0} {2, 3} (by decide) (by decide)
  have hd01_3 : parabolic g {0, 1} ⊓ parabolic g {3} = ⊥ := by
    simpa [Finset.inter_insert] using hcross {0, 1} {3} (by decide) (by decide)
  have hM1 : IntersectionOn g {0, 2, 3} := by
    have h := intersectionOn_union g {0} {2, 3} (intersectionOn_singleton _ _)
      (intersectionOn_mono g (by decide : ({2, 3} : Finset (Fin 4)) ⊆ {1, 2, 3}) hV')
      hd0_23 hc0_23
    convert h using 3 ; decide
  have hM2 : IntersectionOn g {0, 1, 3} := by
    have h := intersectionOn_union g {0, 1} {3}
      (intersectionOn_mono g (by decide : ({0, 1} : Finset (Fin 4)) ⊆ {0, 1, 2}) hF')
      (intersectionOn_singleton _ _) hd01_3 hc01_3
    convert h using 3 ; decide
  have hM1F : parabolic g {0, 2, 3} ⊓ parabolic g {0, 1, 2} = parabolic g {0, 2} := by
    have h23F : parabolic g {2, 3} ⊓ parabolic g {0, 1, 2} = parabolic g {2} := by
      simpa [inf_comm, Finset.inter_insert] using
        hcross {0, 1, 2} {2, 3} (by decide) (by decide)
    have h := commuting_sup_inf (parabolic_le_centralizer g {0} {2, 3} hc0_23)
      (parabolic_mono g (by decide : ({0} : Finset (Fin 4)) ⊆ {0, 1, 2}))
    rw [h23F] at h
    simp only [← parabolic_union] at h
    convert h using 3 <;> decide
  have hM1V : parabolic g {0, 2, 3} ⊓ parabolic g {1, 2, 3} = parabolic g {2, 3} := by
    have h0V : parabolic g {0} ⊓ parabolic g {1, 2, 3} = ⊥ := by
      simpa [Finset.inter_insert] using hcross {0} {1, 2, 3} (by decide) (by decide)
    have h := commuting_sup_inf (parabolic_le_centralizer g {2, 3} {0}
      (fun i hi j hj => (hc0_23 j hj i hi).symm))
      (parabolic_mono g (by decide : ({2, 3} : Finset (Fin 4)) ⊆ {1, 2, 3}))
    rw [h0V] at h
    simp only [← parabolic_union, sup_bot_eq] at h
    convert h using 3 ; decide
  have hM2F : parabolic g {0, 1, 3} ⊓ parabolic g {0, 1, 2} = parabolic g {0, 1} := by
    have h3F : parabolic g {3} ⊓ parabolic g {0, 1, 2} = ⊥ := by
      simpa [inf_comm, Finset.inter_insert] using
        hcross {0, 1, 2} {3} (by decide) (by decide)
    have h := commuting_sup_inf (parabolic_le_centralizer g {0, 1} {3} hc01_3)
      (parabolic_mono g (by decide : ({0, 1} : Finset (Fin 4)) ⊆ {0, 1, 2}))
    rw [h3F] at h
    simp only [← parabolic_union, sup_bot_eq] at h
    convert h using 3 ; decide
  have hM2V : parabolic g {0, 1, 3} ⊓ parabolic g {1, 2, 3} = parabolic g {1, 3} := by
    have h01V : parabolic g {0, 1} ⊓ parabolic g {1, 2, 3} = parabolic g {1} := by
      simpa [Finset.inter_insert] using hcross {0, 1} {1, 2, 3} (by decide) (by decide)
    have h := commuting_sup_inf (parabolic_le_centralizer g {3} {0, 1}
      (fun i hi j hj => (hc01_3 j hj i hi).symm))
      (parabolic_mono g (by decide : ({3} : Finset (Fin 4)) ⊆ {1, 2, 3}))
    rw [h01V] at h
    simp only [← parabolic_union] at h
    convert h using 3 <;> decide
  have hM1M2 : parabolic g {0, 2, 3} ⊓ parabolic g {0, 1, 3} = parabolic g {0, 3} := by
    have h0123 : parabolic g {0, 1} ⊓ parabolic g {2, 3} = ⊥ := by
      simpa [Finset.inter_insert] using hcross {0, 1} {2, 3} (by decide) (by decide)
    have h := cross_sup_inf (parabolic g {0}) (parabolic g {2, 3})
      (parabolic g {0, 1}) (parabolic g {3})
      (parabolic_mono g (by decide)) (parabolic_mono g (by decide)) h0123
      (fun a ha b hb => (parabolic_le_centralizer g _ _ hc0_23 ha b hb).symm)
      (fun a ha b hb => (parabolic_le_centralizer g _ _ hc01_3 ha b hb).symm)
    simp only [← parabolic_union] at h
    convert h using 3 <;> decide
  refine ⟨hi, hs, ?_⟩
  have hu : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  have hfull : IntersectionOn g Finset.univ := by
    apply intersectionOn_of_maximal
    · intro i _
      fin_cases i
      · simpa [hu, Finset.erase_insert_of_ne] using hV'
      · simpa [hu, Finset.erase_insert_of_ne] using hM1
      · simpa [hu, Finset.erase_insert_of_ne] using hM2
      · simpa [hu, Finset.erase_insert_of_ne] using hF'
    · intro i _ j _
      fin_cases i <;> fin_cases j <;> first
        | solve | simp [hu, Finset.erase_insert_of_ne]
        | simpa [hu, Finset.erase_insert_of_ne, Finset.inter_insert, inf_comm] using hM1F
        | simpa [hu, Finset.erase_insert_of_ne, Finset.inter_insert, inf_comm] using hM1V
        | simpa [hu, Finset.erase_insert_of_ne, Finset.inter_insert, inf_comm] using hM2F
        | simpa [hu, Finset.erase_insert_of_ne, Finset.inter_insert, inf_comm] using hM2V
        | simpa [hu, Finset.erase_insert_of_ne, Finset.inter_insert, inf_comm] using hM1M2
        | simpa [hu, Finset.erase_insert_of_ne, Finset.inter_insert, inf_comm] using hmeet
  exact fun I J => hfull I J (Finset.subset_univ _) (Finset.subset_univ _)

end P16c
