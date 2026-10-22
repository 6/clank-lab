import Mathlib

namespace P16c.Toroid

/-- The square toroid presentation, including its period relation. -/
def rels (s : ℕ) : Set (FreeGroup (Fin 3)) :=
  {w | (∃ i, w = FreeGroup.of i ^ 2) ∨
    w = (FreeGroup.of 0 * FreeGroup.of 1) ^ 4 ∨
    w = (FreeGroup.of 1 * FreeGroup.of 2) ^ 4 ∨
    w = (FreeGroup.of 0 * FreeGroup.of 2) ^ 2 ∨
    w = (FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 2 * FreeGroup.of 1) ^ s}

abbrev G (s : ℕ) := PresentedGroup (rels s)
def r (s : ℕ) (i : Fin 3) : G s := PresentedGroup.of i

lemma relations (s : ℕ) :
    (∀ i, r s i ^ 2 = 1) ∧ (r s 0 * r s 1) ^ 4 = 1 ∧
    (r s 1 * r s 2) ^ 4 = 1 ∧ (r s 0 * r s 2) ^ 2 = 1 ∧
    (r s 0 * r s 1 * r s 2 * r s 1) ^ s = 1 := by
  refine ⟨fun i => ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [r]
  · exact PresentedGroup.one_of_mem (Or.inl ⟨i, rfl⟩)
  · exact PresentedGroup.one_of_mem (Or.inr (Or.inl rfl))
  · exact PresentedGroup.one_of_mem (Or.inr (Or.inr (Or.inl rfl)))
  · exact PresentedGroup.one_of_mem (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact PresentedGroup.one_of_mem (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

section Algebra
variable {H : Type*} [Group H] {a b c : H}

lemma braid_four (ha : a * a = 1) (hb : b * b = 1)
    (hab : (a * b) ^ 4 = 1) : a * b * a * b = b * a * b * a := by
  have hi : (a * b * a * b)⁻¹ = a * b * a * b := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using hab
  simpa only [mul_inv_rev, inv_eq_of_mul_eq_one_right ha,
    inv_eq_of_mul_eq_one_right hb, mul_assoc] using hi.symm

lemma commute_of_square (ha : a * a = 1) (hc : c * c = 1)
    (hac : (a * c) ^ 2 = 1) : a * c = c * a := by
  have hi := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hac : (a*c)*(a*c)=1)
  simpa [mul_inv_rev, inv_eq_of_mul_eq_one_right ha,
    inv_eq_of_mul_eq_one_right hc] using hi.symm

/-- The translation identities follow solely from the Coxeter relations. -/
lemma translation_identities (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : (a * b) ^ 4 = 1) (hbc : (b * c) ^ 4 = 1)
    (hac : (a * c) ^ 2 = 1) :
    let x := a * b * c * b
    let y := b * x * b
    Commute x y ∧ b * y * b = x ∧ c * x * c = x ∧ c * y * c = y⁻¹ := by
  have hiA : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hiB : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hiC : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have hAB := braid_four ha hb hab
  have hBC := braid_four hb hc hbc
  have hAC := commute_of_square ha hc hac
  dsimp
  have hy : b * (a * b * c * b) * b = b * a * b * c := by
    simp [mul_assoc, hb]
  rw [hy]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (a * b * c * b) * (b * a * b * c) = (b * a * b * c) * (a * b * c * b)
    calc
      _ = a * b * (c * a) * b * c := by simp [mul_assoc, ← mul_assoc b b, hb]
      _ = a * b * (a * c) * b * c := by rw [hAC]
      _ = (a * b * a * b) * (c * b * c * b) := by
        rw [← hBC]
        simp [mul_assoc, ← mul_assoc b b, hb]
      _ = (b * a * b * a) * (c * b * c * b) := by rw [hAB]
      _ = b * a * b * (a * c) * b * c * b := by group
      _ = b * a * b * (c * a) * b * c * b := by rw [hAC]
      _ = _ := by group
  · simp [mul_assoc, ← mul_assoc b b, hb]
  · calc
      c * (a * b * c * b) * c = (c * a) * (b * c * b * c) := by group
      _ = (a * c) * (c * b * c * b) := by rw [← hAC, hBC]
      _ = _ := by simp [mul_assoc, ← mul_assoc c c, hc]
  · simp [mul_inv_rev, hiA, hiB, hiC, mul_assoc, hc]
end Algebra

lemma involution_normalizes_closure {G : Type*} [Group G] (q : G) (hq : q * q = 1)
    (S : Set G) (hS : ∀ x ∈ S, q * x * q ∈ Subgroup.closure S) :
    q ∈ Subgroup.normalizer (Subgroup.closure S : Set G) := by
  have hi : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq
  have hconj : ∀ x ∈ Subgroup.closure S, q * x * q ∈ Subgroup.closure S := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hS x hx
    | one => simp [hq]
    | mul x y hx hy ihx ihy =>
      have he : q * (x * y) * q = (q * x * q) * (q * y * q) := by simp [mul_assoc, ← mul_assoc q q, hq]
      rw [he]
      exact (Subgroup.closure S).mul_mem ihx ihy
    | inv x hx ih =>
      have he : q * x⁻¹ * q = (q * x * q)⁻¹ := by simp [mul_inv_rev, hi, mul_assoc]
      rw [he]
      exact (Subgroup.closure S).inv_mem ih
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [hi]
  refine ⟨hconj x, fun hx => ?_⟩
  simpa [mul_assoc, ← mul_assoc q q, hq] using hconj (q * x * q) hx


section Counting
variable {H : Type*} [Group H]
open scoped Pointwise

/-- Multiplication covers a supremum when the right subgroup normalizes the left. -/
lemma finite_sup_card (N D : Subgroup H) [Finite N] [Finite D]
    (hn : D ≤ Subgroup.normalizer N) :
    Finite (N ⊔ D : Subgroup H) ∧ Nat.card (N ⊔ D : Subgroup H) ≤ Nat.card N * Nat.card D := by
  let f : N × D → (N ⊔ D : Subgroup H) :=
    fun p => ⟨(p.1 : H) * p.2, Subgroup.mul_mem_sup p.1.property p.2.property⟩
  have hf : Function.Surjective f := by
    intro z
    have hz : (z : H) ∈ ((N : Set H) * (D : Set H)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left N D hn]
      exact z.property
    obtain ⟨n, hn, d, hd, heq⟩ := hz
    exact ⟨(⟨n, hn⟩, ⟨d, hd⟩), Subtype.ext heq⟩
  exact ⟨Finite.of_surjective f hf, (Nat.card_le_card_of_surjective f hf).trans_eq (Nat.card_prod _ _)⟩

lemma cyclic_finite_card (x : H) (n : ℕ) (hn : 0 < n) (hx : x ^ n = 1) :
    Finite (Subgroup.zpowers x) ∧ Nat.card (Subgroup.zpowers x) ≤ n := by
  have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hx⟩
  exact ⟨hfin.finite_zpowers.to_subtype,
    (Nat.card_zpowers x).le.trans (Nat.le_of_dvd hn (orderOf_dvd_of_pow_eq_one hx))⟩

/-- Two commuting elements whose orders divide n generate at most n² elements. -/
lemma pair_finite_card (x y : H) (n : ℕ) (hn : 0 < n)
    (hx : x ^ n = 1) (hy : y ^ n = 1) (hc : Commute x y) :
    Finite (Subgroup.closure ({x, y} : Set H)) ∧
      Nat.card (Subgroup.closure ({x, y} : Set H)) ≤ n ^ 2 := by
  obtain ⟨fx, cx⟩ := cyclic_finite_card x n hn hx
  obtain ⟨fy, cy⟩ := cyclic_finite_card y n hn hy
  letI := fx
  letI := fy
  have hnorm : Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers x) := by
    rw [Subgroup.le_normalizer_iff]
    intro q hq z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hcomm := hc.symm.zpow_zpow i j
    simp [hcomm.eq, mul_assoc]
  have he : Subgroup.zpowers x ⊔ Subgroup.zpowers y = Subgroup.closure ({x, y} : Set H) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
  obtain ⟨ff, cc⟩ := finite_sup_card (Subgroup.zpowers x) (Subgroup.zpowers y) hnorm
  rw [he] at ff cc
  exact ⟨ff, cc.trans (by nlinarith [Nat.mul_le_mul cx cy])⟩
end Counting

/-- The subgroup generated by two involutions with product of period four has at most eight elements. -/
lemma dihedral_finite_card {H : Type*} [Group H] (b c : H)
    (hb : b * b = 1) (hc : c * c = 1) (hbc : (b * c) ^ 4 = 1) :
    Finite (Subgroup.closure ({b, c} : Set H)) ∧
      Nat.card (Subgroup.closure ({b, c} : Set H)) ≤ 8 := by
  let R := Subgroup.zpowers (b * c)
  let B := Subgroup.zpowers b
  obtain ⟨fr, cr⟩ := cyclic_finite_card (b * c) 4 (by omega) hbc
  obtain ⟨fb, cb⟩ := cyclic_finite_card b 2 (by omega) (by simpa [pow_two] using hb)
  letI := fr
  letI := fb
  have hn : B ≤ Subgroup.normalizer R := by
    apply Subgroup.zpowers_le.mpr
    dsimp [R]
    rw [Subgroup.zpowers_eq_closure]
    apply involution_normalizes_closure b hb
    intro x hx
    have hx' : x = b * c := Set.mem_singleton_iff.mp hx
    subst x
    have he : b * (b * c) * b = (b * c)⁻¹ := by
      simp [mul_inv_rev, inv_eq_of_mul_eq_one_right hb,
        inv_eq_of_mul_eq_one_right hc, ← mul_assoc b b, hb]
    rw [he]
    exact (Subgroup.closure {b * c}).inv_mem (Subgroup.subset_closure (by simp))
  have he : R ⊔ B = Subgroup.closure ({b, c} : Set H) := by
    apply le_antisymm
    · refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact (Subgroup.closure {b, c}).mul_mem
          (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
      · exact Subgroup.subset_closure (by simp)
    · apply (Subgroup.closure_le _).mpr
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      · have hz' : z = c := Set.mem_singleton_iff.mp hz
        subst z
        have hh : b * (b * c) = c := by simp [← mul_assoc, hb]
        rw [← hh]
        exact (R ⊔ B).mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers (b * c)))
  obtain ⟨ff, cc⟩ := finite_sup_card R B hn
  rw [he] at ff cc
  exact ⟨ff, cc.trans (by dsimp [R, B] at *; nlinarith [Nat.mul_le_mul cr cb])⟩

/-- Finiteness and the square-toroid upper bound, for every positive period. -/
theorem finite_card (s : ℕ) (hs : 0 < s) : Finite (G s) ∧ Nat.card (G s) ≤ 8 * s ^ 2 := by
  let a := r s 0
  let b := r s 1
  let c := r s 2
  let x := a * b * c * b
  let y := b * x * b
  let N := Subgroup.closure ({x, y} : Set (G s))
  let D := Subgroup.closure ({b, c} : Set (G s))
  obtain ⟨hi, hab, hbc, hac, hx⟩ := relations s
  have ha : a * a = 1 := by simpa [a, pow_two] using hi 0
  have hb : b * b = 1 := by simpa [b, pow_two] using hi 1
  have hc : c * c = 1 := by simpa [c, pow_two] using hi 2
  obtain ⟨hxy, hby, hcx, hcy⟩ := translation_identities ha hb hc hab hbc hac
  change Commute x y at hxy
  change b * y * b = x at hby
  change c * x * c = x at hcx
  change c * y * c = y⁻¹ at hcy
  have hy : y ^ s = 1 := by
    have he : y = b * x * b⁻¹ := by simp [y, inv_eq_of_mul_eq_one_right hb]
    rw [he, conj_pow, hx]
    simp
  obtain ⟨fn, cn⟩ := pair_finite_card x y s hs hx hy hxy
  obtain ⟨fd, cd⟩ := dihedral_finite_card b c hb hc hbc
  letI := fn
  letI := fd
  have hn : D ≤ Subgroup.normalizer N := by
    apply (Subgroup.closure_le _).mpr
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · apply involution_normalizes_closure b hb
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · exact Subgroup.subset_closure (by simp only [← show y = b * x * b from rfl]; simp)
      · have hz' : z = y := Set.mem_singleton_iff.mp hz
        subst z
        rw [hby]
        exact Subgroup.subset_closure (by simp)
    · have hz' : z = c := Set.mem_singleton_iff.mp hz
      subst z
      apply involution_normalizes_closure c hc
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · rw [hcx]; exact Subgroup.subset_closure (by simp)
      · have hz' : z = y := Set.mem_singleton_iff.mp hz
        subst z
        rw [hcy]
        exact N.inv_mem (Subgroup.subset_closure (by simp))
  have ht : N ⊔ D = ⊤ := by
    apply top_unique
    intro z _
    apply PresentedGroup.generated_by (rels s) (N ⊔ D) _ z
    intro i
    fin_cases i
    · change a ∈ N ⊔ D
      have he : a = x * b * c * b := by
        simp [x, mul_assoc, hb, hc]
      rw [he]
      have hxb : x ∈ N ⊔ D := Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      have hbb : b ∈ N ⊔ D := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
      have hcc : c ∈ N ⊔ D := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
      exact (N ⊔ D).mul_mem ((N ⊔ D).mul_mem ((N ⊔ D).mul_mem hxb hbb) hcc) hbb
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp [b, r]))
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp [c, r]))
  obtain ⟨ff, cc⟩ := finite_sup_card N D hn
  rw [ht] at ff cc
  letI := ff
  have fG : Finite (G s) := Finite.of_equiv _ (Subgroup.topEquiv.toEquiv : (⊤ : Subgroup (G s)) ≃ G s)
  refine ⟨fG, ?_⟩
  rw [Nat.card_congr (Subgroup.topEquiv.toEquiv : (⊤ : Subgroup (G s)) ≃ G s)] at cc
  exact cc.trans (by nlinarith [Nat.mul_le_mul cn cd])

section Bridge
variable {H : Type*} [Group H]

/-- The universal homomorphism from the explicitly specified toroid presentation. -/
def toGroup (s : ℕ) (f : Fin 3 → H) (hi : ∀ i, f i ^ 2 = 1)
    (h01 : (f 0 * f 1) ^ 4 = 1) (h12 : (f 1 * f 2) ^ 4 = 1)
    (h02 : (f 0 * f 2) ^ 2 = 1) (ht : (f 0 * f 1 * f 2 * f 1) ^ s = 1) :
    G s →* H :=
  PresentedGroup.toGroup (by
    intro w hw
    rcases hw with ⟨i, rfl⟩ | rfl | rfl | rfl | rfl
    · simpa using hi i
    · simpa using h01
    · simpa using h12
    · simpa using h02
    · simpa using ht)

@[simp] lemma toGroup_r (s : ℕ) (f : Fin 3 → H) (hi h01 h12 h02 ht) (i : Fin 3) :
    toGroup s f hi h01 h12 h02 ht (r s i) = f i := PresentedGroup.toGroup.of _

/-- Every homomorphism from this presentation has precisely the generated range. -/
lemma range_eq (s : ℕ) (φ : G s →* H) :
    φ.range = Subgroup.closure ({φ (r s 0), φ (r s 1), φ (r s 2)} : Set H) := by
  calc
    φ.range = (⊤ : Subgroup (G s)).map φ := φ.range_eq_map
    _ = (Subgroup.closure (Set.range (r s))).map φ := by
      have ht := PresentedGroup.closure_range_of (rels s)
      change Subgroup.closure (Set.range (r s)) = ⊤ at ht
      rw [ht]
    _ = Subgroup.closure (φ '' Set.range (r s)) := φ.map_closure _
    _ = _ := by
      congr 1
      ext z
      simp only [Set.mem_image, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        fin_cases i <;> simp
      · rintro (rfl | rfl | rfl)
        · exact ⟨r s 0, ⟨0, rfl⟩, rfl⟩
        · exact ⟨r s 1, ⟨1, rfl⟩, rfl⟩
        · exact ⟨r s 2, ⟨2, rfl⟩, rfl⟩

/-- An image attaining the upper bound makes the presentation homomorphism faithful. -/
lemma injective_of_card (s : ℕ) (hs : 0 < s) (φ : G s →* H)
    (hcard : Nat.card (Subgroup.closure ({φ (r s 0), φ (r s 1), φ (r s 2)} : Set H)) =
      8 * s ^ 2) : Function.Injective φ := by
  obtain ⟨ff, cc⟩ := finite_card s hs
  letI := ff
  have hc : Nat.card (G s) ≤ Nat.card φ.range := by rw [range_eq, hcard]; exact cc
  have hb := φ.rangeRestrict_surjective.bijective_of_nat_card_le hc
  intro x y hxy
  exact hb.1 (Subtype.ext hxy)
end Bridge
end P16c.Toroid
