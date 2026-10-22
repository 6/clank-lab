import P16c.Toroid
import P16c.StringRelations
import P16c.StringC
import P16c.StringCTheory

namespace P16c
open scoped Pointwise

/-- A dihedral normal form, with bounded exponents; no faithfulness is assumed. -/
lemma dihedral_pair_form {G : Type*} [Group G] (x y : G)
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hxy : (x * y) ^ 4 = 1)
    {z : G} (hz : z ∈ Subgroup.closure ({x, y} : Set G)) :
    ∃ i : Fin 4, ∃ j : Fin 2, (x * y) ^ i.val * x ^ j.val = z := by
  classical
  let R := Subgroup.zpowers (x * y)
  let B := Subgroup.zpowers x
  have hx' : x * x = 1 := by simpa [pow_two] using hx
  have hy' : y * y = 1 := by simpa [pow_two] using hy
  have hn : B ≤ Subgroup.normalizer R := by
    apply Subgroup.zpowers_le.mpr
    dsimp [R]
    rw [Subgroup.zpowers_eq_closure]
    apply Toroid.involution_normalizes_closure x hx'
    intro w hw
    have hw' : w = x * y := Set.mem_singleton_iff.mp hw
    subst w
    have he : x * (x * y) * x = (x * y)⁻¹ := by
      simp [mul_inv_rev, inv_eq_of_mul_eq_one_right hx',
        inv_eq_of_mul_eq_one_right hy', ← mul_assoc x x, hx']
    rw [he]
    exact (Subgroup.closure {x * y}).inv_mem (Subgroup.subset_closure (by simp))
  have he : R ⊔ B = Subgroup.closure ({x, y} : Set G) := by
    apply le_antisymm
    · refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact (Subgroup.closure {x, y}).mul_mem
          (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
      · exact Subgroup.subset_closure (by simp)
    · apply (Subgroup.closure_le _).mpr
      intro w hw
      rcases Set.mem_insert_iff.mp hw with rfl | hw
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      · have hw' : w = y := Set.mem_singleton_iff.mp hw
        subst w
        have hh : x * (x * y) = y := by simp [← mul_assoc, hx']
        rw [← hh]
        exact (R ⊔ B).mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers (x * y)))
  rw [← he] at hz
  have hz' : z ∈ (R : Set G) * (B : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left R B hn]
    exact hz
  obtain ⟨w, hw, v, hv, rfl⟩ := hz'
  have hfxy : IsOfFinOrder (x * y) := isOfFinOrder_iff_pow_eq_one.mpr ⟨4, by omega, hxy⟩
  have hfx : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by omega, hx⟩
  obtain ⟨i, rfl⟩ := hfxy.mem_powers_iff_mem_zpowers.mpr hw
  obtain ⟨j, rfl⟩ := hfx.mem_powers_iff_mem_zpowers.mpr hv
  refine ⟨⟨i % 4, Nat.mod_lt _ (by omega)⟩, ⟨j % 2, Nat.mod_lt _ (by omega)⟩, ?_⟩
  exact congrArg₂ (· * ·)
    (pow_eq_pow_of_modEq (Nat.mod_modEq _ _) hxy)
    (pow_eq_pow_of_modEq (Nat.mod_modEq _ _) hx)

lemma involution_singleton_mem {G : Type*} [Group G] (x : G) (hx : x ^ 2 = 1)
    {z : G} : z ∈ Subgroup.closure ({x} : Set G) ↔ z = 1 ∨ z = x := by
  constructor
  · intro hz
    have hx' : x * x = 1 := by simpa [pow_two] using hx
    induction hz using Subgroup.closure_induction with
    | mem z hz => exact Or.inr (Set.mem_singleton_iff.mp hz)
    | one => exact Or.inl rfl
    | mul z w hz hw ihz ihw =>
      rcases ihz with rfl | rfl <;> rcases ihw with rfl | rfl <;> simp [hx']
    | inv z hz ih =>
      rcases ih with rfl | rfl
      · simp
      · exact Or.inr (inv_eq_of_mul_eq_one_right hx')
  · rintro (rfl | rfl)
    · exact (Subgroup.closure {x}).one_mem
    · exact Subgroup.subset_closure (by simp)

lemma involution_singletons_inf {G : Type*} [Group G] (x y : G)
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hne : x ≠ y) :
    Subgroup.closure ({x} : Set G) ⊓ Subgroup.closure {y} = ⊥ := by
  ext z
  simp only [Subgroup.mem_inf, Subgroup.mem_bot]
  constructor
  · rintro ⟨hzx, hzy⟩
    rcases (involution_singleton_mem x hx).mp hzx with rfl | rfl
    · rfl
    · rcases (involution_singleton_mem y hy).mp hzy with h | h
      · exact h
      · exact (hne h).elim
  · rintro rfl
    exact ⟨(Subgroup.closure {x}).one_mem, (Subgroup.closure {y}).one_mem⟩

lemma pair_stringC {G : Type*} [Group G] (x y : G)
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hne : x ≠ y) :
    IsStringCGroup ![x, y] := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro i; fin_cases i <;> assumption
  · intro i j h
    have hi := i.isLt
    have hj := j.isLt
    omega
  · intro I J
    have hij := involution_singletons_inf x y hx hy hne
    have hji := involution_singletons_inf y x hy hx hne.symm
    have cases2 (S : Finset (Fin 2)) : S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {0, 1} := by
      fin_cases S <;> decide
    have hpair : Subgroup.closure ({x, y} : Set G) =
        Subgroup.closure {x} ⊔ Subgroup.closure {y} := by
      rw [← Subgroup.closure_union]
      congr 1
    rcases cases2 I with rfl | rfl | rfl | rfl <;>
      rcases cases2 J with rfl | rfl | rfl | rfl <;>
      simp [Set.image_insert_eq, Set.image_singleton, Set.image_empty,
        hij, hji, hpair]

lemma pair_stringC_of_order_four {G : Type*} [Group G] (x y : G)
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hxy : orderOf (x * y) = 4) :
    IsStringCGroup ![x, y] := by
  apply pair_stringC x y hx hy
  intro h
  rw [h, ← pow_two, hy] at hxy
  norm_num at hxy

section Matrices
variable {K : Type*} [Field K] [CharP K 2]
open scoped CharTwo
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

private def selectedEntries (M : Mat K) : Fin 6 → K :=
  ![M 0 0, M 0 1, M 0 2, M 1 2, M 2 0, M 3 1]

private def pairEntries01 (a b : K) : Fin 4 → Fin 2 → Fin 6 → K :=
  ![![![1, 0, 0, 0, 0, 0], ![1, 1, 0, 0, a, a]],
    ![![1, 1, 1, 1, a, a], ![1 + a, 0, 1, 1, 0, 0]],
    ![![1 + a, 0, 1, 0, 0, 0], ![1, 1, 1, 0, a, a]],
    ![![1, 1, 0, 1, a, a], ![1, 0, 0, 1, 0, 0]]]

private lemma wordEntries01 (a b : K) (ha : a ≠ 0) (i : Fin 4) (j : Fin 2) :
    selectedEntries (↑((generators a b ha 0 * generators a b ha 1) ^ i.val *
      generators a b ha 0 ^ j.val) : Mat K) = pairEntries01 a b i j := by
  funext c
  fin_cases i <;> fin_cases j <;> fin_cases c <;>
    simp [selectedEntries, pairEntries01, Units.val_mul, Units.val_pow_eq_pow_val,
      generators_zero, generators_one, generators_two, generators_three,
      pow_succ, Matrix.mul_apply, Fin.sum_univ_succ, r, r₁, r₃] <;>
    (try field_simp [ha]) <;> ring_nf <;> simp

private def pairEntries12 (a b : K) : Fin 4 → Fin 2 → Fin 6 → K :=
  ![![![1, 0, 0, 0, 0, 0], ![1, 0, 0, 1, 0, 0]],
    ![![1, 1, 0, 1, b, b], ![1, 1, 1, 0, b, b]],
    ![![1 + b, 0, 1, 0, 0, 0], ![1 + b, 0, 1, 1, 0, 0]],
    ![![1, 1, 1, 1, b, b], ![1, 1, 0, 0, b, b]]]

private lemma wordEntries12 (a b : K) (ha : a ≠ 0) (i : Fin 4) (j : Fin 2) :
    selectedEntries (↑((generators a b ha 1 * generators a b ha 2) ^ i.val *
      generators a b ha 1 ^ j.val) : Mat K) = pairEntries12 a b i j := by
  funext c
  fin_cases i <;> fin_cases j <;> fin_cases c <;>
    simp [selectedEntries, pairEntries12, Units.val_mul, Units.val_pow_eq_pow_val,
      generators_zero, generators_one, generators_two, generators_three,
      pow_succ, Matrix.mul_apply, Fin.sum_univ_succ, r, r₁, r₃] <;>
    (try field_simp [ha]) <;> ring_nf <;> simp

private def pairEntries23 (a b : K) : Fin 4 → Fin 2 → Fin 6 → K :=
  ![![![1, 0, 0, 0, 0, 0], ![1, 1, 0, 0, b, b]],
    ![![0, 1, 0, 0, a, b], ![0, a⁻¹ * b + 1, 0, 0, b + a, b + a]],
    ![![1, a⁻¹ * b + 1, 0, 0, b + a, b + a], ![1, a⁻¹ * b, 0, 0, a, a]],
    ![![0, a⁻¹ * b, 0, 0, b, a], ![0, 0, 0, 0, 0, 0]]]

private lemma wordEntries23 (a b : K) (ha : a ≠ 0) (i : Fin 4) (j : Fin 2) :
    selectedEntries (↑((generators a b ha 2 * generators a b ha 3) ^ i.val *
      generators a b ha 2 ^ j.val) : Mat K) = pairEntries23 a b i j := by
  funext c
  fin_cases i <;> fin_cases j <;> fin_cases c <;>
    simp [selectedEntries, pairEntries23, Units.val_mul, Units.val_pow_eq_pow_val,
      generators_zero, generators_one, generators_two, generators_three,
      pow_succ, Matrix.mul_apply, Fin.sum_univ_succ, r, r₁, r₃] <;>
    (try field_simp [ha]) <;> ring_nf <;> simp

private lemma pair01_pair12_word (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a + b ≠ 0) (i k : Fin 4) (j l : Fin 2)
    (h : (generators a b ha 0 * generators a b ha 1) ^ i.val *
        generators a b ha 0 ^ j.val =
      (generators a b ha 1 * generators a b ha 2) ^ k.val *
        generators a b ha 1 ^ l.val) :
    (generators a b ha 0 * generators a b ha 1) ^ i.val *
        generators a b ha 0 ^ j.val = 1 ∨
    (generators a b ha 0 * generators a b ha 1) ^ i.val *
        generators a b ha 0 ^ j.val = generators a b ha 1 := by
  have hne : a ≠ b := by
    intro he
    apply hab
    simp [he]
  have hba : b + a ≠ 0 := by simpa [add_comm] using hab
  have hm := congrArg selectedEntries (congrArg Units.val h)
  rw [wordEntries01, wordEntries12] at hm
  have h00 := congrArg (fun v : Fin 6 → K => v 0) hm
  have h01 := congrArg (fun v : Fin 6 → K => v 1) hm
  have h02 := congrArg (fun v : Fin 6 → K => v 2) hm
  have h12 := congrArg (fun v : Fin 6 → K => v 3) hm
  have h20 := congrArg (fun v : Fin 6 → K => v 4) hm
  fin_cases k <;> fin_cases l
  · left; simpa only [pow_zero, pow_one, one_mul, mul_one] using h
  · right; simpa only [pow_zero, pow_one, one_mul, mul_one] using h
  all_goals
    exfalso
    clear h hm
    fin_cases i <;> fin_cases j
    all_goals
      norm_num [pairEntries01, pairEntries12, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] at h00 <;>
      norm_num [pairEntries01, pairEntries12, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] at h01 <;>
      norm_num [pairEntries01, pairEntries12, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] at h02 <;>
      norm_num [pairEntries01, pairEntries12, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] at h12 <;>
      norm_num [pairEntries01, pairEntries12, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] at h20 <;>
      first
      | exact hba h20.symm
      | solve | simp [ha, hb, hab, hba, hne, hne.symm] at h00
      | solve | simp [ha, hb, hab, hba, hne, hne.symm] at h01
      | solve | simp [ha, hb, hab, hba, hne, hne.symm] at h02
      | solve | simp [ha, hb, hab, hba, hne, hne.symm] at h12
      | solve | simp [ha, hb, hab, hba, hne, hne.symm] at h20

private lemma pair12_pair23_word (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a + b ≠ 0) (i k : Fin 4) (j l : Fin 2)
    (h : (generators a b ha 1 * generators a b ha 2) ^ i.val *
        generators a b ha 1 ^ j.val =
      (generators a b ha 2 * generators a b ha 3) ^ k.val *
        generators a b ha 2 ^ l.val) :
    (generators a b ha 1 * generators a b ha 2) ^ i.val *
        generators a b ha 1 ^ j.val = 1 ∨
    (generators a b ha 1 * generators a b ha 2) ^ i.val *
        generators a b ha 1 ^ j.val = generators a b ha 2 := by
  have hne : a ≠ b := by
    intro he
    apply hab
    simp [he]
  have hba : b + a ≠ 0 := by simpa [add_comm] using hab
  have hm := congrArg selectedEntries (congrArg Units.val h)
  rw [wordEntries12, wordEntries23] at hm
  have h00 := congrArg (fun v : Fin 6 → K => v 0) hm
  have h01 := congrArg (fun v : Fin 6 → K => v 1) hm
  have h02 := congrArg (fun v : Fin 6 → K => v 2) hm
  have h12 := congrArg (fun v : Fin 6 → K => v 3) hm
  have h20 := congrArg (fun v : Fin 6 → K => v 4) hm
  fin_cases k <;> fin_cases l
  · left; simpa only [pow_zero, pow_one, one_mul, mul_one] using h
  · right; simpa only [pow_zero, pow_one, one_mul, mul_one] using h
  all_goals
    exfalso
    clear h hm
    fin_cases i <;> fin_cases j
    all_goals
      norm_num [pairEntries12, pairEntries23, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] at h00 <;>
      norm_num [pairEntries12, pairEntries23, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] at h01 <;>
      norm_num [pairEntries12, pairEntries23, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] at h02 <;>
      norm_num [pairEntries12, pairEntries23, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] at h12 <;>
      norm_num [pairEntries12, pairEntries23, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] at h20 <;>
      first
      | exact hba h20.symm
      | solve | simp [ha, hb, hab, hba, hne, hne.symm] at h00
      | solve | simp [ha, hb, hab, hba, hne, hne.symm] at h01
      | solve | simp [ha, hb, hab, hba, hne, hne.symm] at h02
      | solve | simp [ha, hb, hab, hba, hne, hne.symm] at h12
      | solve | simp [ha, hb, hab, hba, hne, hne.symm] at h20

/-- The two adjacent rank-two subgroups of the facet meet in its middle reflection. -/
lemma matrix_facet_pair_intersection (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a + b ≠ 0) :
    Subgroup.closure ({generators a b ha 0, generators a b ha 1} : Set (Mat K)ˣ) ⊓
      Subgroup.closure {generators a b ha 1, generators a b ha 2} =
        Subgroup.closure {generators a b ha 1} := by
  let g := generators a b ha
  obtain ⟨hs, h01, h12, h23, h02, h03, h13⟩ := string_relations a b ha hb hab
  have hp01 : (g 0 * g 1) ^ 4 = 1 := by simpa only [g, h01] using pow_orderOf_eq_one (g 0 * g 1)
  have hp12 : (g 1 * g 2) ^ 4 = 1 := by simpa only [g, h12] using pow_orderOf_eq_one (g 1 * g 2)
  apply le_antisymm
  · rintro z ⟨hz01, hz12⟩
    obtain ⟨i, j, hi⟩ := dihedral_pair_form (g 0) (g 1) (hs 0) (hs 1) hp01 hz01
    obtain ⟨k, l, hk⟩ := dihedral_pair_form (g 1) (g 2) (hs 1) (hs 2) hp12 hz12
    have hh := pair01_pair12_word a b ha hb hab i k j l (hi.trans hk.symm)
    rcases hh with hh | hh
    · rw [← hi, hh]
      exact (Subgroup.closure {g 1}).one_mem
    · rw [← hi, hh]
      exact Subgroup.subset_closure (by simp)
  · apply (Subgroup.closure_le _).mpr
    intro z hz
    have hz' : z = g 1 := Set.mem_singleton_iff.mp hz
    subst z
    exact ⟨Subgroup.subset_closure (by simp [g]), Subgroup.subset_closure (by simp [g])⟩

/-- The two adjacent rank-two subgroups of the vertex figure meet in its middle reflection. -/
lemma matrix_vertex_pair_intersection (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a + b ≠ 0) :
    Subgroup.closure ({generators a b ha 1, generators a b ha 2} : Set (Mat K)ˣ) ⊓
      Subgroup.closure {generators a b ha 2, generators a b ha 3} =
        Subgroup.closure {generators a b ha 2} := by
  let g := generators a b ha
  obtain ⟨hs, h01, h12, h23, h02, h03, h13⟩ := string_relations a b ha hb hab
  have hp12 : (g 1 * g 2) ^ 4 = 1 := by simpa only [g, h12] using pow_orderOf_eq_one (g 1 * g 2)
  have hp23 : (g 2 * g 3) ^ 4 = 1 := by simpa only [g, h23] using pow_orderOf_eq_one (g 2 * g 3)
  apply le_antisymm
  · rintro z ⟨hz12, hz23⟩
    obtain ⟨i, j, hi⟩ := dihedral_pair_form (g 1) (g 2) (hs 1) (hs 2) hp12 hz12
    obtain ⟨k, l, hk⟩ := dihedral_pair_form (g 2) (g 3) (hs 2) (hs 3) hp23 hz23
    have hh := pair12_pair23_word a b ha hb hab i k j l (hi.trans hk.symm)
    rcases hh with hh | hh
    · rw [← hi, hh]
      exact (Subgroup.closure {g 2}).one_mem
    · rw [← hi, hh]
      exact Subgroup.subset_closure (by simp)
  · apply (Subgroup.closure_le _).mpr
    intro z hz
    have hz' : z = g 2 := Set.mem_singleton_iff.mp hz
    subst z
    exact ⟨Subgroup.subset_closure (by simp [g]), Subgroup.subset_closure (by simp [g])⟩

/-- Both matrix triples satisfy the complete rank-three intersection property. -/
lemma matrix_local_stringC (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a + b ≠ 0) :
    IsStringCGroup (fun i : Fin 3 => generators a b ha i.castSucc) ∧
      IsStringCGroup (fun i : Fin 3 => generators a b ha i.succ) := by
  let g := generators a b ha
  obtain ⟨hs, h01, h12, h23, h02, h03, h13⟩ := string_relations a b ha hb hab
  have hp01 := pair_stringC_of_order_four (g 0) (g 1) (hs 0) (hs 1) h01
  have hp12 := pair_stringC_of_order_four (g 1) (g 2) (hs 1) (hs 2) h12
  have hp23 := pair_stringC_of_order_four (g 2) (g 3) (hs 2) (hs 3) h23
  constructor
  · apply stringC_rank3
    · exact fun i => hs i.castSucc
    · intro i j hij
      fin_cases i <;> fin_cases j <;> norm_num at hij
      exact h02
    · have he : (fun i : Fin 2 => g i.castSucc.castSucc) = ![g 0, g 1] := by
        funext i; fin_cases i <;> rfl
      change IsStringCGroup (fun i : Fin 2 => g i.castSucc.castSucc)
      rw [he]
      exact hp01
    · have he : (fun i : Fin 2 => g i.succ.castSucc) = ![g 1, g 2] := by
        funext i; fin_cases i <;> rfl
      change IsStringCGroup (fun i : Fin 2 => g i.succ.castSucc)
      rw [he]
      exact hp12
    · simpa [parabolic, Set.image_insert_eq, Set.image_singleton] using
        matrix_facet_pair_intersection a b ha hb hab
  · apply stringC_rank3
    · exact fun i => hs i.succ
    · intro i j hij
      fin_cases i <;> fin_cases j <;> norm_num at hij
      exact h13
    · have he : (fun i : Fin 2 => g i.castSucc.succ) = ![g 1, g 2] := by
        funext i; fin_cases i <;> rfl
      change IsStringCGroup (fun i : Fin 2 => g i.castSucc.succ)
      rw [he]
      exact hp12
    · have he : (fun i : Fin 2 => g i.succ.succ) = ![g 2, g 3] := by
        funext i; fin_cases i <;> rfl
      change IsStringCGroup (fun i : Fin 2 => g i.succ.succ)
      rw [he]
      exact hp23
    · simpa [parabolic, Set.image_insert_eq, Set.image_singleton] using
        matrix_vertex_pair_intersection a b ha hb hab

end Matrices
end P16c
