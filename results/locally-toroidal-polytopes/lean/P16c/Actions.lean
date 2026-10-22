import P16c.GroupDefs
import P16c.Translations

namespace P16c
variable {K : Type*} [Field K] [CharP K 2]
open scoped CharTwo
set_option maxHeartbeats 1600000

lemma generators_involutive (a b : K) (ha : a ≠ 0) (i : Fin 4) :
    generators a b ha i * generators a b ha i = 1 := by
  apply Units.ext
  fin_cases i <;> simp [generators, ← pow_two, r_sq, r₁_sq, r₃_sq a ha]

lemma tGen_commute (a b : K) (ha : a ≠ 0) : Commute (tGen a b ha) (t₂Gen a b ha) := by
  apply Units.ext
  simpa using t_commute a b
lemma vGen_commute (a b : K) (ha : a ≠ 0) : Commute (vGen a b ha) (v₂Gen a b ha) := by
  apply Units.ext
  simpa using v_commute a b ha

lemma conjugate_t (a b : K) (ha : a ≠ 0) :
    generators a b ha 1 * tGen a b ha * generators a b ha 1 = t₂Gen a b ha := rfl
lemma conjugate_t₂ (a b : K) (ha : a ≠ 0) :
    generators a b ha 1 * t₂Gen a b ha * generators a b ha 1 = tGen a b ha := by
  apply Units.ext
  simpa using r₁_t₂ a b
lemma conjugate_t_fixed (a b : K) (ha : a ≠ 0) :
    generators a b ha 2 * tGen a b ha * generators a b ha 2 = tGen a b ha := by
  apply Units.ext
  simpa using r₂_t a b
lemma conjugate_t₂_inv (a b : K) (ha : a ≠ 0) :
    generators a b ha 2 * t₂Gen a b ha * generators a b ha 2 = (t₂Gen a b ha)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply Units.ext
  change (r b * T₂ a b * r b) * T₂ a b = 1
  rw [r₂_t₂]
  simp only [add_mul, smul_mul_assoc, one_mul, ← pow_two, t₂_square]
  simp [add_assoc, add_left_comm]

lemma conjugate_v_inv (a b : K) (ha : a ≠ 0) :
    generators a b ha 1 * vGen a b ha * generators a b ha 1 = (vGen a b ha)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  dsimp [vGen]
  simp only [mul_assoc]
  simp [← mul_assoc, generators_involutive]
lemma conjugate_v₂_fixed (a b : K) (ha : a ≠ 0) :
    generators a b ha 1 * v₂Gen a b ha * generators a b ha 1 = v₂Gen a b ha := by
  apply Units.ext
  simpa using r₁_v₂ a b
lemma conjugate_v (a b : K) (ha : a ≠ 0) :
    generators a b ha 2 * vGen a b ha * generators a b ha 2 = v₂Gen a b ha := rfl
lemma conjugate_v₂ (a b : K) (ha : a ≠ 0) :
    generators a b ha 2 * v₂Gen a b ha * generators a b ha 2 = vGen a b ha := by
  apply Units.ext
  simpa using r₂_v₂ a b

lemma closure_pair_commutative {G : Type*} [Group G] (x y : G) (h : Commute x y) :
    IsMulCommutative (Subgroup.closure ({x, y} : Set G)) := by
  apply Subgroup.isMulCommutative_closure
  intro a ha b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · exact h.eq
  · exact h.symm.eq
  · rfl

lemma af_commutative (a b : K) (ha : a ≠ 0) : IsMulCommutative (AF a b ha) :=
  closure_pair_commutative _ _ (tGen_commute a b ha)
lemma av_commutative (a b : K) (ha : a ≠ 0) : IsMulCommutative (AV a b ha) :=
  closure_pair_commutative _ _ (vGen_commute a b ha)
end P16c
