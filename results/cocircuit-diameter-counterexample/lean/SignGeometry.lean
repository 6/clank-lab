import Endpoint
import Mathlib.Tactic
import Mathlib.Data.Finset.Max

namespace ADKZPricing
open Finset Matrix
noncomputable section

/-- Finite exact boundary step inside a signed cone. The direction fixes
    existing zero slacks. A negative directional slack forces an additional
    zero at a positive parameter, while every original inequality remains. -/
theorem finite_cone_boundary {n : ℕ} (q d : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hz : ∀ i, q i = 0 → d i = 0)
    (hn : ∃ i, d i < 0) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, 0 ≤ q i + t * d i) ∧
      (∃ i, 0 < q i ∧ q i + t * d i = 0) := by
  classical
  let N := univ.filter (fun i => d i < 0)
  have hN : N.Nonempty := by
    obtain ⟨i, hi⟩ := hn
    exact ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  obtain ⟨j, hj, hmin⟩ := exists_min_image N (fun i => q i / (-d i)) hN
  have hdj : d j < 0 := (mem_filter.mp hj).2
  have hqj : 0 < q j := lt_of_le_of_ne (hq j) (by
    intro he
    have heq := hz j he.symm
    linarith)
  let t := q j / (-d j)
  have ht : 0 < t := div_pos hqj (neg_pos.mpr hdj)
  refine ⟨t, ht, ?_, j, hqj, ?_⟩
  · intro i
    by_cases hi : d i < 0
    · have hm : t ≤ q i / (-d i) := hmin i (mem_filter.mpr ⟨mem_univ _, hi⟩)
      have hb := (le_div_iff₀ (neg_pos.mpr hi)).mp hm
      nlinarith
    · have hm := mul_nonneg ht.le (le_of_not_gt hi)
      linarith [hq i]
  · dsimp [t]
    field_simp [hdj.ne]

theorem realSign_zero_iff (x : ℝ) : realSign x = 0 ↔ x = 0 := by
  unfold realSign
  split_ifs <;> simp_all
  linarith

theorem realSign_signed_nonnegative (x : ℝ) : 0 ≤ (realSign x : ℝ) * x := by
  unfold realSign
  split_ifs <;> simp_all
  linarith

theorem realSign_signed_zero_iff (x : ℝ) : (realSign x : ℝ) * x = 0 ↔ x = 0 := by
  unfold realSign
  split_ifs <;> simp_all

/-- The signed-inequality test is exactly the face relation to an actual
    covector when all its zero coordinates are retained. -/
theorem sign_face_of_signed_feasible (x y : ℝ)
    (hz : x = 0 → y = 0) (hy : 0 ≤ (realSign x : ℝ) * y) :
    realSign y = 0 ∨ realSign y = realSign x := by
  by_cases hx0 : x = 0
  · have hy0 := hz hx0
    simp [realSign, hy0]
  by_cases hx : x < 0
  · have hy' : y ≤ 0 := by simpa [realSign, hx] using hy
    by_cases hy0 : y = 0
    · simp [realSign, hy0]
    · have hyl : y < 0 := lt_of_le_of_ne hy' hy0
      simp [realSign, hx, hyl]
  · have hy' : 0 ≤ y := by simpa [realSign, hx, hx0] using hy
    by_cases hy0 : y = 0
    · simp [realSign, hy0]
    · have hyn : ¬ y < 0 := not_lt.mpr hy'
      simp [realSign, hx, hx0, hy0, hyn]

/-- Every nonzero scalar multiple with positive scale has the same signs. -/
theorem realSign_pos_scale (x t : ℝ) (ht : 0 < t) : realSign (t * x) = realSign x := by
  unfold realSign
  have hneg : t * x < 0 ↔ x < 0 := by
    constructor
    · intro h; nlinarith
    · exact mul_neg_of_pos_of_neg ht
  have hzero : t * x = 0 ↔ x = 0 := by simp [ht.ne']
  simp only [hneg, hzero]

/-- A boundary direction inside an actual endpoint covector contradicts
    support minimality. This uses the frozen Covector/Cocircuit/FaceLE
    definitions, not a replacement combinatorial graph. -/
theorem cocircuit_excludes_boundary_direction
    (A : Matrix (Fin 80) (Fin 41) ℚ) (X : SignVector)
    (v w : Fin 41 → ℝ) (hc : Cocircuit A X)
    (hx : ∀ i, X i = realSign (∑ j, (A i j : ℝ) * v j))
    (hinj : Function.Injective (fun z : Fin 41 → ℝ =>
      fun i : Fin 80 => ∑ j, (A i j : ℝ) * z j))
    (hw : ∀ i, (∑ j, (A i j : ℝ) * v j) = 0 →
      (∑ j, (A i j : ℝ) * w j) = 0)
    (hind : ∀ t : ℝ, 0 < t → v + t • w ≠ 0)
    (hnegative : ∃ i, (realSign (∑ j, (A i j : ℝ) * v j) : ℝ) *
      (∑ j, (A i j : ℝ) * w j) < 0) : False := by
  let a : Fin 80 → ℝ := fun i => ∑ j, (A i j : ℝ) * v j
  let b : Fin 80 → ℝ := fun i => ∑ j, (A i j : ℝ) * w j
  let q : Fin 80 → ℝ := fun i => (realSign (a i) : ℝ) * a i
  let δ : Fin 80 → ℝ := fun i => (realSign (a i) : ℝ) * b i
  have hz : ∀ i, q i = 0 → δ i = 0 := by
    intro i hi
    have ha : a i = 0 := (realSign_signed_zero_iff (a i)).mp hi
    have hb : b i = 0 := hw i ha
    simp [δ, hb]
  obtain ⟨t, ht, hfeas, i, hqi, hi⟩ := finite_cone_boundary q δ
    (fun i => realSign_signed_nonnegative (a i)) hz hnegative
  let z := v + t • w
  let c : Fin 80 → ℝ := fun i => ∑ j, (A i j : ℝ) * z j
  let Y : SignVector := fun i => realSign (c i)
  have hcform : ∀ i, c i = a i + t * b i := by
    intro i
    simp only [c, z, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib, a, b, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hcf : ∀ i, 0 ≤ (realSign (a i) : ℝ) * c i := by
    intro i
    rw [hcform i]
    have he : (realSign (a i) : ℝ) * (a i + t * b i) = q i + t * δ i := by
      dsimp only [q, δ]
      ring
    rw [he]
    exact hfeas i
  have hY : Covector A Y := ⟨z, fun _ => rfl⟩
  have hface : FaceLE Y X := by
    intro k
    rw [hx k]
    apply sign_face_of_signed_feasible (a k) (c k) _ (hcf k)
    intro hk
    have hb : b k = 0 := hw k hk
    rw [hcform k, hk, hb]
    ring
  have hYne : Y ≠ 0 := by
    intro hzero
    have hzrows : (fun k : Fin 80 => ∑ j, (A k j : ℝ) * z j) =
        (fun k : Fin 80 => ∑ j, (A k j : ℝ) * (0 : Fin 41 → ℝ) j) := by
      funext k
      have hk := congrArg (fun s : SignVector => s k) hzero
      change realSign (c k) = 0 at hk
      simpa [c] using (realSign_zero_iff (c k)).mp hk
    exact hind t ht (hinj hzrows)
  have heq : Y = X := hc.2.2 Y hY hYne hface
  have hai : a i ≠ 0 := by
    intro hzero
    have hqi0 : q i = 0 := (realSign_signed_zero_iff (a i)).mpr hzero
    linarith
  have hsi : (realSign (a i) : ℝ) ≠ 0 := by
    have hs := (realSign_zero_iff (a i)).not.mpr hai
    exact_mod_cast hs
  have hci : c i = 0 := by
    have he : (realSign (a i) : ℝ) * c i = q i + t * δ i := by
      rw [hcform i]
      dsimp only [q, δ]
      ring
    rw [hi] at he
    exact (mul_eq_zero.mp he).resolve_left hsi
  have hiX := congrArg (fun s : SignVector => s i) heq
  change realSign (c i) = X i at hiX
  rw [hci, hx i] at hiX
  have ha0 : realSign (a i) = 0 := by simpa [realSign] using hiX.symm
  exact hai ((realSign_zero_iff (a i)).mp ha0)

theorem not_proportional_affine_nonzero {r : ℕ} (v w : Fin r → ℝ)
    (hv : v ≠ 0) (hw : ∀ c : ℝ, w ≠ c • v) (t : ℝ) : v + t • w ≠ 0 := by
  intro he
  by_cases ht : t = 0
  · simp only [ht, zero_smul, add_zero] at he
    exact hv he
  apply hw (-1 / t)
  ext j
  have hj := congrArg (fun z : Fin r → ℝ => z j) he
  change v j + t * w j = 0 at hj
  change w j = (-1 / t) * v j
  field_simp [ht]
  nlinarith

/-- Every vector annihilating a cocircuit's zero rows lies on its ray
    line. This derives the one-dimensional kernel from the frozen
    support-minimal covector definition; it is not assumed from labels. -/
theorem cocircuit_kernel_line
    (A : Matrix (Fin 80) (Fin 41) ℚ) (X : SignVector)
    (v w : Fin 41 → ℝ) (hc : Cocircuit A X)
    (hx : ∀ i, X i = realSign (∑ j, (A i j : ℝ) * v j))
    (hinj : Function.Injective (fun z : Fin 41 → ℝ =>
      fun i : Fin 80 => ∑ j, (A i j : ℝ) * z j))
    (hw : ∀ i, (∑ j, (A i j : ℝ) * v j) = 0 →
      (∑ j, (A i j : ℝ) * w j) = 0) :
    ∃ c : ℝ, w = c • v := by
  by_contra hn
  push_neg at hn
  have hv : v ≠ 0 := by
    intro he
    apply hc.2.1
    ext i
    simpa [he, realSign] using hx i
  have hnw : w ≠ 0 := by simpa using hn 0
  have hiw : ∃ i, (∑ j, (A i j : ℝ) * w j) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hnw
    apply hinj
    funext i
    simpa using h i
  obtain ⟨i, hi⟩ := hiw
  have hiv : (∑ j, (A i j : ℝ) * v j) ≠ 0 := fun h => hi (hw i h)
  have hs : (realSign (∑ j, (A i j : ℝ) * v j) : ℝ) ≠ 0 := by
    exact_mod_cast (realSign_zero_iff _).not.mpr hiv
  have hprod := mul_ne_zero hs hi
  rcases lt_or_gt_of_ne hprod with hneg | hpos
  · exact cocircuit_excludes_boundary_direction A X v w hc hx hinj hw
      (fun t _ => not_proportional_affine_nonzero v w hv hn t) ⟨i, hneg⟩
  · apply cocircuit_excludes_boundary_direction A X v (-w) hc hx hinj
    · intro j hj
      simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, hw j hj, neg_zero]
    · intro t _
      have h := not_proportional_affine_nonzero v w hv hn (-t)
      simpa only [neg_smul, smul_neg] using h
    · refine ⟨i, ?_⟩
      simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
      linarith

#print axioms not_proportional_affine_nonzero
#print axioms cocircuit_kernel_line
#print axioms cocircuit_excludes_boundary_direction
#print axioms finite_cone_boundary
#print axioms realSign_zero_iff
#print axioms sign_face_of_signed_feasible
#print axioms realSign_pos_scale
end
end ADKZPricing
