import CocircuitFaces

namespace ADKZPricing
open Matrix Finset
noncomputable section

def rowValue (A : Matrix (Fin 80) (Fin 41) ℚ) (v : Fin 41 → ℝ) (i : Fin 80) : ℝ :=
  ∑ j, (A i j : ℝ) * v j

def signsOf (A : Matrix (Fin 80) (Fin 41) ℚ) (v : Fin 41 → ℝ) : SignVector :=
  fun i => realSign (rowValue A v i)

theorem signsOf_covector (A : Matrix (Fin 80) (Fin 41) ℚ) (v : Fin 41 → ℝ) :
    Covector A (signsOf A v) := ⟨v, fun _ => rfl⟩

theorem rowValue_add (A : Matrix (Fin 80) (Fin 41) ℚ) (v w : Fin 41 → ℝ) (i : Fin 80) :
    rowValue A (v + w) i = rowValue A v i + rowValue A w i := by
  simp [rowValue, mul_add, Finset.sum_add_distrib]

theorem rowValue_smul (A : Matrix (Fin 80) (Fin 41) ℚ) (v : Fin 41 → ℝ)
    (t : ℝ) (i : Fin 80) : rowValue A (t • v) i = t * rowValue A v i := by
  simp only [rowValue, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sign_face_signed_nonnegative (x y : ℝ)
    (h : realSign y = 0 ∨ realSign y = realSign x) : 0 ≤ (realSign x : ℝ) * y := by
  rcases h with h | h
  · rw [(realSign_zero_iff y).mp h, mul_zero]
  · rw [← h]
    exact realSign_signed_nonnegative y

/-- Subtract a positive multiple of a nonzero face ray until an additional
    original row vanishes. All old zeros and signs are retained. -/
theorem subtract_face_boundary (A : Matrix (Fin 80) (Fin 41) ℚ)
    (v w : Fin 41 → ℝ) (hf : FaceLE (signsOf A w) (signsOf A v))
    (hn : signsOf A w ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ FaceLE (signsOf A (v + t • (-w))) (signsOf A v) ∧
      (signSupport (signsOf A (v + t • (-w)))).card < (signSupport (signsOf A v)).card := by
  classical
  let q := fun i => (realSign (rowValue A v i) : ℝ) * rowValue A v i
  let d := fun i => -(realSign (rowValue A v i) : ℝ) * rowValue A w i
  have hz : ∀ i, q i = 0 → d i = 0 := by
    intro i hi
    have hv : rowValue A v i = 0 := (realSign_signed_zero_iff _).mp hi
    have hwi : signsOf A w i = 0 := (hf i).elim id (fun h => by simpa [signsOf, hv, realSign] using h)
    have hw : rowValue A w i = 0 := (realSign_zero_iff _).mp hwi
    simp [d, hw]
  have hiw : ∃ i, signsOf A w i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hn (funext h)
  obtain ⟨j, hj⟩ := hiw
  have hej : realSign (rowValue A w j) = realSign (rowValue A v j) := (hf j).resolve_left hj
  have hp : 0 < (realSign (rowValue A v j) : ℝ) * rowValue A w j := by
    rw [← hej]
    apply lt_of_le_of_ne (realSign_signed_nonnegative _)
    intro he
    exact hj ((realSign_zero_iff _).mpr ((realSign_signed_zero_iff _).mp he.symm))
  have hd : d j < 0 := by dsimp only [d]; nlinarith
  obtain ⟨t, ht, hfeas, i, hqi, hi⟩ := finite_cone_boundary q d
    (fun k => realSign_signed_nonnegative _) hz ⟨j, hd⟩
  have he (k : Fin 80) : rowValue A (v + t • (-w)) k = rowValue A v k - t * rowValue A w k := by
    rw [rowValue_add, rowValue_smul, show -w = (-1 : ℝ) • w by simp, rowValue_smul]
    ring
  have hslack (k : Fin 80) : (realSign (rowValue A v k) : ℝ) *
      rowValue A (v + t • (-w)) k = q k + t * d k := by
    rw [he]
    dsimp only [q, d]
    ring
  have hface : FaceLE (signsOf A (v + t • (-w))) (signsOf A v) := by
    intro k
    apply sign_face_of_signed_feasible
    · intro hk
      have hwk : realSign (rowValue A w k) = 0 :=
        (hf k).elim id (fun h => by simpa [signsOf, hk, realSign] using h)
      rw [he, hk, (realSign_zero_iff _).mp hwk]
      ring
    · rw [hslack]
      exact hfeas k
  refine ⟨t, ht, hface, ?_⟩
  apply card_lt_card
  apply (ssubset_iff_subset_ne).mpr
  refine ⟨face_support_subset hface, ?_⟩
  intro hset
  have hvi : realSign (rowValue A v i) ≠ 0 := by
    intro hzero
    have hq0 : q i = 0 := by simp [q, hzero]
    linarith
  have hnew : rowValue A (v + t • (-w)) i = 0 := by
    have hzprod := hslack i
    rw [hi] at hzprod
    exact (mul_eq_zero.mp hzprod).resolve_left (by exact_mod_cast hvi)
  have hm : i ∈ signSupport (signsOf A v) := mem_filter.mpr ⟨mem_univ _, hvi⟩
  rw [← hset] at hm
  exact (mem_filter.mp hm).2 ((realSign_zero_iff _).mpr hnew)

/-- Every representative in a covector face lies in the linear span of
    that face's actual cocircuit rays. Strong induction is on support
    size; no vertices or bases are enumerated. -/
theorem face_representative_in_submodule (A : Matrix (Fin 80) (Fin 41) ℚ)
    (hu : Uniform A) (T : SignVector) (P : Submodule ℝ (Fin 41 → ℝ))
    (hP : ∀ w, Cocircuit A (signsOf A w) → FaceLE (signsOf A w) T → w ∈ P)
    (v : Fin 41 → ℝ) (hv : FaceLE (signsOf A v) T) : v ∈ P := by
  have induction_claim : ∀ k : ℕ, ∀ z : Fin 41 → ℝ,
      (signSupport (signsOf A z)).card = k → FaceLE (signsOf A z) T → z ∈ P := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro z hk hz
      by_cases hn : signsOf A z = 0
      · have hz0 : z = 0 := by
          apply uniform_real_injective A hu
          funext i
          have hi := congrArg (fun X : SignVector => X i) hn
          have hr := (realSign_zero_iff (rowValue A z i)).mp hi
          simpa [rowValue] using hr
        rw [hz0]
        exact P.zero_mem
      · obtain ⟨Y, hY, hYz⟩ := covector_has_cocircuit_face A (signsOf A z) (signsOf_covector A z) hn
        obtain ⟨w, hw⟩ := hY.1
        have he : signsOf A w = Y := funext (fun i => (hw i).symm)
        have hwP : w ∈ P := hP w (by simpa only [he] using hY)
          (by simpa only [he] using face_trans hYz hz)
        obtain ⟨t, _, hface, hlt⟩ := subtract_face_boundary A z w
          (by simpa only [he] using hYz) (by simpa only [he] using hY.2.1)
        have hzP := ih _ (by simpa only [hk] using hlt) (z + t • (-w)) rfl (face_trans hface hz)
        have heq : z = (z + t • (-w)) + t • w := by simp
        rw [heq]
        exact P.add_mem hzP (P.smul_mem t hwP)
  exact induction_claim _ v rfl hv

/-- Every direction fixing the old zero rows has a positive step staying
    in the original covector face; no boundedness premise is needed. -/
theorem positive_face_step (A : Matrix (Fin 80) (Fin 41) ℚ)
    (v w : Fin 41 → ℝ) (hw : ∀ i, rowValue A v i = 0 → rowValue A w i = 0) :
    ∃ t : ℝ, 0 < t ∧ FaceLE (signsOf A (v + t • w)) (signsOf A v) := by
  classical
  let q := fun i => (realSign (rowValue A v i) : ℝ) * rowValue A v i
  let d := fun i => (realSign (rowValue A v i) : ℝ) * rowValue A w i
  have hz : ∀ i, q i = 0 → d i = 0 := by
    intro i hi
    have hvi := (realSign_signed_zero_iff _).mp hi
    simp [d, hw i hvi]
  have hex : ∃ t : ℝ, 0 < t ∧ ∀ i, 0 ≤ q i + t * d i := by
    by_cases hn : ∃ i, d i < 0
    · obtain ⟨t, ht, hf, _⟩ := finite_cone_boundary q d
        (fun i => realSign_signed_nonnegative _) hz hn
      exact ⟨t, ht, hf⟩
    · push_neg at hn
      refine ⟨1, by norm_num, ?_⟩
      intro i
      simpa using add_nonneg (realSign_signed_nonnegative (rowValue A v i)) (hn i)
  obtain ⟨t, ht, hf⟩ := hex
  refine ⟨t, ht, ?_⟩
  intro i
  apply sign_face_of_signed_feasible
  · intro hi
    rw [rowValue_add, rowValue_smul, hi, hw i hi]
    ring
  · rw [rowValue_add, rowValue_smul]
    have he : (realSign (rowValue A v i) : ℝ) *
        (rowValue A v i + t * rowValue A w i) = q i + t * d i := by
      dsimp only [q, d]
      ring
    rw [he]
    exact hf i

/-- The linear span of a covector face is its entire zero-row kernel.
    This direction follows by stepping from its interior representative.
    The supplied submodule need only contain actual cocircuit rays. -/
theorem face_kernel_in_submodule (A : Matrix (Fin 80) (Fin 41) ℚ)
    (hu : Uniform A) (u : Fin 41 → ℝ) (P : Submodule ℝ (Fin 41 → ℝ))
    (hP : ∀ z, Cocircuit A (signsOf A z) → FaceLE (signsOf A z) (signsOf A u) → z ∈ P)
    (w : Fin 41 → ℝ) (hw : ∀ i, rowValue A u i = 0 → rowValue A w i = 0) : w ∈ P := by
  have huP := face_representative_in_submodule A hu (signsOf A u) P hP u (face_refl _)
  obtain ⟨t, ht, hf⟩ := positive_face_step A u w hw
  have htP := face_representative_in_submodule A hu (signsOf A u) P hP (u + t • w) hf
  have htw : t • w ∈ P := by simpa using P.sub_mem htP huP
  have hwP := P.smul_mem t⁻¹ htw
  simpa [smul_smul, ht.ne'] using hwP

#print axioms positive_face_step
#print axioms face_kernel_in_submodule
#print axioms subtract_face_boundary
#print axioms face_representative_in_submodule
end
end ADKZPricing
