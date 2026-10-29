import CocircuitSpan

namespace ADKZPricing
open Matrix Finset Module
noncomputable section

theorem face_left_compose (X Y : SignVector) : FaceLE X (compose X Y) := by
  intro i
  by_cases hi : X i = 0
  · exact Or.inl hi
  · exact Or.inr (by simp [compose, hi])

theorem face_right_compose {X Y : SignVector} (h : compose X Y = compose Y X) :
    FaceLE Y (compose X Y) := by rw [h]; exact face_left_compose Y X

theorem face_nonzero_upper {X Y : SignVector} (h : FaceLE X Y) (hn : X ≠ 0) : Y ≠ 0 := by
  intro hz
  apply hn
  ext i
  rcases h i with hi | hi
  · exact hi
  · simpa only [hz, Pi.zero_apply] using hi

theorem same_cocircuit_rep_mem (A : Matrix (Fin 80) (Fin 41) ℚ)
    (hu : Uniform A) (X : SignVector) (hc : Cocircuit A X)
    (v z : Fin 41 → ℝ) (hv : signsOf A v = X) (hz : signsOf A z = X)
    (P : Submodule ℝ (Fin 41 → ℝ)) (hp : v ∈ P) : z ∈ P := by
  obtain ⟨c, hc⟩ := cocircuit_kernel_line A X v z hc
    (fun i => congrArg (fun Y : SignVector => Y i) hv.symm)
    (uniform_real_injective A hu) (by
      intro i hi
      have he : realSign (rowValue A z i) = realSign (rowValue A v i) :=
        congrArg (fun Y : SignVector => Y i) (hz.trans hv.symm)
      have hzero : realSign (rowValue A z i) = 0 := by simpa [rowValue, hi, realSign] using he
      exact (realSign_zero_iff _).mp hzero)
  rw [hc]
  exact P.smul_mem c hp

/-- Composition adjacency in the frozen definition forces a face kernel
    of dimension at most two. The span argument uses actual cocircuits. -/
theorem adjacent_composition_zero_lower (A : Matrix (Fin 80) (Fin 41) ℚ)
    (hu : Uniform A) (X Y : SignVector) (hadj : Adjacent A X Y) :
    39 ≤ (signZeros (compose X Y)).card := by
  classical
  rcases hadj with ⟨hcX, hcY, _, _, hcT, honly⟩
  obtain ⟨x, hx⟩ := hcX.1
  obtain ⟨y, hy⟩ := hcY.1
  obtain ⟨u, huT⟩ := hcT
  have hx' : signsOf A x = X := funext (fun i => (hx i).symm)
  have hy' : signsOf A y = Y := funext (fun i => (hy i).symm)
  have hu' : signsOf A u = compose X Y := funext (fun i => (huT i).symm)
  let P := Submodule.span ℝ ({x, y} : Set (Fin 41 → ℝ))
  have hxP : x ∈ P := Submodule.subset_span (by simp)
  have hyP : y ∈ P := Submodule.subset_span (by simp)
  have hP : ∀ z, Cocircuit A (signsOf A z) → FaceLE (signsOf A z) (signsOf A u) → z ∈ P := by
    intro z hzc hzf
    have hzt : FaceLE (signsOf A z) (compose X Y) := by simpa only [hu'] using hzf
    rcases honly (signsOf A z) hzc hzt with hz | hz
    · exact same_cocircuit_rep_mem A hu X hcX x z hx' hz P hxP
    · exact same_cocircuit_rep_mem A hu Y hcY y z hy' hz P hyP
  let J := signZeros (compose X Y)
  let K : Matrix J (Fin 41) ℝ := fun i j => A i.val j
  let L := K.mulVecLin
  have hker : LinearMap.ker L ≤ P := by
    intro w hw
    apply face_kernel_in_submodule A hu u P hP w
    intro i hi
    have hTi : compose X Y i = 0 := by rw [huT i]; exact (realSign_zero_iff _).mpr hi
    have hrow := congrArg (fun z : J → ℝ => z ⟨i, mem_filter.mpr ⟨mem_univ _, hTi⟩⟩)
      (LinearMap.mem_ker.mp hw)
    exact hrow
  have hpdim : Module.finrank ℝ P ≤ 2 := by
    have h := finrank_span_le_card (R := ℝ) ({x, y} : Set (Fin 41 → ℝ))
    simp only [Set.toFinset_insert, Set.toFinset_singleton] at h
    exact h.trans (by by_cases he : x = y <;> simp [he])
  have hkdim := (Submodule.finrank_mono hker).trans hpdim
  have hdim := L.finrank_range_add_finrank_ker
  have hrange := Submodule.finrank_le (LinearMap.range L)
  simp only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] at hdim hrange
  have hcard : Fintype.card J = J.card := Fintype.card_coe _
  change 39 ≤ J.card
  omega

/-- The full composition face of adjacent cocircuits has exactly 39 zeros.
    This is proved from, rather than substituted for, frozen adjacency. -/
theorem adjacent_composition_zero_count (A : Matrix (Fin 80) (Fin 41) ℚ)
    (hu : Uniform A) (X Y : SignVector) (hadj : Adjacent A X Y) :
    (signZeros (compose X Y)).card = 39 := by
  have hlo := adjacent_composition_zero_lower A hu X Y hadj
  rcases hadj with ⟨hcX, hcY, hne, hcomm, hcT, _⟩
  have hXT := face_left_compose X Y
  have hYT := face_right_compose hcomm
  have hnonzero := face_nonzero_upper hXT hcX.2.1
  have hXcard : (signZeros X).card = 40 := uniform_cocircuit_zero_count A hu X hcX
  have hle : (signZeros (compose X Y)).card ≤ 40 := by
    simpa only [hXcard] using card_le_card (face_zero_subset hXT)
  by_contra hn
  have heq : (signZeros (compose X Y)).card = 40 := by omega
  have hT := (uniform_covector_cocircuit_iff A hu _ hcT hnonzero).mpr heq
  have hXeq := hT.2.2 X hcX.1 hcX.2.1 hXT
  have hYeq := hT.2.2 Y hcY.1 hcY.2.1 hYT
  exact hne (hXeq.trans hYeq.symm)

theorem compose_zero_iff (X Y : SignVector) (i : Fin 80) :
    compose X Y i = 0 ↔ X i = 0 ∧ Y i = 0 := by
  by_cases hi : X i = 0 <;> simp [compose, hi]

#print axioms adjacent_composition_zero_lower
#print axioms adjacent_composition_zero_count
end
end ADKZPricing
